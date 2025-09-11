package main

import (
	"bytes"
	"crypto/sha1"
	"encoding/binary"
	"encoding/hex"
	"flag"
	"fmt"
	"log"
	"net"
	"os"
	"strings"
	"time"

	"golang.org/x/crypto/pbkdf2"
)

const (
	// UDP well-known
	CtrlPort = 5246

	// CAPWAP base msg types
	MT_DISCOVERY_REQ  = 1
	MT_DISCOVERY_RESP = 2
	MT_JOIN_REQ       = 3
	MT_JOIN_RESP      = 4
	MT_CFGSTAT_REQ    = 5
	MT_CFGSTAT_RESP   = 6
	MT_CFGUPDATE_REQ  = 7
	MT_CFGUPDATE_RESP = 8
	MT_ECHO_REQ       = 9
	MT_ECHO_RESP      = 10

	// 802.11 binding MEs
	ME_ADD_WLAN = 1024 // 0x0400
	ME_INFO_ELE = 1029 // 0x0405

	// 802.11 IEs
	IE_SSID = 0
	IE_RSN  = 48
)

// ==== Flags / ENV ====
var (
	listenAddr   = flag.String("listen", ":5246", "UDP listen address (e.g. :5246)")
	ssidFlag     = flag.String("ssid", envOr("SSID", "MyLabSSID"), "SSID to provision")
	passFlag     = flag.String("psk", envOr("PSK", "MyStrongPass123!"), "WPA2-PSK passphrase (8..63)")
	radioIDFlag  = flag.Uint("radio", 0, "Radio ID to configure")
	wlanIDFlag   = flag.Uint("wlan", 1, "WLAN ID to (Add/Update)")
	useLEFlag    = flag.Bool("le", false, "Use little-endian for MsgElemLength (try if AP ignores BE)")
	send7DelayMs = flag.Int("send7_delay_ms", 200, "Delay after sending type 6 before sending type 7")
	//logHexPayload = flag.Bool("loghex", true, "Log hex of outgoing packets")
)

// ==== Utils ====
func envOr(k, v string) string {
	if s := os.Getenv(k); s != "" {
		return s
	}
	return v
}

type ConnCtx struct {
	seq  uint8
	peer *net.UDPAddr
}

// === Message Element Builders ===

// ===== Update: Message Element Builders =====

// AC Name (Type=4)
func buildME_ACName(name string) []byte {
	b := []byte(name)
	me := make([]byte, 4+len(b))
	binary.BigEndian.PutUint16(me[0:2], 4) // Type=4
	binary.BigEndian.PutUint16(me[2:4], uint16(len(b)))
	copy(me[4:], b)
	return me
}

func buildME_ACDescriptorBetter() []byte {
	soft := []byte("LiteOn-AC-1.0")
	hard := []byte("LiteOn-HW")

	var v bytes.Buffer
	v.Write([]byte{0x00, 0x10}) // Stations=16
	v.Write([]byte{0x01, 0x00}) // StationLimit=256
	v.Write([]byte{0x00, 0x01}) // ActiveWTPs=1
	v.Write([]byte{0x00, 0x80}) // MaxWTPs=128
	v.Write([]byte{0x00, 0x00}) // Security flags
	v.Write([]byte{0x00, 0x00}) // R-MAC present
	v.Write([]byte{0x00, 0x00}) // Reserved

	v.Write([]byte{0x00, byte(len(soft))})
	v.Write(soft)
	v.Write([]byte{0x00, byte(len(hard))})
	v.Write(hard)

	me := make([]byte, 4+v.Len())
	binary.BigEndian.PutUint16(me[0:2], 2) // Type=2
	binary.BigEndian.PutUint16(me[2:4], uint16(v.Len()))
	copy(me[4:], v.Bytes())
	return me
}

func buildDiscoveryResponse(seq uint8, little bool, acIP net.IP) []byte {
	me2 := buildME_ACDescriptorBetter()
	me4 := buildME_ACName("LiteOn-FakeAC")
	me3 := buildME_ACIPv4List(acIP) // <-- LIST (ada Count)
	me16 := buildME_DTLSPolicy()

	msgElems := append([]byte{}, me2...)
	msgElems = append(msgElems, me4...)
	msgElems = append(msgElems, me3...)
	msgElems = append(msgElems, me16...)

	hdr := buildCapwapPreambleHeader8() // <-- header 8B dengan Type/Version benar
	ctrl := buildControlHeader(MT_DISCOVERY_RESP, seq, uint16(len(msgElems)), little)

	pkt := append(hdr, ctrl...)
	pkt = append(pkt, msgElems...)
	return pkt
}

func buildME_ACIPv4List(addrs ...net.IP) []byte {
	// ambil v4 saja
	v4s := make([]net.IP, 0, len(addrs))
	for _, ip := range addrs {
		if v4 := ip.To4(); v4 != nil {
			v4s = append(v4s, v4)
		}
	}
	if len(v4s) == 0 {
		v4s = []net.IP{net.IPv4(0, 0, 0, 0)}
	}
	payload := make([]byte, 1+4*len(v4s))
	payload[0] = byte(len(v4s))
	off := 1
	for _, v4 := range v4s {
		copy(payload[off:off+4], v4.To4())
		off += 4
	}
	me := make([]byte, 4+len(payload))
	binary.BigEndian.PutUint16(me[0:2], 3) // Type=3
	binary.BigEndian.PutUint16(me[2:4], uint16(len(payload)))
	copy(me[4:], payload)
	return me
}

// DTLS Policy (Type=16) — 0=plaintext
func buildME_DTLSPolicy() []byte {
	me := make([]byte, 5)
	binary.BigEndian.PutUint16(me[0:2], 16) // Type=16
	binary.BigEndian.PutUint16(me[2:4], 1)  // Length=1
	me[4] = 0x00                            // Value=0
	return me
}

// 8-byte CAPWAP header: Version=0 (high nibble), Type=1 (low nibble), HLEN=2 (8 bytes)
func buildCapwapPreambleHeader8() []byte {
	h := make([]byte, 8)
	h[0] = 0x01 // Version=0, Type=1 (control)
	h[1] = 0x20 // HLEN=2 (8 bytes / 4)
	return h
}

func putMsgElemLength(b []byte, off int, v uint16, little bool) {
	if little {
		binary.LittleEndian.PutUint16(b[off:off+2], v)
	} else {
		binary.BigEndian.PutUint16(b[off:off+2], v)
	}
}

// Control header: 4B MessageType (network order), 1B Seq, 2B MsgElemLength, 1B Flags
func buildControlHeader(msgType uint8, seq uint8, msgElemLen uint16, little bool) []byte {
	buf := make([]byte, 8)
	// Message Type: 00 00 00 <type>
	buf[3] = msgType
	buf[4] = seq
	putMsgElemLength(buf, 5, msgElemLen, little)
	buf[7] = 0x00 // Flags
	return buf
}

// ==== 802.11 helpers ====
func pmkFromPassphrase(passphrase, ssid string) []byte {
	return pbkdf2.Key([]byte(passphrase), []byte(ssid), 4096, 32, sha1.New)
}

func buildIE(id uint8, val []byte) []byte {
	out := make([]byte, 2+len(val))
	out[0] = id
	out[1] = uint8(len(val))
	copy(out[2:], val)
	return out
}

// Minimal RSN IE for WPA2-PSK (CCMP)
func rsnIE_CCMP_PSK() []byte {
	var b bytes.Buffer
	b.Write([]byte{0x01, 0x00})             // Version 1
	b.Write([]byte{0x00, 0x0f, 0xac, 0x04}) // Group cipher: CCMP
	b.Write([]byte{0x01, 0x00})             // Pairwise count =1
	b.Write([]byte{0x00, 0x0f, 0xac, 0x04}) // Pairwise: CCMP
	b.Write([]byte{0x01, 0x00})             // AKM count =1
	b.Write([]byte{0x00, 0x0f, 0xac, 0x02}) // AKM: PSK
	b.Write([]byte{0x00, 0x00})             // RSN Capabilities
	return buildIE(IE_RSN, b.Bytes())
}

// CAPWAP 802.11 Info Element (Type=1029) wrapping concatenated 802.11 IEs
func buildME_InfoElem(ies ...[]byte) []byte {
	payload := bytes.Join(ies, []byte{})
	me := make([]byte, 4+len(payload))
	binary.BigEndian.PutUint16(me[0:2], ME_INFO_ELE)
	binary.BigEndian.PutUint16(me[2:4], uint16(len(payload)))
	copy(me[4:], payload)
	return me
}

// Add WLAN (Type=1024) — simplified layout (vendor-neutral for lab):
// RadioID(1) | WLANID(1) | Capability(2) | KeyIndex(1) | KeyStatus(1) | KeyLength(2) | Key(Var)
// | GroupTSC(8+2) | QoS(1) | AuthType(1)
func buildME_AddWLAN(radioID, wlanID uint8, ssid, passphrase string) []byte {
	pmk := pmkFromPassphrase(passphrase, ssid)

	var v bytes.Buffer
	v.WriteByte(radioID)        // Radio
	v.WriteByte(wlanID)         // WLAN ID
	v.Write([]byte{0x00, 0x00}) // Capability (minimal)
	v.Write([]byte{0x00, 0x00}) // KeyIndex, KeyStatus
	b := make([]byte, 2)
	binary.BigEndian.PutUint16(b, uint16(len(pmk)))
	v.Write(b)                // KeyLength
	v.Write(pmk)              // Key (PMK 32 bytes)
	v.Write(make([]byte, 10)) // GroupTSC(10)
	v.WriteByte(0x00)         // QoS
	v.WriteByte(0x02)         // AuthType=PSK

	me := make([]byte, 4+v.Len())
	binary.BigEndian.PutUint16(me[0:2], ME_ADD_WLAN)
	binary.BigEndian.PutUint16(me[2:4], uint16(v.Len()))
	copy(me[4:], v.Bytes())
	return me
}

func buildConfigUpdateRequest(seq uint8, little bool, radioID, wlanID uint8, ssid, passphrase string) []byte {
	ieSSID := buildIE(IE_SSID, []byte(ssid))
	ieRSN := rsnIE_CCMP_PSK()
	meInfo := buildME_InfoElem(ieSSID, ieRSN)
	meAdd := buildME_AddWLAN(radioID, wlanID, ssid, passphrase)

	msgElems := append(meAdd, meInfo...)

	hdr := buildCapwapPreambleHeader8()
	ctrl := buildControlHeader(MT_CFGUPDATE_REQ, seq, uint16(len(msgElems)), little)

	pkt := append(hdr, ctrl...)
	pkt = append(pkt, msgElems...)
	return pkt
}

// Minimal “empty body” responses for 2/4/6/10
func buildSimpleResponse(msgType uint8, seq uint8, little bool) []byte {
	hdr := buildCapwapPreambleHeader8()
	ctrl := buildControlHeader(msgType, seq, 0, little)
	return append(hdr, ctrl...)
}

// ==== Server loop ====
func main() {
	flag.Parse()

	ssid := *ssidFlag
	psk := *passFlag
	if len(psk) < 8 || len(psk) > 63 {
		log.Fatalf("PSK length must be 8..63 chars")
	}

	radioID := uint8(*radioIDFlag)
	wlanID := uint8(*wlanIDFlag)
	useLE := *useLEFlag

	addr, err := net.ResolveUDPAddr("udp", *listenAddr)
	if err != nil {
		log.Fatal(err)
	}
	conn, err := net.ListenUDP("udp", addr)
	if err != nil {
		log.Fatal(err)
	}
	defer conn.Close()
	log.Printf("Fake CAPWAP AC (PLAINTEXT) listening on %s, SSID=%q, WLAN=%d, Radio=%d, LE=%v",
		*listenAddr, ssid, wlanID, radioID, useLE)

	buf := make([]byte, 65535)
	// Track last peer; simple single-WTP lab mode
	var peer *net.UDPAddr
	seq := uint8(1)

	for {
		n, raddr, err := conn.ReadFromUDP(buf)
		if err != nil {
			log.Println("read:", err)
			continue
		}
		payload := buf[:n]
		mt, ok := guessMsgType(payload)
		if !ok {
			log.Printf("unknown packet from %v len=%d", raddr, n)
			continue
		}
		if peer == nil {
			peer = raddr
		}

		log.Printf("← from %v msg_type=%d len=%d", raddr, mt, n)
		log.Printf("Payload (hex): %x\n", payload)
		log.Printf("Payload (bytes): %v\n", payload)
		log.Printf("DTLS :%v", isDTLS(payload))

		switch mt {
		case MT_DISCOVERY_REQ:
			log.Println("Masuk ke MT_DISCOVERY_REQ")
			parseDiscoveryRequest(payload)
			//reply := buildSimpleResponse(MT_DISCOVERY_RESP, seq, useLE)
			reply := buildDiscoveryResponse(seq, useLE, net.ParseIP("172.16.1.1"))

			seq++
			// send to the current raddr, not to a cached peer
			_, err := conn.WriteToUDP(reply, raddr)
			if err != nil {
				log.Printf("write err: %v", err)
			} else if os.Getenv("NOHEX") == "" {
				log.Printf("→ sent (to %v) len=%d hex=%s", raddr, len(reply), strings.ToUpper(hex.EncodeToString(reply)))
			}
			// NOTE: do NOT lock peer yet; wait until we receive a unicast Join Request (3)

		case MT_JOIN_REQ:
			log.Println("Masuk ke MT_JOIN_REQ")
			reply := buildSimpleResponse(MT_JOIN_RESP, seq, useLE)
			seq++
			peer = raddr
			send(conn, peer, reply)

		case MT_CFGSTAT_REQ:
			log.Println("Masuk ke MT_CFGSTAT_REQ")
			// Send 6, then 7
			resp6 := buildSimpleResponse(MT_CFGSTAT_RESP, seq, useLE)
			seq++
			send(conn, peer, resp6)

			time.Sleep(time.Duration(*send7DelayMs) * time.Millisecond)

			cfg7 := buildConfigUpdateRequest(seq, useLE, radioID, wlanID, ssid, psk)
			seq++
			send(conn, peer, cfg7)

		case MT_ECHO_REQ:
			log.Println("Masuk ke MT_ECHO_REQ")
			resp10 := buildSimpleResponse(MT_ECHO_RESP, seq, useLE)
			seq++
			send(conn, peer, resp10)

		case MT_CFGUPDATE_RESP:
			log.Printf("→ got Configuration Update Response (8) — AP acknowledged")

		default:
			log.Printf("unhandled msg_type=%d (no-op)", mt)
		}
	}
}

func send(c *net.UDPConn, addr *net.UDPAddr, pkt []byte) {
	_, err := c.WriteToUDP(pkt, addr)
	if err != nil {
		log.Printf("write err: %v", err)
		return
	}
	if os.Getenv("NOHEX") == "" {
		log.Printf("→ sent len=%d hex=%s", len(pkt), strings.ToUpper(hex.EncodeToString(pkt)))
	}
}

func isDTLS(payload []byte) bool {
	// Check for DTLS
	if len(payload) >= 13 && payload[0] >= 20 && payload[0] <= 23 &&
		payload[1] == 0xFE && (payload[2] == 0xFD || payload[2] == 0xFF) {
		log.Println("Detected DTLS packet")
		log.Printf("Content Type: %d\n", payload[0])
		log.Printf("Version: %x\n", payload[1:3])
		if payload[0] == 22 && len(payload) >= 14 && payload[13] == 1 {
			log.Println("DTLS Handshake: ClientHello")
		}
		return true
	}
	log.Println("Not a DTLS packet")

	return false
}

func guessMsgType(b []byte) (uint8, bool) {
	if len(b) < 12 {
		return 0, false
	}
	mt := b[11] // Byte terakhir dari Message Type (offset 11)
	if mt > 0 && mt < 64 {
		return mt, true
	}
	// Fallback loop (jika diperlukan)
	for off := 8; off <= 32; off += 4 {
		if len(b) >= off+4 {
			mt := b[off+3]
			if mt > 0 && mt < 64 {
				return mt, true
			}
		}
	}
	return 0, false
}

func parseDiscoveryRequest(payload []byte) {
	if len(payload) < 12 {
		fmt.Println("Payload too short for CAPWAP")
		return
	}
	preamble := payload[0]
	messageType := binary.BigEndian.Uint32(payload[8:12])
	mt, ok := guessMsgType(payload)
	if preamble == 0x10 && messageType == 1 && mt == 1 && ok {
		fmt.Println("CAPWAP Discovery Request detected")
	} else {
		fmt.Printf("Not a CAPWAP Discovery Request: Preamble=%x, MessageType=%d, guessMsgType=%d\n", preamble, messageType, mt)
		return
	}

	// Parsing Message Elements
	offset := 16
	for offset < len(payload) {
		if offset+4 > len(payload) {
			break
		}
		elemType := binary.BigEndian.Uint16(payload[offset : offset+2])
		elemLength := binary.BigEndian.Uint16(payload[offset+2 : offset+4])
		if offset+4+int(elemLength) > len(payload) {
			break
		}
		value := payload[offset+4 : offset+4+int(elemLength)]
		switch elemType {
		case 1: // Discovery Type
			if len(value) >= 1 {
				fmt.Printf("Discovery Type: %d (0=Unknown, 1=DHCP, 2=DNS)\n", value[0])
			}
		case 21: // WTP Software Version
			fmt.Printf("WTP Software Version: %s\n", string(value))
		case 38: // WTP Descriptor
			if len(value) >= 18 {
				mac := string(value[8:27]) // MAC sebagai string ASCII
				fmt.Printf("WTP Descriptor MAC: %s\n", mac)
			}
		case 39: // WTP Board Data
			if len(value) >= 16 {
				model := string(value[9:100])
				fmt.Printf("WTP Board Data Model: %s\n", model)
			}
		case 2: // WTP Hardware Address
			if len(value) >= 18 {
				mac := string(value[0:18])
				fmt.Printf("WTP Hardware Address: %s\n", mac)
			}
		}
		offset += 4 + int(elemLength)
	}
}
