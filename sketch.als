enum Security {Trusted, NotTrusted}

sig Sequence {
  prev: lone Sequence,
  next: lone Sequence
}
one sig StartSeq, EndSeq in Sequence {}

// sig Data {}
sig Packet {
  sequence: one Sequence
  //data: one Data
}

sig PacketStream {
  packets: set Packet,
  startPkt: one Packet,
  endPkt: one Packet
}

// Sketch  <-  incoming  <-  NIC
// NIC  ->  outgoing  ->  Sketch
one sig Sketch {
 compute: Security,
 memory: Security,
  incoming: PacketStream,
  outgoing: PacketStream
}

one sig NIC {
  incoming: PacketStream,
  outgoing: PacketStream
}

// make sure sequence is consecutive
fact {
  no StartSeq.prev
  Sequence in StartSeq.*next
  all s: Sequence { s not in s.^next }

  no EndSeq.next
  Sequence in EndSeq.*prev
  all s: Sequence { s not in s.^prev }

  all s1, s2: Sequence { s1.next = s2 => s2.prev = s1 }
  all s1, s2: Sequence { s1.prev = s2 => s2.next = s1 }
}

// restriction for packet stream
fact {
  all ps: PacketStream {
    // make sure startPkt is before endPkt
    ps.endPkt.sequence in ps.startPkt.sequence.*next
    ps.startPkt.sequence in ps.endPkt.sequence.*prev

    // all pkt is between startPkt and endPkt
    all p: ps.packets | p.sequence in ps.startPkt.sequence.*next
    all p: ps.packets | p.sequence in ps.endPkt.sequence.*prev
	
	ps.startPkt in ps.packets
    ps.endPkt in ps.packets
  }
}

// sgx
fact {
  Sketch.compute = Trusted
  Sketch.memory = Trusted
}

// Sketch Checker and NIC Checker will guarantee 
// 1. all send pkt's sequence is successive
// 2. no send pkt has same sequence
pred SuccessiveSeq[ps: PacketStream] {
  all p1: ps.packets | 
    p1 != ps.endPkt => { 
      one p2: ps.packets | p2.sequence = p1.sequence.next}
}
pred NoDuplicateSeq[ps: PacketStream] {
  all p1, p2: ps.packets | p1 != p2 => p1.sequence != p2.sequence
}
fact {
  SuccessiveSeq[NIC.incoming]
  SuccessiveSeq[Sketch.outgoing]
  NoDuplicateSeq[NIC.incoming]
  NoDuplicateSeq[Sketch.outgoing]
}

// MAC ensures not injection (attacker could not spoof packets)
pred NoInject[sendPS, recvPS: PacketStream] {
  all p: recvPS.packets | p in sendPS.packets
}
fact {
  NoInject[NIC.incoming, Sketch.incoming]
  NoInject[Sketch.outgoing, NIC.outgoing]
}

// check successive seq => all previous packets are received
pred NoDrop [ps: PacketStream, startPkt: Packet] {
  all p1: ps.packets | p1 != startPkt => 
		{ one p2: ps.packets | p2.sequence = p1.sequence.prev }
}
fact {
  NoDrop[Sketch.incoming, NIC.incoming.startPkt]
  NoDrop[NIC.outgoing, Sketch.outgoing.startPkt]
}

// heartbeat/ACK is received
pred HeartbeatReceived [sendPS, recvPS: PacketStream] {
  sendPS.endPkt in recvPS.packets
}
fact {
  HeartbeatReceived[NIC.incoming, Sketch.incoming]
  HeartbeatReceived[Sketch.outgoing, NIC.outgoing]
}

// InputIntegrity
pred SamePacketStream[ps1, ps2: PacketStream] {
  all p: ps1.packets | p in ps2.packets
  all p: ps2.packets | p in ps1.packets
}
pred InputIntegrity [] {
  SamePacketStream[Sketch.incoming, NIC.incoming]
  SamePacketStream[Sketch.outgoing, NIC.outgoing]
}

pred ComputeIntegrity [] {
  Sketch.compute = Trusted
}

pred MemoryIntegrity [] {
  Sketch.memory = Trusted
}

assert TrustedSketch {
  InputIntegrity[]
  ComputeIntegrity[]
  MemoryIntegrity[]
}

check TrustedSketch for 5
// run InputIntegrity
