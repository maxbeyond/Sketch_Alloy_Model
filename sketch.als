
// sig PacketStream {}

one sig Sketch {
  compute: Trust,
  memory: Trust,
  incoming: PacketStream
  outgoing: PacketStream
}

one sig NIC {
  incoming: PacketStream
  outgoing: PacketStream
}

enum Trust {Trusted, NotTrusted}

sig Data {}

sig PacketStream {
  packets: set Packet
  startPkt: one Packet
  endPkt: one Packet
}

// sig Data {}
sig Packet {
  sequence: one Sequence
  //data: one Data
}

sig Sequence {
  prev: lone Sequence,
  next: lone Sequence
}

one sig StartSeq, EndSeq extends Sequence {}
one sig StartPkt, EndPkt extends Packet {}

one sig Recv, Send extends PacketStream {}

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

fact {
  // make sure StartPkt is before EndPkt
  EndPkt.sequence in StartPkt.sequence.*next
  StartPkt.sequence in EndPkt.sequence.*prev

  // all send pkt is between StartPkt and EndPkt
  all p: Send.packets | p.sequence in StartPkt.sequence.*next
  all p: Send.packets | p.sequence in EndPkt.sequence.*prev

  // no send pkt has same sequence
  all p1, p2: Send.packets | p1 != p2 => p1.sequence != p2.sequence
}

fact {
  // MAC ensures not injection (attacker could not spoof packets)
  all p: Recv.packets | p in Send.packets
  
  // heartbeat is received
  EndPkt in Recv.packets

  // Recv check sequence => all previous packets are received
  all p: Recv.packets | p != StartPkt => 
		{ one prev_p: Recv.packets | prev_p.sequence = p.sequence.prev }
}

assert InputIntegrity {
  // Recv == Send
  all p: Send.packets | p in Recv.packets
  all p: Recv.packets | p in Send.packets
}

check InputIntegrity for 5

// // no recv pkt has same sequence
// all p1, p2: Recv.packets | p1 != p2 => p1.sequence != p2.sequence
