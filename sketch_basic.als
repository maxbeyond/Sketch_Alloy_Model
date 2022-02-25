open util/boolean
open util/integer

enum ProgramPostion { EnclaveProgram, HostProgram }
enum MemoryType { EnclaveMemory, SecureMemory, HostMemory }
enum Security { Safe, Compromised }

one sig Attacker {
  rootAccess: Bool
}

sig Program {
  programPostion: ProgramPostion,
  codeAttest: Bool,
  bootSecurity: Security,
  runSecurity: Security
}

sig Memory {
  memoryType: MemoryType,
  security: Security
}

sig Data {}
sig Packet {
  data: one Data
}

sig DatapathPkt extends Packet {}
one sig HeartBeatPkt extends Packet {}
one sig AckPkt extends Packet {}

// Sketch  <-  incoming  <-  NIC
// NIC  ->  outgoing  ->  Sketch
one sig Sketch {
  program: one Program,
  counter: one Memory,
  heap: one Memory,
  incomingPackets: seq Packet,
  outgoingPackets: seq Packet
}

one sig NIC {
  incomingPackets: seq Packet,
  outgoingPackets: seq Packet
}

one sig PacketsBuffer in Memory {}

sig AttestedPacket {
  pkt: one Packet,
  sequence: Int
}

one sig EnclaveChecker {
  incomingPackets: seq AttestedPacket,
  outgoingPackets: seq AttestedPacket
}

one sig NICChecker {
  incomingPackets: seq AttestedPacket,
  outgoingPackets: seq AttestedPacket
}

// if no attacker, assume program and memory are safe
fact {
  (Attacker.rootAccess = False) => {
    all p: Program | p.runSecurity = Safe
    all m: Memory | m.security = Safe
  }
}

// packets
// 1. sent by VM 
// 2. received from network (datapath)
// 3. heartbeat or ack pkt
fact {
  // all Packet instances are used in model
  HeartBeatPkt + AckPkt + DatapathPkt = Packet
  
  // no useless DatapathPkt
  all p: DatapathPkt | (p in NIC.incomingPackets.elems) || (p in Sketch.outgoingPackets.elems)
}

// if plain system, no heartbeat/ack packets
fact NoHeartbeat {
  PlainSystem[] => {
    all p: NIC.incomingPackets.elems | (p in DatapathPkt)
    all p: NIC.outgoingPackets.elems | (p in DatapathPkt)
    all p: Sketch.incomingPackets.elems | (p in DatapathPkt)
    all p: Sketch.outgoingPackets.elems | (p in DatapathPkt)
  }
  OurSystem[] => {
    all p: NIC.incomingPackets.elems | (p in DatapathPkt) || (p in HeartBeatPkt)
    all p: Sketch.outgoingPackets.elems | (p in DatapathPkt) || (p in AckPkt)
  }
}


// all AttestedPacket instances are used in model
fact {
  EnclaveChecker.incomingPackets.elems
  + EnclaveChecker.outgoingPackets.elems
  + NICChecker.incomingPackets.elems
  + NICChecker.outgoingPackets.elems
   = AttestedPacket
}

// no duplicate packets in sequence
// we use distinct Packet instance for input integrity check
fact NoDupPkt {
  !(NIC.incomingPackets.hasDups)
  !(NIC.outgoingPackets.hasDups)
  !(Sketch.incomingPackets.hasDups)
  !(Sketch.outgoingPackets.hasDups)

  // easy to check: 'NIC incoming pkts' and 'sketch outgoing pkts' has no overlap
  all p: NIC.incomingPackets.elems | !(p in Sketch.outgoingPackets.elems)
  all p: Sketch.outgoingPackets.elems | !(p in NIC.incomingPackets.elems)

}

// all Memory and Program instances are used in model
fact {
  Sketch.program = Program
  Sketch.counter + Sketch.heap + PacketsBuffer = Memory
}

// pkt stream is not changed only if PacketsBuffer is safe
// assume no packet drop due to buffer overflow
fact {
 (PacketsBuffer.security = Safe) => {
   Sketch.incomingPackets = NIC.incomingPackets
   NIC.outgoingPackets = Sketch.outgoingPackets
 }
}

// code attestation can guarantee boot security
fact {
  all p: Program | (p.codeAttest = True) => (p.bootSecurity = Safe)
}

// enclave safety guarantee
fact {
  // remote attestation can be used for code in enclav10
  all p: Program | (p.programPostion = EnclaveProgram) => (p.codeAttest = True)

  // code and memory in enclave are safe
  all p: Program | (p.programPostion = EnclaveProgram) => (p.runSecurity = Safe)
  all m: Memory | (m.memoryType = EnclaveMemory) => (m.security = Safe)
}

// strawman (code attestation) only guarantee boot security
fact {
  all p: Program | (p.codeAttest = True) => (p.bootSecurity = Safe)
}

// strawman (secure memory) only guarantee memory are safe
fact {
  all m: Memory | (m.memoryType = SecureMemory) => (m.security = Safe)
}

pred ComputeIntegrity [] {
  Sketch.program.bootSecurity = Safe
  Sketch.program.runSecurity = Safe
}

pred MemoryIntegrity [] {
  Sketch.counter.security = Safe && Sketch.heap.security = Safe
}

pred InputIntegrity[] {
  Sketch.incomingPackets = NIC.incomingPackets
  Sketch.outgoingPackets = NIC.outgoingPackets
}

pred TrustedSketch[] {
  ComputeIntegrity[]
  MemoryIntegrity[]
  InputIntegrity[]
}

// plain system : sketch is running in host memory
pred PlainSystem[] {
  Sketch.program.programPostion = HostProgram
  Sketch.counter.memoryType = HostMemory
  Sketch.heap.memoryType = HostMemory
  PacketsBuffer.memoryType = HostMemory
}

pred attackerHasRootAccess[] {
  Attacker.rootAccess = True
}

pred ComputeAttack[] {
  Sketch.program.bootSecurity = Compromised
  Sketch.program.runSecurity = Compromised
}

pred UseComputeAttack {
  attackerHasRootAccess[] && PlainSystem[]
  && ComputeAttack[] && (!ComputeIntegrity[])
}
run UseComputeAttack for 10

pred CounterAttack[] {
  Sketch.counter.security = Compromised
}

pred UseCounterAttack {
  attackerHasRootAccess[] && PlainSystem[]
  && CounterAttack[] && (!MemoryIntegrity[])
}
run UseCounterAttack for 10

pred HeapAttack[] {
  Sketch.heap.security = Compromised
}

pred UseHeapAttack {
  attackerHasRootAccess[] && PlainSystem[]
  && HeapAttack[] && (!MemoryIntegrity[])
}
run UseHeapAttack for 10

// inject packets
pred InjectAttack[] {
  some p: Sketch.incomingPackets.elems | !(p in NIC.incomingPackets.elems)
  some p: NIC.outgoingPackets.elems | !(p in Sketch.outgoingPackets.elems)

  all p: NIC.incomingPackets.elems | p in Sketch.incomingPackets.elems
  all p: Sketch.outgoingPackets.elems | p in NIC.outgoingPackets.elems
}

pred UseInjectAttack {
  attackerHasRootAccess[] && PlainSystem[]
  && InjectAttack[] && (!InputIntegrity[])
}
run UseInjectAttack for 10

// drop packets
pred DropAttack[] {
  some p: NIC.incomingPackets.elems | !(p in Sketch.incomingPackets.elems)
  some p: Sketch.outgoingPackets.elems | !(p in NIC.outgoingPackets.elems)
}

pred UseDropAttack {
  attackerHasRootAccess[] && PlainSystem[]
  && DropAttack[] && (!InputIntegrity[])
}
run UseDropAttack for 10

pred ModifyPS[PS1: seq Packet, PS2: seq Packet] {
  (#PS1) = (#PS2)
  // all i: Int | (lt[i, #PS1] && gte[i, 0]) => (PS1[i] != PS2[i])
  PS1.elems != PS2.elems
}

// modify outgoing packets
pred ModifyAttack[] {
  ModifyPS[NIC.incomingPackets, Sketch.incomingPackets]
  ModifyPS[NIC.outgoingPackets, Sketch.outgoingPackets]
}

pred UseModifyAttack {
  attackerHasRootAccess[] && PlainSystem[]
  && ModifyAttack[] && (!InputIntegrity[])
}
run UseModifyAttack for 10


// plain system would be compromised if attacker has root access
assert PlainSystemFail {
  (attackerHasRootAccess[] && PlainSystem[]) => 
    (TrustedSketch[])
}
check PlainSystemFail for 10

// Idea 1: use enclave
pred UseEnclave[] {
  Sketch.program.programPostion = EnclaveProgram
  Sketch.counter.memoryType = EnclaveMemory
  Sketch.heap.memoryType = EnclaveMemory
  PacketsBuffer.memoryType = HostMemory
}

// MAC ensures that attacker could not inject, modify packets
// all pkt in ps1 should be in ps2
pred MAC[ps1: seq AttestedPacket, ps2: seq AttestedPacket] {
  all p: ps1.elems | p in ps2.elems
}

// sequence number is successive
pred SuccessiveSeq[ps: seq AttestedPacket] {
  all i: Int | (lt[i, #ps] && gt[i, 0]) => (eq[ps[i].sequence, add[ps[sub[i, 1]].sequence, 1]])
}

// EnclaveChecker and NICChecker will start with the same sequence number
// ps1 <- memory <- ps2
pred StartSequence[ps1: seq AttestedPacket, ps2: seq AttestedPacket] {
  gt[#ps1, 0] => eq[ps1[0].sequence, ps2[0].sequence]
}

// we add attested data as packet header, so AttestedPacket and Packet should be the same packet
pred AddOrRemoveAttest[attestPS: seq AttestedPacket, PS: seq Packet] {
  (#attestPS) = (#PS)
  all i: Int | (lt[i, #PS] && gte[i, 0]) => (attestPS[i].pkt = PS[i])
}

// limit int range to avoid int overflow because alloy use 4 bit int default
fact {
  all p: AttestedPacket | lt[p.sequence, 6] && gt[p.sequence, -6]
}

// Idea 2: attestation protocol
pred AttestedProtocol[] {
  // MAC ensures that attacker could not inject, modify packets
  MAC[EnclaveChecker.incomingPackets, NICChecker.incomingPackets]
  MAC[NICChecker.outgoingPackets, EnclaveChecker.outgoingPackets]

  // successive sequence number 
  SuccessiveSeq[EnclaveChecker.incomingPackets]
  SuccessiveSeq[EnclaveChecker.outgoingPackets]
  SuccessiveSeq[NICChecker.incomingPackets]
  SuccessiveSeq[NICChecker.outgoingPackets]

  // add or remove attested data as packet header
  AddOrRemoveAttest[EnclaveChecker.incomingPackets, Sketch.incomingPackets]
  AddOrRemoveAttest[EnclaveChecker.outgoingPackets, Sketch.outgoingPackets]
  AddOrRemoveAttest[NICChecker.incomingPackets, NIC.incomingPackets]
  AddOrRemoveAttest[NICChecker.outgoingPackets, NIC.outgoingPackets]

  StartSequence[EnclaveChecker.incomingPackets, NICChecker.incomingPackets]
  StartSequence[NICChecker.outgoingPackets, EnclaveChecker.outgoingPackets]
}

// we use timeout mechanism to make sure at least one heartbeat will get ack packet
// here we model only that heartbeat/ack packet
// we can guarantee that input integrity for all packets before heartbeat/ack
pred SendHeartBeat[] {
  NIC.incomingPackets.last = HeartBeatPkt
}

pred RecvAckPacket[] {
  AckPkt in NIC.outgoingPackets.elems
}

// enclave would reply ack after receiving heartbeat pkt
fact EnclaveReplyAck {
  // we guarantee input integrity for 
  // 1. incomingPackets between 2 heartbeat
  // 2. outgoingPackets between 2 ack pkt
  // so we assume only 1 HeartBeatPkt and 1 AckPkt
  // both of them are the last in the sequence
  (HeartBeatPkt in Sketch.incomingPackets.elems)
    <=> (AckPkt in Sketch.outgoingPackets.elems)
  
  (AckPkt in Sketch.outgoingPackets.elems)
	=> (Sketch.outgoingPackets.last = AckPkt)
}

// Idea 3: heartbeat
pred HeartBeat[] {
  SendHeartBeat[]
  RecvAckPacket[]
}

pred OurSystem[] {
  UseEnclave[]
  AttestedProtocol[]
  HeartBeat[]
}

// Idea 1/2/3 will ensure trust sketch
assert OurSystemCorrect {
  (attackerHasRootAccess[] 
    && OurSystem[]) => 
      (TrustedSketch[])
}
check OurSystemCorrect for 10 but 4 Int

// Generate a sample instance of the model
pred simulate {
  attackerHasRootAccess[] 
  OurSystem[]
  TrustedSketch[]
}
// assume we have some in/out packets
run simulate for 10
