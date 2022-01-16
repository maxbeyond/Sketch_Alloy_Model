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

// attacker ability: if get root access, all program and memory in host are compromised
fact {
  (Attacker.rootAccess = True) => {
    all p: Program | (p.programPostion = HostProgram) => (p.runSecurity = Compromised)
    all m: Memory | (m.memoryType = HostMemory) => (m.security = Compromised)
  }
  else {
    all p: Program | p.runSecurity = Safe
    all m: Memory | m.security = Safe
  }
}

// pkt stream is not changed only if PacketsBuffer is safe
// assume no packet drop due to buffer overflow
fact {
  (PacketsBuffer.security = Safe) => {
    Sketch.incomingPackets = NIC.incomingPackets
    NIC.outgoingPackets = Sketch.incomingPackets
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
  InputIntegrity[]
  ComputeIntegrity[]
  MemoryIntegrity[]
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

// plain system would be compromised if attacker has root access
assert PlainSystemFail {
  (attackerHasRootAccess[] && PlainSystem[]) => 
    (TrustedSketch[])
}
check PlainSystemFail for 10

// strawman (code attestation)
pred StrawmanCodeAttest[] {
  all p: Program | p.codeAttest = True
}

// code attestation would be compromised if attacker has root access
assert CodeAttestFail {
  (attackerHasRootAccess[] 
    && PlainSystem[] 
    && StrawmanCodeAttest[]) => 
      (TrustedSketch[])
}
check CodeAttestFail for 10

// strawman (secure memory)
pred StrawmanSecureMemory[] {
  Sketch.program.programPostion = HostProgram
  Sketch.counter.memoryType = SecureMemory
  Sketch.heap.memoryType = SecureMemory
  PacketsBuffer.memoryType = HostMemory
}

// secure memory would be compromised if attacker has root access
assert SecureMemoryFail {
  (attackerHasRootAccess[] 
    && StrawmanSecureMemory[]) => 
      (TrustedSketch[])
}
check SecureMemoryFail for 10

// Idea 1: use enclave
pred UseEnclave[] {
  Sketch.program.programPostion = EnclaveProgram
  Sketch.counter.memoryType = EnclaveMemory
  Sketch.heap.memoryType = EnclaveMemory
  PacketsBuffer.memoryType = HostMemory
}

// Only using Idea 1 is insufficient if attacker has root access
assert OnlyEnclaveFail {
  (attackerHasRootAccess[] && UseEnclave[]) =>
      (TrustedSketch[])
}
check OnlyEnclaveFail for 10

// MAC ensures that attacker could not inject, modify packets
// all pkt in ps1 should be in ps2
pred MAC[ps1: seq AttestedPacket, ps2: seq AttestedPacket] {
  all p: ps1.elems | p in ps2.elems
}

// sequence number is successive
pred SuccessiveSeq[ps: seq AttestedPacket] {
  all i: Int | (i < #ps && i > 0) => (ps[i].sequence = ps[i - 1].sequence + 1)
}

// we add attested data as packet header, so AttestedPacket and Packet should be the same packet
pred AddOrRemoveAttest[attestPS: seq AttestedPacket, PS: seq Packet] {
  #attestPS = #PS
  all i: Int | (i < #PS) => (attestPS[i].pkt = PS[i])
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
}

// Idea 1 + Idea 2 still suffer from enclave-disconnect-attack
assert EnclaveAndAttestFail {
  (attackerHasRootAccess[] 
    && UseEnclave[]
    && AttestedProtocol) => 
      (TrustedSketch[])
}
check EnclaveAndAttestFail for 10
