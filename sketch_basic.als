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

one sig PacketsBuffer {
  pktBuf: one Memory
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
  (PacketsBuffer.pktBuf.security = Safe) => {
    Sketch.incomingPackets = NIC.incomingPackets
    NIC.outgoingPackets = Sketch.incomingPackets
  }
}

// code and memory in enclave are safe
fact {
  all p: Program | (p.codeAttest = True) => (p.bootSecurity = Safe)
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

// InputIntegrity
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
    (!TrustedSketch[])
}
check PlainSystemFail for 5

// strawman (code attestation)
pred StrawmanCodeAttest[] {
  all p: Program | p.codeAttest = True
}

// code attestation would be compromised if attacker has root access
assert CodeAttestFail {
  (attackerHasRootAccess[] 
    && PlainSystem[] 
    && StrawmanCodeAttest[]) => 
      (!TrustedSketch[])
}
check CodeAttestFail for 5

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
      (!TrustedSketch[])
}
check SecureMemoryFail for 5

// only use enclave
pred OnlyEnclave[] {
  Sketch.program.programPostion = EnclaveProgram
  Sketch.counter.memoryType = EnclaveMemory
  Sketch.heap.memoryType = EnclaveMemory
  PacketsBuffer.memoryType = HostMemory
}

// secure memory would be compromised if attacker has root access
assert OnlyEnclaveFail {
  (attackerHasRootAccess[] 
    && OnlyEnclave[]) => 
      (!TrustedSketch[])
}
check OnlyEnclaveFail for 5

