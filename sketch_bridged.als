enum ProgramPostion { EnclaveProgram, HostProgram }
enum MemoryType { EnclaveMemory, SecureMemory, HostMemory }
enum Security { Safe, Compromised }
sig Program {
  programPostion: ProgramPostion,
  codeAttestted: Bool,
  bootSecurity: Security,
  runSecurity: Security
}
sig DataInMemory {
  memoryType: MemoryType,
  security: Security
}
sig Packet {}
one sig Sketch {
  program: one Program,
  counter: one DataInMemory,
  heap: one DataInMemory,
  incomingPackets: seq Packet,
  outgoingPackets: seq Packet
}
one sig NIC {
  incomingPackets: seq Packet,
  outgoingPackets: seq Packet
}
one sig PacketsBuffer in DataInMemory {}
one sig Attacker {
  rootAccess: Bool
}
fact { // attack ability
  (Attacker.rootAccess = True) => {
    all p: Program | (p.programPostion = HostProgram) => (p.runSecurity = Compromised)
    all m: DataInMemory | (m.memoryType = HostMemory) => (m.security = Compromised)
  }
  else {
    all p: Program | p.runSecurity = Safe
    all m: DataInMemory | m.security = Safe
  }
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