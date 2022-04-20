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
sig Packet {
  hdr: one Data
}

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

pred TrustedSketch[] {
  ComputeIntegrity[]
  MemoryIntegrity[]
  InputIntegrity[]
}

fact {
  (Attacker.rootAccess = False) => {
    all p: Program | p.runSecurity = Safe
    all m: Memory | m.security = Safe
  }
}
fact {
  (PacketsBuffer.security = Safe) => {
    Sketch.incomingPackets = NIC.incomingPackets
    NIC.outgoingPackets = Sketch.outgoingPackets
  }
}