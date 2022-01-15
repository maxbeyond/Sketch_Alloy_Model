open util/boolean
open util/integer

enum ProgramPostion { EnclaveProgram, HostProgram }
enum MemoryType { EnclaveMemory, SecureMemory, HostMemory }
enum Security { Safe, Compromised }

// one sig Server {
//   os: one OS
// }
// sig OS {
//   security: Security
// }

one sig Attacker {
  rootAccess: Bool
}

sig Program {
  programPostion: ProgramPostion,
  security: Security
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

// attacker ability: if get root access, all program and memory are compromised
fact {
  (Attacker.rootAccess = True) => {
    all p: Program | p.programPostion = HostProgram => p.security = Compromised
    all m: Memory | m.memoryType = HostMemory => m.security = Compromised
  }
  else {
    all p: Program | p.security = Safe
    all m: Memory | m.security = Safe
  }
}

// pkt stream is not changed only if PacketsBuffer is safe
// assume no packet drop due to buffer overflow
fact {
  PacketsBuffer.pktBuf.security = Safe => {
    Sketch.incomingPackets = NIC.incomingPackets
    NIC.outgoingPackets = Sketch.incomingPackets
  }
}

// code and memory in enclave are safe
fact {
  all p: Program | (p.programPostion = EnclaveProgram) => (p.security = Safe)
  all m: Memory | (m.memoryType = EnclaveMemory) => (m.security = Safe)
}

// strawman (secure memory) only guarantee memory are safe
fact {
  all m: Memory | (m.memoryType = SecureMemory) => (m.security = Safe)
}

pred ComputeIntegrity [] {
  Sketch.program.security = Safe
}

pred MemoryIntegrity [] {
  Sketch.counter.security = Safe && Sketch.heap.security = Safe
}

// InputIntegrity
// pred SamePacketStream[ps1, ps2: PacketStream] {
// //   all p: ps1.packets | p in ps2.packets
// //   all p: ps2.packets | p in ps1.packets
//     ps1 = ps2
// }
pred InputIntegrity[] {
  Sketch.incomingPackets = NIC.incomingPackets
  Sketch.outgoingPackets = NIC.outgoingPackets
  // SamePacketStream[Sketch.incoming, NIC.incoming]
  // SamePacketStream[Sketch.outgoing, NIC.outgoing]
}

pred TrustedSketch[] {
  InputIntegrity[]
  ComputeIntegrity[]
  MemoryIntegrity[]
}

// sketch is running in host memory
pred sketchInHostMemory[] {
  Sketch.program.programPostion = HostProgram
  Sketch.counter.memoryType = HostMemory
  Sketch.heap.memoryType = HostMemory
}

pred attackerGetRootAccess[] {
  Attacker.rootAccess = True
}

assert attackSuccess {
  (attackerGetRootAccess[] && sketchInHostMemory[]) => 
    (!TrustedSketch[])
}

check attackSuccess for 5

// run InputIntegrity
