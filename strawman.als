
// attacker ability: if get root access, all program and memory in host are compromised
  // else {
  //   all p: Program | (p.programPostion = HostProgram) => (p.runSecurity = Compromised)
  //   all m: Memory | (m.memoryType = HostMemory) => (m.security = Compromised)
  // }

// begin of strawman
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

// end of strawman


// begin: partial design fail
// Only using Idea 1 is insufficient if attacker has root access
assert OnlyEnclaveFail {
  (attackerHasRootAccess[] && UseEnclave[]) =>
      (TrustedSketch[])
}
check OnlyEnclaveFail for 10

// Idea 1 + Idea 2 still suffer from enclave-disconnect-attack
assert EnclaveAndAttestFail {
  (attackerHasRootAccess[] 
    && UseEnclave[]
    && AttestedProtocol[]) => 
      (TrustedSketch[])
}
check EnclaveAndAttestFail for 10

// end: partial design fail
