abstract sig Host {
  trust: Trust
}

abstract sig ReferenceMonitor {
  capabilities: set Capabilities
}

abstract sig DP extends Host { }
abstract sig CP extends Host { }

sig Gateway extends DP {
  vswitch: set Vswitch,
  mbox: set Mbox,
  controller: one Controller,
  channel: Channel,
  channelProtection: Agent,
  hyp: lone Hypervisor,
  sysResource: CritStateorOp
}

sig Vswitch, Mbox extends DP {
  SW: SWstate,
  SWprotection: Agent,
  pktsAccepted: Paths,
  pktProtection: Agent
} 

// set of trusted gateways for processing packets
sig TrustedDP in Gateway {}

sig Controller extends CP {
  apps: set Apps,
  appProection: apps -> Agent,
  policy: CritStateorOp,
  policyProtection: Agent, 
  channel: Channel,
  channelProtection: Agent,
  gateway: set Gateway,
  hyp: lone Hypervisor,
  sysResource: CritStateorOp
}

abstract sig Apps {
  state: CritStateorOp,
  ops: CritStateorOp
}

one sig PolicyApp, OtherApp extends Apps {}

sig Hypervisor extends ReferenceMonitor {
  agent: set Agent
}

abstract sig Agent {
 leverages: set Capabilities
}

sig PktSign, CommAgent, AppProtect, vTPM extends Agent {}

abstract sig Pkt {
  processBy: set DP,
  action: one Action
}
// packets that either container attacks or were modified on data plane
sig MaliciousPkt extends Pkt { }
sig BenignPkt extends Pkt { }

enum SWstate {Attested, Vulnerable}
enum Paths {Authenticated, Tagged, Original}
enum Trust {Trusted, NotTrusted}
enum CritStateorOp {Protected, Exposed}
enum Channel {AuthEncryp, Encrypted, Plaintext}
enum Action {Allow, Drop}

enum Capabilities {Attestation, Isolation, Mediation}


// there are gateways, mboxes, vswitches, controllers, and malicious packets
fact {some MaliciousPkt}
fact {some BenignPkt}
fact {some Vswitch}
fact {some Mbox}
fact {some Gateway}
fact {some Controller}
fact {some Hypervisor}

// every gateway has at least one vswitch, mbox and a controller
fact {all g: Gateway | {
    some v:Vswitch | v in g.vswitch 
    some m:Mbox | m in g.mbox  
    one c:Controller | c in g.controller  
    one h:Hypervisor | h in g.hyp
  }
}

// ever controller has a gateway
fact {all c: Controller | {
    some g: Gateway | g in c.gateway 
    one h:Hypervisor | h in c.hyp
    one a: PolicyApp | a in c.apps
  }
}

// enforce relationship between controllers and gateways
fact {all c: Controller, g: Gateway |
    g in c.gateway and c in g.controller
}

// mboxes must be part of a gateway
fact {all m:Mbox |
  one g:Gateway | m in g.mbox
}

// vswitch must be part of a gateway
fact {all v:Vswitch |
  one g:Gateway | v in g.vswitch
}

// all apps must be in a controller
fact {all a: Apps | 
  some c: Controller | a in c.apps
}

// all agents must be in a hypervisor
fact {all a: Agent | {
    some c: Capabilities | c in a.leverages
    some h: Hypervisor | a in h.agent
    all g: Gateway, c: Controller | (a in g.hyp.agent or a in c.hyp.agent)
  }  
}

// hypervisors only with gateways or controllers
fact {all h: Hypervisor | {
    Capabilities in h.capabilities
    some a: Agent | a in h.agent
    all g: Gateway, c: Controller | h in (g.hyp + c.hyp) 
  }
}

fact {all g: Gateway, c: Controller | 
  disj [g.hyp, c.hyp]
}

// mbox is trusted if its code is attested and pkts are authenticated
pred trustMbox [d: Mbox] {
    d.SW = Attested
    d.pktsAccepted = Authenticated
}

// vswitch is trusted if its code is attested and pkts are authenticated
pred trustVswitch [d: Vswitch] {
    d.SW = Attested
    d.pktsAccepted=Authenticated
}


// alternative for trustGW
pred gatewayTest[g:Gateway] {
  all m: g.mbox | {
    (m.pktsAccepted = Authenticated) <=> authPkt[m,g] 
    (m.SW = Attested) <=> attestedSW[m,g]
  }
  all v: g.vswitch | {
   (v.pktsAccepted = Authenticated) <=> authPkt[v,g]
   (v.SW = Attested) <=> attestedSW[v,g]
  }
  all c: g.controller | {
/*
    (c.policy = Protected) <=> PolicySecured[c]
*/
    all a: c.apps |
      ((a = PolicyApp) and (a.state = Protected) and (a.ops = Protected)) <=>
        PolicySecured[c, a]
    (c.channel = AuthEncryp) <=> AuthEncrypChannel[c]
  }
  (g.channel = AuthEncryp) <=> AuthEncrypChannel[g]
}  

// packet follows the correct path
pred processPktCorrectly [p: Pkt, g: Gateway] { 
  (correctGW[g]) and processPkt[p,g]
}

// gateway enforces packets following the correct path
pred correctGW[g:Gateway] {
  all v:g.vswitch, m:g.mbox | { correctPktPath[v,m] 
    correctSW[v] 
    correctSW[m]
  }
  all c: g.controller | { secureChannel[g,c] 
    securePolicy[c]
  }
}

// correct packet routing on the data channel
pred correctPktPath[v: Vswitch, m: Mbox] {
  v.pktsAccepted = Authenticated
  m.pktsAccepted = Authenticated
}

// correct sw on the data plane
pred correctSW[v: Vswitch] {
  v.SW = Attested
}
pred correctSW[m: Mbox] {
  m.SW = Attested
}

// secure control channel
pred secureChannel[g: Gateway, c: Controller] {
  g.channel = AuthEncryp
  c.channel = AuthEncryp
}

// security policy is protected from attackers
pred securePolicy[c: Controller] {
  c.policy=Protected
}


// controller is trusted if control channel uses authenticated encryption and security policy is protected
pred trustController [c:Controller] {
    c.channel = AuthEncryp
    c.policy=Protected
}

// gateway is trusted if controller is trusted, control channel uses authenticated encryption,
// all vswitchs are trusted, and all mboxes are trusted 
pred trustGW [g: Gateway] {
    all c: g.controller | c.trust=Trusted
    all v: g.vswitch | v.trust=Trusted
    all m: g.mbox | m.trust=Trusted
    g.channel = AuthEncryp
}

// if malicious packets are processed by a trusted gateway they are dropped
pred processPkt [p:Pkt, g: Gateway] {
  p.processBy = g
  trustGW[g] <=> (g.trust = Trusted)
  (p in MaliciousPkt) => 
    (g.trust = Trusted) => p.action = Drop
    else p.action = Allow
  else
    (g.trust = Trusted) => p.action = Allow
    else p.action = Drop
}

// SW that is Attested requiers an agent to attest it
pred attestedSW[d: Mbox, g:Gateway] {
  d.SWprotection = vTPM
  vTPM in g.hyp.agent 
}

// pkts that are authenticated require an agent to perform action
pred authPkt[d: Mbox, g: Gateway] {
  d.pktProtection = PktSign
  PktSign in g.hyp.agent
}

pred attestedSW[d: Vswitch, g:Gateway] {
  d.SWprotection=vTPM
  vTPM in g.hyp.agent 
}

pred authPkt[d: Vswitch, g: Gateway] {
  d.pktProtection = PktSign
  PktSign in g.hyp.agent
}

pred AuthEncrypChannel [g: Gateway] {
  g.channelProtection = CommAgent
  CommAgent in g.hyp.agent
}

pred AuthEncrypChannel [c: Controller] {
  c.channelProtection = CommAgent
  CommAgent in c.hyp.agent
}

pred PolicySecured [c: Controller] {
  c.policyProtection = AppProtect
  AppProtect in c.hyp.agent
}

pred PolicySecured [c: Controller, a: Apps] {
  c.appProection[a] = AppProtect
  AppProtect in c.hyp.agent
}

//hypervisor capabilities required and utilized by different agents
pred vTPMreq [a: Agent, h:Hypervisor] {
  (Mediation + Attestation + Isolation) in h.capabilities
  a.leverages = (Mediation + Isolation + Attestation)
}

pred SecPolicyReq [a: Agent, h: Hypervisor] {
  (Mediation + Isolation) in h.capabilities 
  a.leverages = (Mediation + Isolation)
}

pred CommAgentReq [a: Agent, h: Hypervisor] {
  (Mediation + Isolation) in h.capabilities 
  a.leverages = (Mediation + Isolation)
}

pred PktSignReq [a: Agent, h: Hypervisor] {
  (Mediation + Isolation) in h.capabilities 
  a.leverages = (Mediation + Isolation)
}

fact {all c: Controller | (c.trust = Trusted) <=> trustController[c]}
fact {all g: Gateway | {
    all m: g.mbox | (m.trust = Trusted) <=> trustMbox[m]
    all v: g.vswitch | (v.trust = Trusted) <=> trustVswitch[v]
    (g.trust = Trusted) <=> trustGW[g] 
  }
}


// trust foundation (gateway)
fact {all g:Gateway | {
    all m: g.mbox | {
      (m.SW = Attested) <=> attestedSW[m,g]
      (m.pktsAccepted = Authenticated) <=> authPkt[m,g]
    }
    all v: g.vswitch | {
      (v.SW = Attested) <=> attestedSW[v,g]
      (v.pktsAccepted = Authenticated) <=> authPkt[v,g]
    }
    (g.channel=AuthEncryp)<=>AuthEncrypChannel[g]
  }
}

// trust foundations (controller)
fact {all c:Controller | {
    (c.channel = AuthEncryp) <=> AuthEncrypChannel[c]
    (c.policy = Protected) <=> PolicySecured[c]
  }
}


// Mapping of hypervisor agents to ref monitor capabilities
fact {all h: Hypervisor | 
  all a: h.agent | {
    (a in PktSign) => PktSignReq[a,h]
    (a in CommAgent) => CommAgentReq[a,h]
    (a in AppProtect) => SecPolicyReq[a,h]
    (a in vTPM) => vTPMreq[a,h]
  }
}


// place trusted gateways into TrustedDP set
fact {all g: Gateway | (g.trust=Trusted) <=> (g in TrustedDP)}

// all malicious packets are processed by some gateway
fact {all p:Pkt | some g:Gateway | processPkt[p, g] }

/* Example Attack Logic */
// Control Channel:  Sniff
pred canSeeFlow [g:Gateway] {
  g.channel = Plaintext or g.controller.channel = Plaintext
}

// Control Channel: Modify (eg MitM)
pred canModFlow [g:Gateway] {
  g.channel = Plaintext or 
  g.controller.channel = Plaintext or 
  g.vswitch.SW = Vulnerable
}

// Control Channel: Inject
pred canInjectFlow [g:Gateway] {
  ( (g.channel = Plaintext) or (g.channel = Encrypted) ) or 
  ( (g.controller.channel = Plaintext) or (g.controller.channel = Encrypted) ) or
  g.vswitch.SW = Vulnerable
}

// Controller App: Mod State (some app)
pred canModAppState [c: Controller] {
  some a: c.apps | a.state = Exposed
}

// Controller App: Mod State (specific app)
pred canModAppState [c: Controller, a: Apps] {
  a in c.apps
  a.state = Exposed
}

// Controller App: Mod Operation (some app)
pred canModAppOps [c: Controller] {
  some a: c.apps | a.ops = Exposed
}

// Controller App: Mod Operation (specific app)
pred canModAppOps [c: Controller, a: Apps] {
  a in c.apps 
  a.ops = Exposed
}

// Controller: tamper with some reource
pred canTamperwithResource [c: Controller] {
  c.sysResource = Exposed
}

// Gateway: tamper with some reource
pred canTamperwithResource [g: Gateway] {
  g.sysResource = Exposed
}

// Controller: protect some reource
pred protectedResource[c: Controller] {
  let h = c.hyp |
  (c.sysResource = Protected) <=> (
    ( (Mediation + Isolation) in h.capabilities ) ) 
}

// Controller: protect some reource
pred protectedResource[g: Gateway] {
  let h = g.hyp |
  (g.sysResource = Protected) <=> (
    ( (Mediation + Isolation) in h.capabilities ) ) 
}

// Check for attacker ability to sniff
assert attackerSniffsFlow {
  some g:Gateway | !canSeeFlow[g]
}
check attackerSniffsFlow for 10

// Attacker can't sniff flows on trusted GW
assert attackerNotSniffTrsutedGWFlows {
  some g:Gateway | 
    trustGW[g] => ! canSeeFlow[g] 
}
check attackerNotSniffTrsutedGWFlows for 10

// Attacker can mod flows (allow attack)
assert attackerModsFlow {
  some g:Gateway | all p:MaliciousPkt | 
    (canModFlow[g] and processPkt[p,g]) => p.action = Drop
}
check attackerModsFlow for 10

// Attacker can't mod flows on trusted GW
assert attackerNotModsTrsutedGWFlows {
  some g:Gateway | 
    trustGW[g] => ! canModFlow[g] 
}
check attackerNotModsTrsutedGWFlows for 10

// Attacker can inject flows (allow attack)
assert attackerInjectsFlow {
  some g:Gateway | all p:MaliciousPkt | 
    (canInjectFlow[g] and processPkt[p,g]) => p.action = Drop
}
check attackerInjectsFlow for 10

// Attacker can't inject flows on trusted GW
assert attackerNotInjectTrsutedGWFlows {
  some g:Gateway | 
    trustGW[g] => ! canInjectFlow[g] 
}
check attackerNotInjectTrsutedGWFlows for 10

// Attacker can modify an apps state (allow attack)
assert attackerModAppState {
  some c: Controller | some g:Gateway | all p:MaliciousPkt |
    (canModAppState[c] and processPkt[p,g]) => p.action = Drop
}
check attackerModAppState for 10

// Attacker can't modify policy apps state 
assert attackerNotModTrustedAppState {
  some c: Controller | some a: c.apps |
    (trustController[c] and (a = PolicyApp)) => ! canModAppState[c, a]
}
check attackerNotModTrustedAppState for 10

// Attacker can modify an apps ops (allow attack)
assert attackerModAppOps {
  some c: Controller | some g:Gateway | all p:MaliciousPkt |
    (canModAppOps[c] and processPkt[p,g]) => p.action = Drop
}
check attackerModAppOps for 10

// Attacker can't modify policy apps ops 
assert attackerNotModTrustedAppOps {
  some c: Controller | some a: c.apps |
    (trustController[c] and (a = PolicyApp)) => ! canModAppOps[c, a]
}
check attackerNotModTrustedAppOps for 10

// Attacker can't tamper with a protected resource on gateway or controller
assert protectSysResource {
 some c: Controller |
    protectedResource[c] => ! canTamperwithResource[c]
  some g: Gateway | 
    protectedResource[g] => ! canTamperwithResource[g]
}

// Generate a sample instance of the model
pred simulate {
  some TrustedDP
}
run simulate for 5
