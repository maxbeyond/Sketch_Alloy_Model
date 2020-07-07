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
  hyp: lone Hypervisor
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
  policy: Policy,
  policyProtection: Agent, 
  channel: Channel,
  channelProtection: Agent,
  gateway: set Gateway,
  hyp: lone Hypervisor
}

sig Hypervisor extends ReferenceMonitor {
  agent: set Agent
}

abstract sig Agent {
 leverages: set Capabilities
}
sig PktSign, CommAgent, SecPolicy, vTPM extends Agent {}

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
enum Policy {Protected, Exposed}
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
  }
}

// enforce relationship between controllers and gateways
fact {all c: Controller, g: Gateway | {
    g in c.gateway and c in g.controller
  }
}

// mboxes must be part of a gateway
fact {all m:Mbox |
  one g:Gateway | m in g.mbox
}

// vswitch must be part of a gateway
fact {all v:Vswitch |
  one g:Gateway | v in g.vswitch
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

fact {all g: Gateway, c: Controller | {
    disj [g.hyp, c.hyp] 
//    disj [g.hyp.agent, c.hyp.agent]
  }
}


// mbox is trusted if its code is attested and pkts are authenticated
pred trustMbox [d: Mbox, g: Gateway] {
    d.SW = Attested
    d.pktsAccepted = Authenticated
}

// vswitch is trusted if its code is attested and pkts are authenticated
pred trustVswitch [d: Vswitch, g:Gateway] {
    d.SW = Attested
    d.pktsAccepted=Authenticated
}


// packets authenticated by PktSigning
pred correctPkts[g:Gateway] {
  all m: g.mbox | {
    (m.pktsAccepted = Authenticated) <=> authPkt[m,g] 
    (m.SW = Attested) <=> attestedSW[m,g]
  }
  all v: g.vswitch | {
   (v.pktsAccepted = Authenticated) <=> authPkt[v,g]
   (v.SW = Attested) <=> attestedSW[v,g]
  }
}  


// controller is trusted if control channel uses authenticated encryption and security policy is protected
pred trustController [c:Controller] {
    c.channel = AuthEncryp
    c.policy=Protected
}

// gateway is trusted if controller is trusted, control channel uses authenticated encryption,
// all vswitchs are trusted, and all mboxes are trusted 
pred trustGW [g: Gateway] {
    correctPkts[g]
    all c: g.controller | c.trust=Trusted
    all v: g.vswitch | v.trust=Trusted
    all m: g.mbox | m.trust=Trusted
    g.channel = AuthEncryp
}

// if malicious packets are processed by a trusted gateway they are dropped
pred processPkt [p:Pkt, g: Gateway] {
  p.processBy = g
  p in MaliciousPkt =>
    (g.trust = Trusted <=> trustGW[g]) => p.action = Drop
    else p.action = Allow
  else
     (g.trust = Trusted <=> trustGW[g]) => p.action = Allow
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
  c.policyProtection = SecPolicy
  SecPolicy in c.hyp.agent
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
    all m: g.mbox | (m.trust = Trusted) <=> trustMbox[m,g]
    all v: g.vswitch | (v.trust = Trusted) <=> trustVswitch[v,g]
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
    (a in SecPolicy) => SecPolicyReq[a,h]
    (a in vTPM) => vTPMreq[a,h]
  }
}


// place trusted gateways into TrustedDP set
fact {all g: Gateway | (g.trust=Trusted) <=> (g in TrustedDP)}

// all malicious packets are processed by some gateway
fact {all p:Pkt | some g:Gateway | processPkt[p, g] }


assert checkTrustedMbox {
  some g: Gateway | some m: g.mbox | (m.trust = Trusted) => (
    attestedSW[m,g] and authPkt[m,g]
  )
}
check checkTrustedMbox for 5

// for a gateway to be trusted, its controller must also be trusted
assert controllerImpactsGW {
  some g: Gateway | (g.trust = Trusted) => (g.controller.trust = Trusted)
}
check controllerImpactsGW for 10

// a malicious packet processed by a trusted gateway must be dropped
// a benign packet is output
assert badDP {
  all p: Pkt |  
    p in MaliciousPkt => 
      (processPkt[p, TrustedDP] => p.action = Drop)
    else
      (processPkt[p, TrustedDP] => p.action = Allow)
}
check badDP for 10


// Generate a sample instance of the model
pred simulate {
  some TrustedDP
}
run simulate for 15
