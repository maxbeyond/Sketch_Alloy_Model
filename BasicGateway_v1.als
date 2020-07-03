abstract sig Host {
  trust: Trust
}

abstract sig DP extends Host { }
abstract sig CP extends Host { }

sig Gateway extends DP {
  channel: Channel,
  vswitch: set Vswitch,
  mbox: set Mbox,
  controller: one Controller
}

sig Vswitch, Mbox extends DP {
  SW: SWstate,
  pktsAccepted: Paths,
} 

// set of trusted gateways for processing packets
sig TrustedDP in Gateway {}

sig Controller extends CP {
  policy: Policy,
  channel: Channel,
  gateway: set Gateway
}

// packets that either container attacks or were modified on data plane
sig MaliciousPkt {
  processBy: set DP,
  action: one Action
}

enum SWstate {Attested, Vulnerable}
enum Paths {Authenticated, Tagged, Original}
enum Trust {Trusted, NotTrusted}
enum Policy {Protected, Exposed}
enum Channel {AuthEncryp, Encrypted, Plaintext}
enum Action {Allow, Drop}


// there are gateways, mboxes, vswitches, controllers, and malicious packets
fact {some MaliciousPkt}
fact {some Vswitch}
fact {some Mbox}
fact {some Gateway}
fact {some Controller}

// every gateway has at least one vswitch, mbox and a controller
fact {all g: Gateway |   
  some v:Vswitch | v in g.vswitch and
  some m:Mbox | m in g.mbox and 
  one c:Controller | c in g.controller
}

// ever controller has a gateway
fact {all c: Controller |
  some g: Gateway | g in c.gateway
}

// enforce relationship between controllers and gateways
fact {all c: Controller | all g: Gateway |
  g in c.gateway and c in g.controller
}

// mboxes must be part of a gateway
fact {all m:Mbox |
  some g:Gateway | m in g.mbox
}

// vswitch must be part of a gateway
fact {all v:Vswitch |
  some g:Gateway | v in g.vswitch
}

// mbox is trusted if its code is attested and pkts are authenticated
pred trustMbox [d: Mbox] {
  ((d.SW = Attested) and d.pktsAccepted=Authenticated) <=>
  d.trust = Trusted
}

// vswitch is trusted if its code is attested and pkts are authenticated
pred trustVswitch [d: Vswitch] {
  ((d.SW = Attested) and d.pktsAccepted=Authenticated) <=>
  d.trust = Trusted
}

// controller is trusted if control channel uses authenticated encryption and security policy is protected
pred trustController [c:Controller] {
  (c.channel = AuthEncryp and c.policy=Protected) <=>
  c.trust = Trusted
}

// gateway is trusted if controller is trusted, control channel uses authenticated encryption,
// all vswitchs are trusted, and all mboxes are trusted 
pred trustGW [g: Gateway] {
    ((all c: g.controller |
      c.trust=Trusted <=> trustController[c]) and
    (all v: g.vswitch |
      v.trust=Trusted <=> trustVswitch[v]) and
   (all m: g.mbox |
      m.trust=Trusted <=> trustMbox[m]) and 
   g.channel = AuthEncryp) <=> g.trust=Trusted
}



// if malicious packets are processed by a trusted gateway they are dropped
pred processPkt [p:MaliciousPkt, g: Gateway] {
  p.processBy = g
  (g.trust = Trusted <=> trustGW[g]) => p.action = Drop
  else p.action = Allow
}

// determine if devices are trusted
fact {all v: Vswitch | trustVswitch[v]}
fact {all m: Mbox | trustMbox[m]}
fact {all c: Controller | trustController[c]}
fact {all g: Gateway | trustGW[g]}
//fact {all c: Controller | all g: Gateway | trustController[c,g]}

// place trusted gateways into TrustedDP set
fact {all g: Gateway | (g.trust=Trusted) <=> g in TrustedDP}

// all malicious packets are processed by some gateway
fact {all p:MaliciousPkt | some g:Gateway | processPkt[p, g] }


// for a gateway to be trusted, its controller must also be trusted
assert controllerImpactsGW {
  some g: Gateway | g.trust = Trusted => g.controller.trust = Trusted
}
check controllerImpactsGW for 10

// a malicious packet processed by a trusted gateway must be dropped
assert badDP {
  all p: MaliciousPkt |  (processPkt[p, TrustedDP] => p.action = Drop)
}
check badDP for 10


// Generate instance(s) of model
pred show() {}
run show for 10 
