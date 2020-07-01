/*
open util/ordering[Time]

sig Time {}
*/

abstract sig DP { 
  trust: Trust,
  components: set DP
}

sig Gateway extends DP {}

sig Vswitch, Mbox extends DP {
  SW: SWstate,
  pktPath: Paths,
} {components = none}

enum SWstate {Verified, Attested, Vulnerable}
enum Paths {Authenticated, Tagged, Original}

enum Trust {Trusted, NotTrusted}
sig TrustedDP in DP {}

sig MaliciousPkt {
  processBy: set DP,
  action: one Action
}

abstract sig Action {}
one sig Allow, Drop extends Action {}

fact {some MaliciousPkt}
fact {some Vswitch}
fact {some Mbox}
fact {some Gateway}

fact {all g: Gateway |   
  some v:Vswitch | v in g.components and
  some M:Mbox | M in g.components 
}

pred trustMbox [d: Mbox] {
  (((d.SW = Verified) or (d.SW = Attested)) and d.pktPath=Authenticated) <=>
  d.trust = Trusted
}

pred trustVswitch [d: Vswitch] {
  (((d.SW = Verified) or (d.SW = Attested)) and d.pktPath=Authenticated) <=>
  d.trust = Trusted
}

pred trustGW [g: Gateway] {
  g.trust=Trusted <=> (all x: g.components |
    x.trust=Trusted <=> 
      x in Vswitch =>
         trustVswitch[x]
     else
         trustMbox[x])
}


pred processPkt [p:MaliciousPkt, dp: Gateway] {
  p.processBy = dp
  (dp.trust = Trusted <=> trustGW[dp]) => p.action = Drop
  else p.action = Allow
}

fact {all v: Vswitch | trustVswitch[v]}
fact {all m: Mbox | trustMbox[m]}
fact {all g: Gateway | trustGW[g]}
fact {all dp: Gateway | (dp.trust=Trusted) <=> dp in TrustedDP}
fact {all p:MaliciousPkt | processPkt[p, Gateway] }


/*
fun processPath: DP -> DP {
  Vswitch -> Mbox +
  Mbox -> Vswitch
}
*/

assert badDP {
  all p: MaliciousPkt |  (processPkt[p, TrustedDP] => p.action = Drop)
}
check badDP for 10


// Generate instance of model
pred show() {}
run show for 10 
