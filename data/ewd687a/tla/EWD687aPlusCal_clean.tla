-------------------------- MODULE EWD687aPlusCal --------------------------

EXTENDS Integers, FiniteSets, TLC

CONSTANT
Node,
initiator,
maxMsg

ASSUME /\ IsFiniteSet(Node)
/\ initiator \in Node

none == CHOOSE x : x \notin Node

terminationDetected = FALSE,

network = [n \in Node |-> [msg |-> [snd \in Node |-> 0], ack |-> 0]];
define {

sendMsg(net, from, to) == [net EXCEPT ![to].msg[from] = @+1]
pendingMsg(net, to, from) == net[to].msg[from] > 0
receiveMsg(net, to, from) == [net EXCEPT ![to].msg[from] = @-1]
sendAck(net, to) == [net EXCEPT ![to].ack = @+1]
pendingAck(net, to) == net[to].ack > 0
receiveAck(net, to) == [net EXCEPT ![to].ack = @-1]
}
fair process (node \in Node)
variables active = (self = initiator),
parent = IF self = initiator THEN self ELSE none,
activeSons = 0;
{
l:  while (TRUE) {
either {
when active;
with (dst \in Node \ {self}) {
network := sendMsg(network, self, dst)
};
activeSons := activeSons + 1
} or {
when active;
active := FALSE
} or {
with (snd \in Node) {
when pendingMsg(network, self, snd);
active := TRUE;
with (net = receiveMsg(network, self, snd)) {

if (parent = none) {
parent := snd;
network := net
} else {
network := sendAck(net, snd)
}
}
}
} or {
when pendingAck(network, self);
network := receiveAck(network, self);
activeSons := activeSons - 1
} or {
when (~active /\ activeSons = 0 /\ parent # none);
if (parent = self) {
terminationDetected := TRUE
} else {
network := sendAck(network, parent);
};
parent := none
}
}
}
}
*)

VARIABLES terminationDetected, network

sendMsg(net, from, to) == [net EXCEPT ![to].msg[from] = @+1]
pendingMsg(net, to, from) == net[to].msg[from] > 0
receiveMsg(net, to, from) == [net EXCEPT ![to].msg[from] = @-1]
sendAck(net, to) == [net EXCEPT ![to].ack = @+1]
pendingAck(net, to) == net[to].ack > 0
receiveAck(net, to) == [net EXCEPT ![to].ack = @-1]

VARIABLES active, parent, activeSons

vars == << terminationDetected, network, active, parent, activeSons >>

ProcSet == (Node)

Init ==
/\ terminationDetected = FALSE
/\ network = [n \in Node |-> [msg |-> [snd \in Node |-> 0], ack |-> 0]]

/\ active = [self \in Node |-> (self = initiator)]
/\ parent = [self \in Node |-> IF self = initiator THEN self ELSE none]
/\ activeSons = [self \in Node |-> 0]

node(self) == \/ /\ active[self]
/\ \E dst \in Node \ {self}:
network' = sendMsg(network, self, dst)
/\ activeSons' = [activeSons EXCEPT ![self] = activeSons[self] + 1]
/\ UNCHANGED <<terminationDetected, active, parent>>
\/ /\ active[self]
/\ active' = [active EXCEPT ![self] = FALSE]
/\ UNCHANGED <<terminationDetected, network, parent, activeSons>>
\/ /\ \E snd \in Node:
/\ pendingMsg(network, self, snd)
/\ active' = [active EXCEPT ![self] = TRUE]
/\ LET net == receiveMsg(network, self, snd) IN
IF parent[self] = none
THEN /\ parent' = [parent EXCEPT ![self] = snd]
/\ network' = net
ELSE /\ network' = sendAck(net, snd)
/\ UNCHANGED parent
/\ UNCHANGED <<terminationDetected, activeSons>>
\/ /\ pendingAck(network, self)
/\ network' = receiveAck(network, self)
/\ activeSons' = [activeSons EXCEPT ![self] = activeSons[self] - 1]
/\ UNCHANGED <<terminationDetected, active, parent>>
\/ /\ (~active[self] /\ activeSons[self] = 0 /\ parent[self] # none)
/\ IF parent[self] = self
THEN /\ terminationDetected' = TRUE
/\ UNCHANGED network
ELSE /\ network' = sendAck(network, parent[self])
/\ UNCHANGED terminationDetected
/\ parent' = [parent EXCEPT ![self] = none]
/\ UNCHANGED <<active, activeSons>>

Next == (\E self \in Node: node(self))

Spec == /\ Init /\ [][Next]_vars
/\ \A self \in Node : WF_vars(node(self))

StateConstraint ==
/\ \A n \in Node : network[n].ack <= 2
/\ \A m,n \in Node : network[m].msg[n] <= maxMsg

TypeOK ==
/\ terminationDetected \in BOOLEAN
/\ network \in [Node -> [msg : [Node -> Nat], ack : Nat]]
/\ active \in [Node -> BOOLEAN]
/\ parent \in [Node -> Node \union {none}]
/\ activeSons \in [Node -> Nat]

Quiescence ==
/\ \A n \in Node : ~active[n]
/\ \A n \in Node : network[n].ack = 0
/\ \A m,n \in Node : network[n].msg[m] = 0

TerminationDetection == terminationDetected => Quiescence

Liveness == Quiescence ~> terminationDetected

=============================================================================
