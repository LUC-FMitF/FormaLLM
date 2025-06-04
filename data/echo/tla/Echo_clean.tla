-------------------------------- MODULE Echo --------------------------------

EXTENDS Naturals, FiniteSets, Relation, TLC

CONSTANTS Node,
initiator,
R

ASSUME /\ initiator \in Node
/\ R \in [Node \X Node -> BOOLEAN]

/\ IsIrreflexive(R, Node)

/\ IsSymmetric(R, Node)

/\ IsConnected(R, Node)

NoNode == CHOOSE x : x \notin Node
neighbors(n) == { m \in Node : R[m,n] }

VARIABLES inbox, pc

send(net, p, q, knd) == [net EXCEPT ![q] = @ \cup {[kind |-> knd, sndr |-> p]}]

receive(net, p, msg) == [net EXCEPT ![p] = @ \ {msg}]

multicast(net, p, dest, knd) ==
[m \in Node |-> IF m \in dest THEN net[m] \cup {[kind |-> knd, sndr |-> p]}
ELSE net[m]]

VARIABLES parent, children, rcvd, nbrs

vars == << inbox, pc, parent, children, rcvd, nbrs >>

ProcSet == (Node)

Init ==
/\ inbox = [n \in Node |-> {}]

/\ parent = [self \in Node |-> NoNode]
/\ children = [self \in Node |-> {}]
/\ rcvd = [self \in Node |-> 0]
/\ nbrs = [self \in Node |-> neighbors(self)]
/\ pc = [self \in ProcSet |-> "n0"]

n0(self) == /\ pc[self] = "n0"
/\ IF self = initiator
THEN /\ inbox' = multicast(inbox, self, nbrs[self], "m")
ELSE /\ TRUE
/\ inbox' = inbox
/\ pc' = [pc EXCEPT ![self] = "n1"]
/\ UNCHANGED << parent, children, rcvd, nbrs >>

n1(self) == /\ pc[self] = "n1"
/\ IF rcvd[self] < Cardinality(nbrs[self])
THEN /\ \E msg \in inbox[self]:
LET net == receive(inbox, self, msg) IN
/\ rcvd' = [rcvd EXCEPT ![self] = rcvd[self]+1]
/\ IF self # initiator /\ rcvd'[self] = 1
THEN /\ Assert((msg.kind = "m"),
"Failure of assertion at line 55, column 16.")
/\ parent' = [parent EXCEPT ![self] = msg.sndr]
/\ inbox' = multicast(net, self, nbrs[self] \ {msg.sndr}, "m")
ELSE /\ inbox' = net
/\ UNCHANGED parent
/\ IF msg.kind = "c"
THEN /\ children' = [children EXCEPT ![self] = children[self] \cup {msg.sndr}]
ELSE /\ TRUE
/\ UNCHANGED children
/\ pc' = [pc EXCEPT ![self] = "n1"]
ELSE /\ pc' = [pc EXCEPT ![self] = "n2"]
/\ UNCHANGED << inbox, parent, children, rcvd >>
/\ nbrs' = nbrs

n2(self) == /\ pc[self] = "n2"
/\ IF self # initiator
THEN /\ Assert((parent[self] \in nbrs[self]),
"Failure of assertion at line 70, column 10.")
/\ inbox' = send(inbox, self, parent[self], "c")
ELSE /\ TRUE
/\ inbox' = inbox
/\ pc' = [pc EXCEPT ![self] = "Done"]
/\ UNCHANGED << parent, children, rcvd, nbrs >>

node(self) == n0(self) \/ n1(self) \/ n2(self)

Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
/\ UNCHANGED vars

Next == (\E self \in Node: node(self))
\/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

TypeOK ==
/\ parent \in [Node -> (Node \cup {NoNode})]
/\ children \in [Node -> SUBSET Node]
/\ rcvd \in [Node -> Nat]
/\ nbrs \in [Node -> SUBSET Node]
/\ \A n \in Node : nbrs[n] = neighbors(n) /\ rcvd[n] <= Cardinality(nbrs[n])
/\ inbox \in [Node -> SUBSET [kind : {"m","c"}, sndr : Node]]
/\ \A n \in Node : \A msg \in inbox[n] : msg.sndr \in nbrs[n]

InitiatorNoParent == parent[initiator] = NoNode

ParentIsNeighbor == \A n \in Node : parent[n] \in neighbors(n) \cup {NoNode}

ParentChild == \A m,n \in Node :
/\ n \in children[m] => m = parent[n]
/\ m = parent[n] /\ pc[m] = "Done" => n \in children[m]

IsParent == [m,n \in Node |-> n = parent[m]]
IsAncestor == TransitiveClosure(IsParent, Node)

AncestorProperties ==
(\A n \in Node : pc[n] = "Done")
=> LET anc == IsAncestor
IN  /\ \A n \in Node \ {initiator} : anc[n, initiator]
/\ IsIrreflexive(anc, Node)

=============================================================================
