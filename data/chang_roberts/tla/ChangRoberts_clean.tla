---------------------------- MODULE ChangRoberts ----------------------------

EXTENDS Naturals, Sequences

CONSTANTS N, Id

Node == 1 .. N

ASSUME
/\ N \in Nat \ {0}
/\ Id \in Seq(Nat)
/\ Len(Id) = N
/\ \A m,n \in Node : m # n => Id[m] # Id[n]

succ(n) == IF n=N THEN 1 ELSE n+1

variable msgs = [n \in Node |-> {}];
fair process (node \in Node)
variables

initiator \in BOOLEAN,
state = IF initiator THEN "cand" ELSE "lost";
{

n0: if (initiator) {
msgs[succ(self)] := @ \cup {Id[self]}
};
n1: while (TRUE) {

with (id \in msgs[self],
_msgs = [msgs EXCEPT ![self] = @ \ {id}]) {
if (state = "lost") {
msgs := [_msgs EXCEPT ![succ(self)] = @ \cup {id}]
} else if (id < Id[self]) {

state := "lost";
msgs := [_msgs EXCEPT ![succ(self)] = @ \cup {id}]
} else {

msgs := _msgs;
if (id = Id[self]) { state := "won" }
}
}
}
}
}
**)

VARIABLES msgs, pc, initiator, state

vars == << msgs, pc, initiator, state >>

ProcSet == (Node)

Init ==
/\ msgs = [n \in Node |-> {}]

/\ initiator \in [Node -> BOOLEAN]
/\ state = [self \in Node |-> IF initiator[self] THEN "cand" ELSE "lost"]
/\ pc = [self \in ProcSet |-> "n0"]

n0(self) == /\ pc[self] = "n0"
/\ IF initiator[self]
THEN /\ msgs' = [msgs EXCEPT ![succ(self)] = @ \cup {Id[self]}]
ELSE /\ TRUE
/\ msgs' = msgs
/\ pc' = [pc EXCEPT ![self] = "n1"]
/\ UNCHANGED << initiator, state >>

n1(self) == /\ pc[self] = "n1"
/\ \E id \in msgs[self]:
LET _msgs == [msgs EXCEPT ![self] = @ \ {id}] IN
IF state[self] = "lost"
THEN /\ msgs' = [_msgs EXCEPT ![succ(self)] = @ \cup {id}]
/\ state' = state
ELSE /\ IF id < Id[self]
THEN /\ state' = [state EXCEPT ![self] = "lost"]
/\ msgs' = [_msgs EXCEPT ![succ(self)] = @ \cup {id}]
ELSE /\ msgs' = _msgs
/\ IF id = Id[self]
THEN /\ state' = [state EXCEPT ![self] = "won"]
ELSE /\ TRUE
/\ state' = state
/\ pc' = [pc EXCEPT ![self] = "n1"]
/\ UNCHANGED initiator

node(self) == n0(self) \/ n1(self)

Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
/\ UNCHANGED vars

Next == (\E self \in Node: node(self))
\/ Terminating

Spec == /\ Init /\ [][Next]_vars
/\ \A self \in Node : WF_vars(node(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

-----------------------------------------------------------------------------

TypeOK ==
/\ pc \in [Node -> {"n0", "n1", "Done"}]
/\ msgs \in [Node -> SUBSET {Id[n] : n \in Node}]
/\ initiator \in [Node -> BOOLEAN]
/\ state \in [Node -> {"cand", "lost", "won"}]

Correctness ==
\A n \in Node : state[n] = "won" =>
/\ initiator[n]
/\ \A m \in Node \ {n} :
/\ state[m] = "lost"
/\ initiator[m] => Id[m] > Id[n]

Liveness == (\E n \in Node : state[n] = "cand") => <>(\E n \in Node : state[n] = "won")
=============================================================================
