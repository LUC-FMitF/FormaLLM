---- MODULE EWD998ChanID_export ----

(***************************************************************************)
(* c properly initialized with empty channels.                             *)
(***************************************************************************)

CONSTANTS   Node,      \* The set of all nodes in the system.
            Init       \* Fewer initial states to speed-up startup.
VARIABLES   vc,        \* The vector clock for each node.
            chan      \* The channel between two nodes.
----------------------------------------------------------------------------
\* The simulator/generator may generate a prefix of a behavior whose length is
\* less than what we wish to see.
CHECK_DEADLOCK FALSE

Node == {n1, n2, n3, n4, n5, n6, n7}

Init == \* Fewer initial states to speed-up startup.
    /\ vc = [n \in Node |-> 0]
    /\ chan = [((n1, n2), {}) \/ (n2, n3) \/ (n3, n4) \/ (n4, n5) \/ (n5, n6) \/ (n6, n7)]
    
VectorClock == \* The vector clock for each node.
    [Node -> Nat]

Channel == \* The channel between two nodes.
    [((Node \* Node) -> SUBSET Node) -> SUBSET Node]
    
PostInv == \* Some read-world invariant (here terminationDetected occurs within N steps where N has been chosen arbitrarily).
    /\ \A t \in Nat : \A n \in Node : vc[n] <= t

JsonInv == \* Make TLC stop and print the usual error trace.
    /\ \A t \in Nat : \A n \in Node : vc[n] = t
    
TerminationDetected(t) == \* Make TLC stop and print the usual error trace.
    /\ \E n \in Node : vc[n] = t
    /\ \A n \in Node : vc[n] < t
    
VectorClockUpdate(vc, chan) == \* Update the vector clock for each node based on the channel between two nodes.
    [((Node \* Node) -> SUBSET Node) -> (Node -> Nat)]
    
Spec == \* Initialize state with Init and transition with VectorClockUpdate.
    Init /\ [](VectorClockUpdate(vc, chan))

INVARIANT JsonInv /\ PostInv
=============================================================================
====