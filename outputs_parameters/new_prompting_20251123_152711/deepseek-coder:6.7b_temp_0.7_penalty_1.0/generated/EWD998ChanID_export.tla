---- MODULE EWD998ChanID_export ----
EXTENDS ModuleName

CONSTANTS Node = {n1,n2,n3,n4,n5,n6,n7}

VARIABLES
    VectorClock << Node -> NATURAL>>,
    TempVectorClock << Node -> NATURAL>>,
    Message << Node -> Node -> BOOLEAN>>

ASSIGN
    Init == \* Fewer initial states to speed-up startup.
        VectorClock = [n \in Node |-> 0]

NEXT
    [n \in Node |-> IF Message[n][m] THEN VectorClock'[m]' ELSE VectorClock'[m] = VectorClock[m]]

Spec == \* Termination detection
    /\ [n \in Node |-> VectorClock[n] > 0]

PostInv == \* Post-condition invariant
    /\ [n \in Node |-> VectorClock[n] = Sequence(VectorClock, n)]

THEOREM Spec => VectorClock = Init

====

TLC Configuration:

CONSTANTS
    Node = {n1,n2,n3,n4,n5,n6,n7}

SPECIFICATION
    Spec

INVARIANT
    PostInv

CHECK_DEADLOCK
    FALSE
====