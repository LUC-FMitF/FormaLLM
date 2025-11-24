---- MODULE EWD998ChanID_export ----
EXTENDS TLC

CONSTANTS
    Node = {n1,n2,n3,n4,n5,n6,n7}

VARIABLES
    VectorClock[Node]

ASSUME
    Init == [n \in Node |-> {0}]

NEXT
    VectorClock'[n] ==
        IF n \in Node
        THEN VectorClock[n] \ {n} U {Max(VectorClock[n] \ {n}) + 1}
        ELSE UNCHANGED VectorClock[n]

INVARIANT
    PostInv == [n \in Node |-> VectorClock[n] \ {n} = UNCHANGED VectorClock[n]]

SPECIFICATION
    Spec == [n \in Node |-> VectorClock[n] \ {n} = UNCHANGED VectorClock[n]]

TLC_CONFIG
    CONSTANTS
        Node = {n1,n2,n3,n4,n5,n6,n7}
    SPECIFICATION
        Spec
    INVARIANT
        PostInv
    CHECK_DEADLOCK
        FALSE
====