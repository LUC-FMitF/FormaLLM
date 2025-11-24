---- MODULE EWD998ChanID_export ----
EXTENDS TLC

CONSTANTS
    Node = {n1,n2,n3,n4,n5,n6,n7}

VARIABLES
    Clock[Node]

ASSUME
    Init == [n \in Node |-> IF n = n1 THEN 0 ELSE 1]

NEXT
    Tick == [n \in Node |-> IF n = n1 THEN Clock[n] ELSE Clock[n] + 1]

INVARIANT
    JsonInv == \* A read-world invariant.
        \A n \in Node : Clock[n] >= 0
    PostInv == \* A post-condition invariant.
        \A n \in Node : Clock[n] >= 0

SPECIFICATION
    Spec == [](\A n \in Node : Clock[n] >= 0)

TLC_CONFIG
    CONSTANTS
        Node = {n1,n2,n3,n4,n5,n6,n7}
        Init <- Init
    SPECIFICATION
        Spec
    INVARIANT
        JsonInv
        PostInv
    CHECK_DEADLOCK
        FALSE
    ERROR_TRACE
        TRACE_JSON
        TRACE_FILE("error_trace.json")
        TRACE_PING("https://your-webhook-url")
=============================================================================
====