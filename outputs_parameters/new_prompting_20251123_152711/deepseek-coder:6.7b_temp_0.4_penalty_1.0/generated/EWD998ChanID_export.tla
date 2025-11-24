---- MODULE EWD998ChanID_export ----
EXTENDS TLC

CONSTANTS
    Node = {n1,n2,n3,n4,n5,n6,n7}
    Init <- MCInit \* Fewer initial states to speed-up startup.

VARIABLES
    VectorClock[Node] <- [n \in Node |-> 0]

ASSUME
    Init \in State

NEXT
    VectorClockNext[n] ==
        IF \E m \in Node : m \neq n : VectorClock[m] > VectorClock[n]
        THEN VectorClock[n] + 1
        ELSE VectorClock[n]

SPECIFICATION
    Spec

INVARIANT
    JsonInv ==
        LET json <- {
            "nodes": [n \in Node |-> VectorClock[n]],
            "inv": "VectorClock[n] <= VectorClock[m] for all m \in Node"
        }
        IN json \in State

    PostInv ==
        LET N <- |Node|
        IN N <= 1 OR (VectorClock[Node] \in State)

CHECK_DEADLOCK
    FALSE

TLC_OPTIONS
    --deadlock-check=false
    --error-format=json
    --tlc-timeout=1000
    --output-format=json
    --output-file=error.json
    --ping-web-endpoint=http://example.com/errors

====