---- MODULE EWD998ChanID_export ----

(*******************************************************************************)
(* Each node maintains a (local) vector clock                                    *)
(* https://en.wikipedia.org/wiki/Vector_clock                                   *)
(*******************************************************************************)

CONSTANTS   Node,            \* The set of all nodes.
            Init  <- MCInit  \* Fewer initial states to speed-up startup.

VARIABLES   Clock            <\* Vector clock for each node *>

Assumptions == <\* Some assumptions about the system *>
    /\ <<Node>> \in SUBSET [0 .. Infinity]
    
Init 1==                         \* Initial state predicate.
    /\ Clock = [n |-> 0 : n \in Node]  

Next ==                           \* Next-state relation.
    \[Clock' = IF n = X THEN Clock[n] + 1 ELSE Clock[n] : n \in Node\]

Spec 2==                          \* Specification.
    Init /\ []A(Clock)

PostInv ==                        \* Post-condition invariant.
    \[EXISTS m . Clock[m] = Max {Clock[n] : n \in Node} \]

JsonInv ==                       \* Json format invariant.
    \[JSON(Clock) IS STRUCTURED AS \{"node": string, "clock": int\}^Node\]

TLC Configuration:
CONSTANTS 
    Node = {"n1","n2","n3","n4","n5","n6","n7"}
    Init <- MCInit * Fewer initial states to speed-up startup.
SPECIFICATION 
    Spec
INVARIANT 
    PostInv
    JsonInv
CHECK_DEADLOCK 
    FALSE
===============================================================================
====