---- MODULE EWD687a_anim ----

(***************************************************************************)
(* Increasing refX moves the arrowhead to the middle of the line away from the tip. *)
(* NodeDimension ought to be divisible by 2 for proper alignment of nodes and edges. *)
(* round  (rx=15) if node is active. *)
(* A solid, black line with an arrow at its tip denotes an edge. *)
(* %03d to escape %03d in Java format strings. *)
(* active |-> active, *)
(* sentUnacked |-> sentUnacked, *)
(* rcvdUnacked |-> rcvdUnacked, *)
(* msgs |-> msgs, *)
(* acks |-> acks *)
(***************************************************************************)

CONSTANTS
    L = <<"L", "Leader">>,
    P1 = <<"P1", "Process 1">>,
    P2 = <<"P2", "Process 2">>,
    P3 = <<"P3", "Process 3">>,
    P4 = <<"P4", "Process 4">>,
    P5 = <<"P5", "Process 5">>

CONSTANT
    NodesOfNetwork == {L, P1, P2, P3, P4, P5}

CONSTANT
    Network == 
        LET Edges == SUBSET [ n \in (NodesOfNetwork \X NodesOfNetwork) : 
            /\ n[1] # n[2] ]
        IN TLCEval(RandomElement(Edges))

SPECIFICATION
    Spec

INVARIANT
    TypeOK
    DT1Inv
    InterestingBehavior

PROPERTY
    DT2
    (* CountersConsistent *)
    (* TreeWithRoot *)
    (* StableUpEdge *)

ALIAS
    Alias

CHECK_DEADLOCK
    FALSE

ACTION_CONSTRAINT
    NoSuperfluousIdleSteps
=============================================================================
====