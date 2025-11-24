---- MODULE EWD687a_anim ----


(* Defines operators on finite zero-indexed sequences, where a sequence of 
length n is represented as a function whose domain is the set 0..(n-1)  
(the set {0, 1, 2, ..., n-1}).                                            
*)

EXTENDS ZSequences

CONSTANTS
    L = <<"L">>
    P1 = <<"P1">>
    P2 = <<"P2">>
    P3 = <<"P3">>
    P4 = <<"P4">>
    P5 = <<"P5">>

CONSTANT
    NodesOfNetwork == {L, P1, P2, P3, P4, P5}

CONSTANT
    Network ==
    LET Edges == SUBSET [ n \in (NodesOfNetwork \X NodesOfNetwork) :
        (* No self-loops. *)
        n[1] # n[2]
        (* L is a source and never a sink. *)
        n[2] # L 
    ]
    IN TLCEval(RandomElement(Edges))

CONSTANT
    Procs == NodesOfNetwork

CONSTANT
    Leader == L

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