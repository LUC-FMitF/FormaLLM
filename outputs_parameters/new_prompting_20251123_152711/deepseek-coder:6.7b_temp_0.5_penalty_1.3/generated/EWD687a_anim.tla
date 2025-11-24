---- MODULE EWD687a_anim ----

(***************************************************************************)
(* This module defines a set of operations on zero-indexed sequences,       *)
(* including operators for length, conversion between one- and zero-indexed   *)
(* sequences, lexicographic order, and rotation.                            *)
(***************************************************************************)

EXTENDS FiniteSets, Naturals, Sequences

CONSTANTS 
    L = {active, sentUnacked, rcvdUnacked, msgs, acks}
    P1 = {active, sentUnacked, rcvdUnacked, msgs, acks}
    P2 = {active, sentUnacked, rcvdUnacked, msgs, acks}
    P3 = {active, sentUnacked, rcvdUnacked, msgs, acks}
    P4 = {active, sentUnacked, rcvdUnacked, msgs, acks}
    P5 = {active, sentUnacked, rcvdUnacked, msgs, acks}

CONSTANT 
    Procs <- {L, P1, P2, P3, P4, P5}

CONSTANT 
    Edges <- LET Edgs == SUBSET { n \in (Procs \X Procs):
        /\ n[1] # n[2]
        /\ n[2] # L }
    IN TLCEval(RandomElement(Edgs))

SPECIFICATION Spec

INVARIANT TypeOK
    DT1Inv
    InterestingBehavior

PROPERTY 
    DT2
    CountersConsistent
    TreeWithRoot
    StableUpEdge

ALIAS Alias

CHECK_DEADLOCK FALSE

ACTION_CONSTRAINT NoSuperfluousIdleSteps(proc) == proc = Idle \/ (Next[proc] = Active /\ ProcState[Next[proc]] != Idle)

=============================================================================
====