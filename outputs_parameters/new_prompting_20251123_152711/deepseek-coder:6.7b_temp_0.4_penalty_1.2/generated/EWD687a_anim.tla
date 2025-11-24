---- MODULE EWD687a_anim ----
EXTENDS FiniteSets, Naturals, Sequences, ZSequences

CONSTANTS 
    L = <<L>>,
    P1 = <<P1>>,
    P2 = <<P2>>,
    P3 = <<P3>>,
    P4 = <<P4>>,
    P5 = <<P5>>

VARIABLES
    Procs == {L, P1, P2, P3, P4, P5},
    Edges == LET Edgs == SUBSET { n \in (Procs \X Procs): n[1] # n[2] } IN TLCEval(RandomElement(Edgs))

ASSUME PrintT(<<"Edges", Edges>>)

OPERATIONS
    Spec == ... (* Your specification goes here *)

INVARIANT 
    TypeOK,
    DT1Inv == ... (* Your first invariant definition goes here *),
    InterestingBehavior == ... (* A definition of an interesting behavior goes here *)

PROPERTY 
    DT2 == ... (* Definition for property DT2 goes here *)
    (* CountersConsistent, TreeWithRoot, StableUpEdge definitions go here *)

ALIAS
    Alias == ... (* Your alias definition goes here *)

CHECK_DEADLOCK FALSE

ACTION_CONSTRAINT 
    NoSuperfluousIdleSteps(Procs) == 
        \E a, b : Procs /\ a ~> b => (State[a].active = State[b].active)
====