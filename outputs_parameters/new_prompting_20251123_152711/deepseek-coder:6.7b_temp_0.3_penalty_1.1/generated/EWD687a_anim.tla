---- MODULE EWD687a_anim ----
EXTENDS FiniteSets, Naturals, Sequences

CONSTANTS L = L, P1 = P1, P2 = P2, P3 = P3, P4 = P4, P5 = P5

VARIABLES Procs <- {L, P1, P2, P3, P4, P5}

CONSTANT Edges == LET Edgs == SUBSET [ n \in (Procs \X Procs): n[1] # n[2]] IN TLCEval(RandomElement(Edgs))

ASSUME PrintT(<<"Edges", Edges>>)

OPERATIONS
  -- Operations go here.

INVARIANTS
  TypeOK == \A x, y: Procs /\ [x] = [y] -> (x = y)
  DT1Inv == \E x: Procs /\ Active(x) -> (x != Leader)
  InterestingBehavior == \A x: Procs /\ (#Msgs(x) > 0) -> (~Neutral(x))

PROPERTIES
  DT2 == -- Property goes here.

ALIASES
  Alias == -- Aliases go here.

CHECK_DEADLOCK == FALSE

ACTION_CONSTRAINT NoSuperfluousIdleSteps == \A x: Procs /\ (Active(x) -> ~Change[x])

SPECIFICATION Spec == -- Your specification goes here.
====