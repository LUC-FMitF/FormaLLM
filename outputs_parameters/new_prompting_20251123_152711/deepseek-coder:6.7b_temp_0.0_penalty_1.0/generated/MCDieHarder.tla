---- MODULE MCDieHarder ----


EXTENDS ModuleDieHarder

CONSTANTS Goal     = \* The goal amount of liquid
         Jug      <- MCJug     \* The capacity of the jug
         Capacity <- MCCapacity  \* The capacity of the jug

SPECIFICATION Spec

INVARIANTS TypeOK NotSoloved

=============================================================================
====


CONSTANTS Jug, Capacity, Goal

VARIABLES Jugs

Init ==
  /\ Jugs = [0 .. Jug-1 -> False]
  /\ UNCHANGED <<Goal>>

NextState ==
  /\ Jugs'[i] = IF Jugs[i] THEN False ELSE True
  /\ UNCHANGED <<Goal, Jugs>>

Spec == Init /\ [](NextState)

INVARIANTS TypeOK ==
  /\ Jug \in Nat
  /\ Capacity \in Nat
  /\ Goal \in Nat
  /\ Jugs \subseteq {True, False}
  /\ Cardinality(Jugs) = Capacity

THEOREM NotSolved == ~[](Solved)

=============================================================================
====


CONSTANTS Jug, Capacity, Goal

VARIABLES Jugs

Init ==
  /\ Jugs = [0 .. Jug-1 -> False]
  /\ UNCHANGED <<Goal>>

NextState ==
  /\ Jugs'[i] = IF Jugs[i] THEN False ELSE True
  /\ UNCHANGED <<Goal, Jugs>>

Spec == Init /\ [](NextState)

INVARIANTS TypeOK ==
  /\ Jug \in Nat
  /\ Capacity \in Nat
  /\ Goal \in Nat
  /\ Jugs \subseteq {True, False}
  /\ Cardinality(Jugs) = Capacity

THEOREM NotSolved == ~[](Solved)

=============================================================================
====


CONSTANTS Goal     = \* The goal amount of liquid
         Jug      <- MCJug     \* The capacity of the jug
         Capacity <- MCCapacity  \* The capacity of the jug

SPECIFICATION Spec

INVARIANTS TypeOK NotSoloved

=============================================================================
====


CONSTANTS Jug, Capacity, Goal

VARIABLES Jugs

Init ==
  /\ Jugs = [0 .. Jug-1 -> False]
  /\ UNCHANGED <<Goal>>

NextState ==
  /\ Jugs'[i] = IF Jugs[i] THEN False ELSE True
  /\ UNCHANGED <<Goal, Jugs>>

Spec == Init /\ [](NextState)

INVARIANTS TypeOK ==
  /\ Jug \in Nat
  /\ Capacity \in Nat
  /\ Goal \in Nat
  /\ Jugs \subseteq {True, False}
  /\ Cardinality(Jugs) = Capacity

THEOREM NotSolved == ~[](Solved)

=============================================================================
====