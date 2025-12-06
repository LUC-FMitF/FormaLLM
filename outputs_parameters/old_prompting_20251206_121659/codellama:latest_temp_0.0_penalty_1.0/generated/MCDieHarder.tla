---- MODULE MCDieHarder ----

(**************************************************************************)
(* The following definitions duplicate the original Die Hard problem.     *)
(**************************************************************************)

CONSTANTS Goal     =  4
          Jug      <- 3
          Capacity <- 5

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

Spec ==
  Init /\ [][Next]_<<Goal, Jug, Capacity>>

TypeOK ==
  /\ Goal \in 0..4
  /\ Jug \in 0..4
  /\ Capacity \in 0..4

NotSolved ==
  /\ Goal > 0
  /\ Jug > 0
  /\ Capacity > 0
  /\ Goal > Jug
  /\ Goal > Capacity

Next ==
  \/ \E Goal' \in 0..4 : Goal' = Goal - 1
  \/ \E Jug' \in 0..4 : Jug' = Jug - 1
  \/ \E Capacity' \in 0..4 : Capacity' = Capacity - 1
  \/ \E Goal' \in 0..4 : Goal' = Goal - 1 /\ Jug' = Jug - 1
  \/ \E Goal' \in 0..4 : Goal' = Goal - 1 /\ Capacity' = Capacity - 1
  \/ \E Jug' \in 0..4 : Jug' = Jug - 1 /\ Capacity' = Capacity - 1
  \/ \E Goal' \in 0..4 : Goal' = Goal - 1 /\ Jug' = Jug - 1 /\ Capacity' = Capacity - 1

=============================================================================
====