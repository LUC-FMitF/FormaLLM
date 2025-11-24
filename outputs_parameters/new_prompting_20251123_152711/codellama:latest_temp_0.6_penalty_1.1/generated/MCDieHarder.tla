---- MODULE MCDieHarder ----

(**************************************************************************)
(* The following definitions duplicate the original Die Hard problem.   *)
(**************************************************************************)

CONSTANTS Goal     \* The goal of the game.
    == 4

Jug      <- MCJug    \* The capacity of the jug.
Capacity <- MCCapacity    \* The capacity of the jug.

MCJug(n) ==
  IF n = 0
  THEN 0
  ELSE 1 + MCJug(n - 1)

MCCapacity(n) ==
  IF n = 0
  THEN 0
  ELSE 1 + MCCapacity(n - 1)
  
Spec == \* The specification.
    /\ Init /\ [][Next]_<<Jug, Goal>>

Init == \* The initial predicate.
    /\ Jug = 0      \* The jug is initially empty.
    /\ Goal = 4     \* The goal is to fill the jug with 4 gallons of water.

Next == \* The next-state relation.
    \/ \E g \in Goal : Fill(g)
    \/ \E j \in Jug : Empty(j)
    \/ \E j \in Jug : Pour(j, Goal - j)

Fill(g) == \* The goal has been filled.
    /\ g = 4
    /\ Goal' = 4

Empty(j) == \* The jug is empty.
    /\ j = 0
    /\ Jug' = 0

Pour(j, q) == \* Pour q gallons from the jug to the goal.
    /\ j + q <= Goal   \* The jug has enough water to pour.
    /\ j <= Goal       \* The goal has enough space for the water.
    /\ Jug' = j        \* The jug is unchanged.
    /\ Goal' = Goal - q \* The goal has q gallons less water.
=============================================================================
====