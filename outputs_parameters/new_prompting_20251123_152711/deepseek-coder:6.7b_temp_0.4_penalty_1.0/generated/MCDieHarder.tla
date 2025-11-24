---- MODULE MCDieHarder ----


EXTENDS ModuleDieHarder

CONSTANTS Goal     <- 4

FUNCTION MCCapacity ==
  CASE Jug = 1 -> 2
  [] Jug = 2 -> 3
  [] Jug = 3 -> 4
  [] Jug = 4 -> 5
  [] OTHER -> UNDEF

FUNCTION MCJug ==
  CASE Capacity = 2 -> 1
  [] Capacity = 3 -> 2
  [] Capacity = 4 -> 3
  [] Capacity = 5 -> 4
  [] OTHER -> UNDEF

=============================================================================
====


CONSTANTS Jug, Capacity, Goal

VARIABLES X, Y, Z

Next ==
  (X' = [X EXCEPT 1] U {Goal}, Y' = [Y EXCEPT 1] U {Goal}, Z' = [Z EXCEPT 1] U {Goal})
  /\ X \in 1..Capacity
  /\ Y \in 1..Capacity
  /\ Z \in 1..Capacity
  /\ X + Y + Z = Capacity
  /\ X \neq Y
  /\ Y \neq Z
  /\ X \neq Z

Spec == Init /\ [](Next)

INVARIANT TypeOK == Jug IN {1, 2, 3, 4} /\ Capacity IN {2, 3, 4, 5}

NOTSOLVED == X + Y + Z \neq Capacity

=============================================================================
====

TLC Configuration:

CONSTANTS Goal     = 4
          Jug      <- MCJug
          Capacity <- MCCapacity 

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved
====