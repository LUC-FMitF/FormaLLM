---- MODULE MCDieHarder ----


EXTENDS DieHarder

\* The maximum capacity of the jug
FUNCTION MCCapacity ==
  IF Jug = 0
  THEN 0
  ELSE Capacity

\* The maximum volume of the jug
FUNCTION MCJug ==
  IF Capacity = 0
  THEN 0
  ELSE Jug

=============================================================================
====


CONSTANTS Jug, Capacity, Goal

VARIABLES X, Y, Z, A, B, C

\* Specification of the problem
Spec ==
  [] Init
  [] [](A = X + Y  /\  B = X + Z  /\  C = Y + Z)
  [] [](X, Y, Z >= 0  /\  A =< Goal  /\  B =< Goal  /\  C =< Goal)
  [] [](X = 0  /\  Y = Jug  /\  Z = Capacity)
  [] [](X' = Y  /\  Y' = (X + Y) MOD (Jug + Capacity)  /\  Z' = C)
  [] [](A' = B  /\  B' = (A + B) MOD (Goal + Goal)  /\  C' = (B + C) MOD (Goal + Goal))

\* Well-formedness invariant
NotSolved ==
  [] (X, Y, Z, A, B, C >= 0)

\* Initial state
Init ==
  [] X = 0  /\  Y = Jug  /\  Z = Capacity  /\  A = 0  /\  B = 0  /\  C = 0

=============================================================================
====

---- TLC Configuration ----
------------------------------ TLC Configuration ----------------------------

CONSTANTS Goal = <desired_goal_value>
          Jug = MCCapacity - 1  // Adjust Jug value to be one less than the Capacity
          Capacity = MCCapacity

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved
====