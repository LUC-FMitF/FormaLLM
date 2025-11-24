---- MODULE MCDieHarder ----

(**************************************************************************)
(* The following definitions duplicate the original Die Hard problem.     *)
(**************************************************************************)

CONSTANTS Goal     \* The goal of the game is to move all the money      *)
                  \* from the safe to the bank.                           *)
    == 4

Jug      \* The amount of money in the jug.                               *)
    <- MCJug

Capacity \* The maximum amount of money that can be held in the jug.     *)
    <- MCCapacity

MCJug(j) ==
  IF j = 0
  THEN 0
  ELSE 1 + MCJug(j - 1)

MCCapacity(c) ==
  IF c = 0
  THEN 0
  ELSE 1 + MCCapacity(c - 1)

Spec == \* The specification of the game.                                *)
    Init /\ [][Next]_<<Goal, Jug, Capacity>>

Init == \* The initial state of the game.                                *)
    Goal = 4 /\ Jug = 0 /\ Capacity = 16

Next == \* The next-state relation of the game.                          *)
    [
      \* If the goal is not yet achieved, move money from the safe to   *)
      \* the jug.                                                        *)
      Goal > 0 /\ Jug < Capacity /\
      NextJug = Jug + 1 /\ NextCapacity = Capacity - 1 /\
      NextGoal = Goal - 1
    ]
    [
      \* If the goal is achieved, move money from the jug to the bank.   *)
      Goal = 0 /\ Jug > 0 /\
      NextJug = Jug - 1 /\ NextCapacity = Capacity /\
      NextGoal = Goal + 1
    ]

Invariants == \* The type invariant of the game.                         *)
    [](
      \A i \in DOMAIN Next : Next[i].Jug <= Next[i].Capacity
      /\ Next[i].Goal >= 0
      /\ Next[i].Jug >= 0
      /\ Next[i].Capacity >= 0
    )

NotSolved == \* The invariant that the game is not yet solved. *)
    [](NextGoal > 0)

TypeOK == \* The type invariant of the game.                     *)
    [](
      \A i \in DOMAIN Next : Next[i].Jug <= Next[i].Capacity
      /\ Next[i].Goal >= 0
      /\ Next[i].Jug >= 0
      /\ Next[i].Capacity >= 0
    )

=============================================================================
====