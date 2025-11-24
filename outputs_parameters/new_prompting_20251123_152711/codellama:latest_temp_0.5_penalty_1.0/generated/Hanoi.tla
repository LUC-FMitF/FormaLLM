---- MODULE Hanoi ----

(***************************************************************************)
(*                                                                         *)
(*   Towers of Hanoi with N towers                                        *)
(*                                                                         *)
(*   The total sum of all towers must amount to the disks in the system  *)
(*                                                                         *)
(*   Towers are naturals in the interval (0, 2^D] *)
(*                                                                         *)
(*   The final configuration has all disks on the right tower. If TLC is  *)
(*   set to run with an invariant rightTower # 2^N-1, it will search for  *)
(*   configurations in which this invariant is violated. If violation can  *)
(*   be found, the stack trace shows the steps to solve the Hanoi         *)
(*   problem.                                                              *)
(*                                                                         *)
(*   The minimum number of moves required to solve a Tower of Hanoi       *)
(*   puzzle generally is 2n-1, where n is the number of disks. Thus, the  *)
(*   counter-examples shown by TLC will be of length 2n-1                  *)
(*                                                                         *)
(***************************************************************************)

LOCAL Instance FiniteSets
LOCAL Instance Naturals

CONSTANT N = 3
CONSTANT D = 3
CONSTANT RIGHT_TOWER = 2^N - 1
CONSTANT LEFT_TOWER = 2^N - 2
CONSTANT MIDDLE_TOWER = 2^N - 3

VARIABLES
  big, small

CONSTANTS
  EmptyTower = <<>>
  TowerOfDisks = [
    big  |-> [D .. D],
    small |-> [1 .. 1]
  ]

INITIAL
  Init ==
    (big = EmptyTower) /\
    (small = EmptyTower) /\
    (TowerOfDisks = [[D .. D], [1 .. 1]])

NEXT
  Next ==
    (big = small)   /\
    (small = TowerOfDisks)   /\
    (TowerOfDisks = [[D .. D], [1 .. 1]])

NEXT
  Move ==
    (big = small)   /\
    (small = TowerOfDisks)   /\
    (TowerOfDisks = [[D .. D], [1 .. 1]])

NEXT
  NotSolved ==
    (big = EmptyTower) /\
    (small = EmptyTower) /\
    (TowerOfDisks = [[D .. D], [1 .. 1]])

INVARIANT
  Inv ==
    (big # 2^N-1) /\
    (small # 2^N-1) /\
    (TowerOfDisks # 2^N-1) /\
    (big = RIGHT_TOWER) /\
    (small = LEFT_TOWER) /\
    (MIDDLE_TOWER # big) /\
    (MIDDLE_TOWER # small)

\*
  The final configuration has all disks on the right tower. If TLC is set to run with an invariant rightTower # 2^N-1, it will search for configurations in which this invariant is violated. If violation can be found, the stack trace shows the steps to solve the Hanoi problem.
  The minimum number of moves required to solve a Tower of Hanoi puzzle generally is 2n-1, where n is the number of disks. Thus, the counter-examples shown by TLC will be of length 2n-1
*

=============================================================================
====