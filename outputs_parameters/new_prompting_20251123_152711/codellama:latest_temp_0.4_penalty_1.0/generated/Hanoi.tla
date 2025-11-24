---- MODULE Hanoi ----

(***************************************************************************)
(* Defines a Tower of Hanoi puzzle with N towers, where each tower can   *)
hold up to D disks.                                                      *)
(***************************************************************************)

CONSTANTS
  D \* The maximum number of disks on any single tower.
  N \* The total number of towers in the puzzle.
VARIABLES
  bigTower, smallTower \* The two towers involved in the game (big and    *)
                      * small).                                          *)
  disk1 .. D           \* A set of all disks on the first tower.         *)
  disk2 .. D           \* A set of all disks on the second tower.        *)
  ...                  \* A set of all disks on the Nth tower.            *)
  notSmall             \* The set of all towers that are not the small   *)
                      * one (big and other).                              *)
  rightTower           \* The number of disks on the right tower.        *)
  leftTower            \* The number of disks on the left tower.         *)
  middleTower          \* The number of disks on the middle tower.   *)
  notSolved           \* An invariant that ensures a solution  *)
                      * exists (see below).                       *)
LOCAL Instance FiniteSets
LOCAL Instance Naturals
LOCAL Instance Sequences

\* The initial configuration of the puzzle.                     *)
Init ==
  bigTower = ZSeq(1 .. D) & smallTower = {} & disk1..D \in {0, 1} &
              notSmall = {bigTower, smallTower} & rightTower = 0 &
              leftTower = 0 & middleTower = 0 & notSolved = TRUE

\* The next configuration of the puzzle.                         *)
Next ==
  IF (rightTower < D) \/ (leftTower > 0) \/ (middleTower > 0) THEN
    [big, small] \in {(1..D), ()} & big = {} ->
      rightTower' = rightTower + 1 & leftTower' = leftTower - 1 &
                     middleTower' = middleTower + 1 & disk1..D' =
                       [disk |-> IF disk \in notSmall THEN big ELSE small]
    [] (big, small) -> rightTower' = rightTower - 1 & leftTower' =
      leftTower + 1 & middleTower' = middleTower - 1 & disk1..D' = [disk |-> IF disk \in notSmall THEN big ELSE small]
    [] (big, small) -> rightTower' = rightTower & leftTower' = leftTower &
                        middleTower' = middleTower & disk1..D' = [disk |-> IF disk \in notSmall THEN big ELSE small]
  ELSE FALSE

\* The final configuration of the puzzle.                         *)
Final == rightTower # 2^N - 1

\* An invariant that ensures a solution exists (see below).        *)
notSolved == Final \/ TRUE

=============================================================================
====