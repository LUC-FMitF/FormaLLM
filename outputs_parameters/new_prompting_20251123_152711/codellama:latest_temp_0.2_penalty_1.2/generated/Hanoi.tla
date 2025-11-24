---- MODULE Hanoi ----

(**************************************************************************)
(* Towers of Hanoi with N towers                                          *)
(**************************************************************************)

CONSTANTS
  D, N,                      \* Number of disks and towers.
  big, small,               \* Names of the big and small towers.
  disk,                     \* Name of the disk.
  NotSolved,                \* Invariant that the puzzle is not solved.
  rightTower                 \* Invariant that all disks are on the right tower.

VARIABLES
  tower[big, small, disk],   \* The current configuration of the towers.
  moves                      \* The sequence of moves performed.

----------------------------------------------------------------------------
NoVal ==    \* Choose something to represent the absence of a value.
    CHOOSE v : v \notin Val

Tower ==    \* The set of all towers.
    [big, small, disk \union {NoVal}]

Init == \* The initial predicate.
    /\ tower[big, small, disk] = [
        big   = [0 .. (D - 1)],
        small = [D .. (2 * D - 1)],
        disk = [0 .. (D - 1)]
    ]
    /\ moves = <<>>

Next == \* The transition relation.
    [
        tower[big, small, disk]' = tower[big, small, disk],
        moves' = moves \union {[
            big   = tower[big, small, disk][big],
            small = tower[big, small, disk][small],
            disk = tower[big, small, disk][disk]
        ]}
    ]
    /\ tower[big, small, disk]' =
        [
            big   = [0 .. (D - 1)],
            small = [D .. (2 * D - 1)],
            disk = [0 .. (D - 1)]
        ]
    /\ moves' =
        [
            big   = tower[big, small, disk][big],
            small = tower[big, small, disk][small],
            disk = tower[big, small, disk][disk]
        ]

NotSolved == \* Invariant that the puzzle is not solved.
    /\ tower[big, small, disk]' = tower[big, small, disk]
    \/ moves' = moves

rightTower == \* Invariant that all disks are on the right tower.
    /\ tower[big, small, disk]' = tower[big, small, disk]
    \/ moves' = moves

=============================================================================
====