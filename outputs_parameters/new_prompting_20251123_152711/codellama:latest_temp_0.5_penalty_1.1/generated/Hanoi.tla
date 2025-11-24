---- MODULE Hanoi ----
(**************************************************************************)
(* Towers of Hanoi with N towers.                                          *)
(*                                                                         *)
(* The initial predicate specifies the initial values of the variables.    *)
(*                                                                         *)
(* Next specifies the transition relation.                                 *)
(**************************************************************************)

CONSTANTS   D, N, big, small, NotSolved, RightTower, LeftTower, MiddleTower
VARIABLES   tower, disk
----------------------------------------------------------------------------
Init == \* The initial predicate.
    /\ tower = [t |-> IF t = RightTower THEN 2^D ELSE 0]
    /\ disk = [d |-> IF d = small THEN big ELSE 0]
    /\ NotSolved = TRUE
    /\ RightTower = {1 .. N}
    /\ LeftTower = {N+1 .. 2*N}
    /\ MiddleTower = {2*N+1 .. 3*N}
----------------------------------------------------------------------------
Next == \* The transition relation.
    /\ (big \in big \* Tower) \* Disk => Move(big, big, small)
    /\ (small \in big \* Tower) \* Disk => Move(small, big, small)
    /\ (big \in small \* Tower) \* Disk => Move(big, small, small)
    /\ (small \in small \* Tower) \* Disk => Move(small, small, small)
    /\ (big \in big \* Tower) \* NotDisk => Move(big, big, big)
    /\ (small \in big \* Tower) \* NotDisk => Move(small, big, big)
    /\ (big \in small \* Tower) \* NotDisk => Move(big, small, big)
    /\ (small \in small \* Tower) \* NotDisk => Move(small, small, big)
----------------------------------------------------------------------------
Move == \* The action that moves a disk from one tower to another.
    /\ (fromTower \in 1 .. N)
    /\ (toTower   \in 1 .. N)
    /\ (disk      \in 1 .. D)
    ==> IF fromTower = toTower
        THEN FALSE
        ELSE tower[fromTower] - disk <= tower[toTower] + disk
----------------------------------------------------------------------------
Invariant == NotSolved <-> RightTower # 2^N-1
=============================================================================
====