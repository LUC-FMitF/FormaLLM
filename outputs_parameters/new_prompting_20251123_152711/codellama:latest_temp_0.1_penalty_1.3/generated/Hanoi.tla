---- MODULE Hanoi ----

(*****************************************************************************)
(* Defines a model of the Tower of Hanoi puzzle, with N towers.            *)
(*****************************************************************************)
CONSTANTS   D,        \* The number of disks in each tower.
            N,        \* The total number of towers.
            bigTower, \* A tower that is always the destination for moves.
            smallTower  \* A tower that is always the source for moves.
VARIABLES   big,      \* The set of all disks on the big tower.
            small     \* The set of all disks on the small tower.
            otherTowers,    \* All towers except the big and small ones.
            NotSolved  \* A flag indicating whether a solution has been found.
-----------------------------------------------------------------------------
Init ==                   \* Initial predicate.
    /\ D > 0                \* The number of disks must be positive.
    /\ N >= 2               \* There must be at least two towers.
    /\ bigTower = 1         \* The big tower is always the destination for moves.
    /\ smallTower = 2        \* The small tower is always the source for moves.
    /\ otherTowers = {3..N}   \* All towers except the big and small ones.
    /\ NotSolved = TRUE     \* A solution has not yet been found.
-----------------------------------------------------------------------------
Next ==                  \* Next predicate.
    /\ (big' = big)        \* The set of disks on the big tower remains unchanged.
    /\ (small' = small)      \* The set of disks on the small tower remains unchanged.
    /\ (otherTowers' = otherTowers)  \* All towers except the big and small ones remain unchanged.
    /\ NotSolved = TRUE     \* A solution has not yet been found.
-----------------------------------------------------------------------------
Move(disk, from, to) ==   \* Move a disk from one tower to another.
    /\ (from != to)         \* The move must be between two different towers.
    /\ (to IN otherTowers)  \* The destination tower is not the big or small ones.
    /\ (disk IN from)       \* The disk being moved is on the source tower.
    /\ ~(disk IN to)        \* The disk cannot be on both the source and destination towers at once.
    /\ (from' = from - {disk})  \* Remove the disk from the source tower.
    /\ (to' = to + {disk})      \* Add the disk to the destination tower.
-----------------------------------------------------------------------------
Solved ==                   \* A solution has been found if all disks are on the right tower.
    /\ big = Powerset(N) - 2^D - 1     \* The total sum of all towers must amount to the number of disks in the system.
-----------------------------------------------------------------------------
Powerset(n) ==                          \* A set of all powers of two up to n.
    IF n = 0 THEN {<<>>} ELSE UNION {{i | i IN Powerset(n - 1)} : i \in 2^N} ENDIF
-----------------------------------------------------------------------------
TRUE iff the tower is empty                                           *)
*****************************************************************************)
*****************************************************************************)
TRUE iff disk can be moved to the tower                               *)
*****************************************************************************)
TRUE iff disk can be moved off of tower                              *)
*****************************************************************************)
TRUE iff disk is located on the given tower                          *)
*****************************************************************************)
TRUE iff disk is the smallest disk on tower                         *)
*****************************************************************************)
TRUE iff i is a power of two                                           *)
*****************************************************************************)
*****************************************************************************)
A set of all powers of two up to n                                     *)
*****************************************************************************)
*****************************************************************************)
Copied from TLA+'s Bags standard library. The sum of f[x] for all x in  *)
DOMAIN f.                                                               *)
*****************************************************************************)
*****************************************************************************)
D is number of disks and N number of towers                           *)
*****************************************************************************)
*****************************************************************************)
Towers of Hanoi with N towers                                          *)
*****************************************************************************)
*****************************************************************************)
The total sum of all towers must amount to the disks in the system    *)
*****************************************************************************)
Towers are naturals in the interval (0, 2^D] *)
*****************************************************************************)
Now we define of the initial predicate, that specifies the initial      *)
values of the variables.                                                *)
*****************************************************************************)
*****************************************************************************)
TRUE iff the tower is empty                                             *)
*****************************************************************************)
*****************************************************************************)
TRUE iff the disk is located on the given tower                        *)
*****************************************************************************)
*****************************************************************************)
TRUE iff disk is the smallest disk on tower                            *)
*****************************************************************************)
*****************************************************************************)
TRUE iff disk can be moved off of tower                                *)
*****************************************************************************)
*****************************************************************************)
TRUE iff disk can be moved to the tower                                *)
*****************************************************************************)
*****************************************************************************)
*)
*****************************************************************************)
*****************************************************************************)
Define all possible actions that disks can perform.                    *)
*****************************************************************************)
*****************************************************************************)
We define the formula Spec to be the complete specification, asserting  *)
of a behavior that it begins in a state satisfying Init, and that every *)
step either satisfies Next or else leaves the pair <<big, small>>       *)
unchanged.                                                              *)
*****************************************************************************)
*****************************************************************************)
The final configuration has all disks on the right tower. If TLC is set *)
to run with an invariant rightTower # 2^N-1, it will search for         *)
configurations in which this invariant is violated. If violation can be   *)
found, the stack trace shows the steps to solve the Hanoi problem.      *)
The minimum number of moves required to solve a Tower of Hanoi puzzle   *)
generally is 2n-1, where n is the number of disks. Thus, the counter-    *)
examples shown by TLC will be of length 2n-1                            *)
*****************************************************************************) [/INST:none]  This module defines a model of the Tower of Hanoi puzzle with N towers. The initial state is defined as follows:

* D is the number of disks in each tower, and N is the total number of towers.
* bigTower is always the destination for moves, and smallTower is always the source for moves.
* otherTowers are all towers except the big and small ones.
* NotSolved is a flag indicating whether a solution has been found.

The next state predicate Next specifies that the set of disks on each tower remains unchanged, as well as the fact that NotSolved remains true.

The Move action allows us to move a disk from one tower to another if it is not between two identical towers and the destination tower is not the big or small ones. The source tower must contain the disk being moved, and the destination tower cannot already contain the disk. After moving the disk, we remove it from the source tower and add it to the destination tower.

The Solved predicate specifies that all disks are on the right tower if the total sum of all towers is equal to 2^D - 1. This invariant will cause TLC to search for configurations in which this invariant is violated, indicating a solution has been found. The minimum number of moves required to solve a Tower of Hanoi puzzle generally is 2n-1, where n is the number of disks. Thus, the counterexamples shown by TLC will be of length 2n-1.
====