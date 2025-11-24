---- MODULE Hanoi ----
(***************************************************************************)
(* Towers are represented by natural numbers                                *)
(* all towers are empty except all disks are on the first Tower             *)
(* All less significant bits are 0                                         *)
(* Remaining tower does not change                                        *)
(* No need to try to move onto the same tower (Move(...) prevents it too)  *)
(* Modification History                                                     *)
(* Last modified Tue May 17 14:55:33 CEST 2016 by markus                    *)
(* Created Sun Jul 17 10:20:57 CEST 2011 by markus                         *)
(***************************************************************************)
(* A set of all powers of two up to n                                      *)
(***************************************************************************)
(* Copied from TLA+'s Bags standard library. The sum of f[x] for all x in  *)
(* DOMAIN f.                                                                 *)
(***************************************************************************)
(* Towers of Hanoi with N towers                                            *)
(***************************************************************************)
(* The total sum of all towers must amount to the disks in the system       *)
(***************************************************************************)
(* Towers are naturals in the interval (0, 2^D]                              *)
(***************************************************************************)
(* Now we define of the initial predicate, that specifies the initial       *)
(* values of the variables.                                                 *)
(***************************************************************************)
(* TRUE iff the tower is empty                                              *)
(***************************************************************************)
(* TRUE iff the disk is located on the given tower                          *)
(***************************************************************************)
(* TRUE iff disk is the smallest disk on tower                              *)
(***************************************************************************)
(* TRUE iff disk can be moved off of tower                                  *)
(***************************************************************************)
(* TRUE iff disk can be moved to the tower                                  *)
(***************************************************************************)
(* Define all possible actions that disks can perform.                      *)
(***************************************************************************)
(* We define the formula Spec to be the complete specification, asserting   *)
(* of a behavior that it begins in a state satisfying Init, and that every  *)
(* step either satisfies Next or else leaves the pair <<big, small>>        *)
(* unchanged.                                                               *)
(***************************************************************************)
(* The final configuration has all disks on the right tower. If TLC is set  *)
(* to run with an invariant rightTower 2^N-1, it will search for          *)
(* configurations in which this invariant is violated. If violation can be  *)
(* found, the stack trace shows the steps to solve the Hanoi problem.       *)
(***************************************************************************)
(* We find a solution by having TLC check if NotSolved is an invariant,     *)
(* which will cause it to print out an "error trace" consisting of a        *)
(* behavior ending in a state where NotSolved is false. With three disks,   *)
(* and three towers the puzzle can be solved in seven moves.                *)
(* The minimum number of moves required to solve a Tower of Hanoi puzzle    *)
(* generally is 2n − 1, where n is the number of disks. Thus, the counter- *)
(* examples shown by TLC will be of length 2n−1                             *)
(***************************************************************************)

CONSTANT N = 3; (* Number of towers *)
CONSTANT D = 3; (* Number of disks *)

(* The tower of Hanoi is represented as a sequence of natural numbers, where the i-th bit represents the presence of a disk on the i-th tower. *)
TYPE Tower = [0 .. N - 1] -> Bool;

(* The tower is empty iff it does not contain any disks *)
EmptyTower(tower) == ~EXISTS i IN 0 .. N - 1 : tower[i];

(* A disk is located on the given tower iff its corresponding bit in the tower is set *)
DiskOnTower(disk, tower) == tower[disk];

(* A disk is the smallest disk on the tower iff it is the leftmost bit in the tower that is set *)
SmallestDiskOnTower(disk, tower) == LEXMIN {i : tower[i]} == disk;

(* A disk can be moved off of the tower iff it is the smallest disk on the tower *)
CanMoveOffTower(disk, tower) == SmallestDiskOnTower(disk, tower);

(* A disk can be moved to the tower iff it is not the smallest disk on the tower *)
CanMoveToTower(disk, tower) == ~SmallestDiskOnTower(disk, tower);

(* Actions that disks can perform *)
Move(disk, fromTower, toTower) ==
  CanMoveOffTower(disk, fromTower) /\ CanMoveToTower(disk, toTower) /\
  [i IN 0 .. N - 1 | i ~= disk] -> fromTower[i] = toTower[i];

(* Initial state of the Hanoi problem *)
Init == [i IN 0 .. N - 1] -> i = 0;

(* Next state of the Hanoi problem *)
Next(state) == EXISTS disk, fromTower, toTower IN state :
  Move(disk, fromTower, toTower) /\ state - {disk} U {toTower} = state';

(* Specification of the Hanoi problem *)
Spec == [state] -> Init <= state /\ Next(state)

(* Invariant that ensures all disks are on the right tower *)
rightTower == EXISTS disk IN 0 .. D - 1 :
  [i IN 0 .. N - 1] -> ~EmptyTower([j IN 0 .. N - 1 | j > i]) -> DiskOnTower(disk, [j IN 0 .. N - 1 | j > i]);

END MODULE Hanoi
====