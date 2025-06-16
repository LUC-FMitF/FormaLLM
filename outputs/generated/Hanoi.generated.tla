------------------------------ MODULE TowersOfHanoi ------------------------------
(***************************************************************************)
(* Towers are represented by natural numbers. Initially, all towers are    *)
(* empty except all disks are on the first Tower. All less significant     *)
(* bits are 0. Remaining tower does not change. No need to try to move     *)
(* onto the same tower (Move(...) prevents it too).                        *)
(***************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, TLC

(***************************************************************************)
(* TRUE iff i is a power of two                                            *)
(***************************************************************************)
IsPowerOfTwo(i) == \E n \in Nat : i = 2^n

(***************************************************************************)
(* A set of all powers of two up to n                                      *)
(***************************************************************************)
PowersOfTwo(n) == {i \in 1..n : IsPowerOfTwo(i)}

(***************************************************************************)
(* Copied from TLA+'s Bags standard library. The sum of f[x] for all x in  *)
(* DOMAIN f.                                                               *)
(***************************************************************************)
Sum(f) == LET S == DOMAIN f IN
          IF S = {} THEN 0
          ELSE LET x == CHOOSE y \in S : TRUE IN
               f[x] + Sum([f EXCEPT ![x] = NULL])

(***************************************************************************)
(* D is number of disks and N number of towers                             *)
(***************************************************************************)
CONSTANTS D, N
ASSUME D \in Nat /\ N \in Nat

(***************************************************************************)
(* Towers of Hanoi with N towers                                           *)
(***************************************************************************)
VARIABLES towers, move
vars == <<towers, move>>

(***************************************************************************)
(* The total sum of all towers must amount to the disks in the system      *)
(***************************************************************************)
Invariant == Sum(towers) = 2^D - 1

(***************************************************************************)
(* Towers are naturals in the interval (0, 2^D]                           *)
(***************************************************************************)
TypeInvariant == towers \in [1..N -> 0..(2^D - 1)]

(***************************************************************************)
(* Now we define of the initial predicate, that specifies the initial      *)
(* values of the variables.                                                *)
(***************************************************************************)
Init == /\ towers = [t \in 1..N |-> IF t = 1 THEN 2^D - 1 ELSE 0]
        /\ move = <<0, 0>>

(***************************************************************************)
(* TRUE iff the tower is empty                                             *)
(***************************************************************************)
IsEmpty(tower) == towers[tower] = 0

(***************************************************************************)
(* TRUE iff the disk is located on the given tower                         *)
(***************************************************************************)
IsOnTower(disk, tower) == towers[tower] \geq 2^disk

(***************************************************************************)
(* TRUE iff disk is the smallest disk on tower                             *)
(***************************************************************************)
IsSmallest(disk, tower) == /\ IsOnTower(disk, tower)
                           /\ ~IsOnTower(disk - 1, tower)

(***************************************************************************)
(* TRUE iff disk can be moved off of tower                                 *)
(***************************************************************************)
CanMoveOff(disk, tower) == IsSmallest(disk, tower)

(***************************************************************************)
(* TRUE iff disk can be moved to the tower                                 *)
(***************************************************************************)
CanMoveTo(disk, tower) == /\ IsEmpty(tower)
                          \/ ~IsOnTower(disk - 1, tower)

(***************************************************************************)
(* Define all possible actions that disks can perform.                     *)
(***************************************************************************)
Move(disk, from, to) ==
  /\ CanMoveOff(disk, from)
  /\ CanMoveTo(disk, to)
  /\ towers' = [towers EXCEPT ![from] = @ - 2^disk,
                               ![to] = @ + 2^disk]
  /\ move' = <<disk, from, to>>
  /\ UNCHANGED <<N, D>>

Next == \E disk \in 1..D, from \in 1..N, to \in 1..N :
        /\ from # to
        /\ Move(disk, from, to)

(***************************************************************************)
(* We define the formula Spec to be the complete specification, asserting  *)
(* of a behavior that it begins in a state satisfying Init, and that every *)
(* step either satisfies Next or else leaves the pair <<big, small>>       *)
(* unchanged.                                                              *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* The final configuration has all disks on the right tower. If TLC is set *)
(* to run with an invariant rightTower # 2^N-1, it will search for         *)
(* configurations in which this invariant is violated. If violation can be *)
(* found, the stack trace shows the steps to solve the Hanoi problem.      *)
(***************************************************************************)
NotSolved == towers[N] # 2^D - 1

(***************************************************************************)
(* We find a solution by having TLC check if NotSolved is an invariant,    *)
(* which will cause it to print out an "error trace" consisting of a       *)
(* behavior ending in a state where NotSolved is false. With three disks,  *)
(* and three towers the puzzle can be solved in seven moves.               *)
(* The minimum number of moves required to solve a Tower of Hanoi puzzle   *)
(* generally is 2n - 1, where n is the number of disks. Thus, the counter- *)
(* examples shown by TLC will be of length 2n-1                            *)
(***************************************************************************)
=============================================================================
\* Modification History
\* Last modified Tue May 17 14:55:33 CEST 2016 by markus
\* Created Sun Jul 17 10:20:57 CEST 2011 by markus