---- MODULE TowersOfHanoi ----
EXTENDS Naturals, FiniteSets, Sequences

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
VARIABLES tower

(***************************************************************************)
(* The total sum of all towers must amount to the disks in the system      *)
(***************************************************************************)
SumInvariant == Sum(tower) = (D * (D + 1)) \div 2

(***************************************************************************)
(* Towers are naturals in the interval (0, 2^D] *)
(***************************************************************************)
TowerInvariant == tower \in [1..N -> PowersOfTwo(D)]

(***************************************************************************)
(* Now we define of the initial predicate, that specifies the initial      *)
(* values of the variables.                                                *)
(***************************************************************************)
Init == /\ tower = [t \in 1..N |-> IF t = 1 THEN (D * (D + 1)) \div 2 ELSE 0]
        /\ SumInvariant
        /\ TowerInvariant

(***************************************************************************)
(* TRUE iff the tower is empty                                             *)
(***************************************************************************)
IsEmpty(t) == tower[t] = 0

(***************************************************************************)
(* TRUE iff the disk is located on the given tower                         *)
(***************************************************************************)
IsOnTower(disk, t) == tower[t] >= 2^disk

(***************************************************************************)
(* TRUE iff disk is the smallest disk on tower                             *)
(***************************************************************************)
IsSmallestOnTower(disk, t) == /\ IsOnTower(disk, t)
                              /\ ~IsOnTower(disk - 1, t)

(***************************************************************************)
(* TRUE iff disk can be moved off of tower                                 *)
(***************************************************************************)
CanMoveOff(disk, t) == IsSmallestOnTower(disk, t)

(***************************************************************************)
(* TRUE iff disk can be moved to the tower                                 *)
(***************************************************************************)
CanMoveTo(disk, t) == /\ IsEmpty(t)
                      \/ ~IsOnTower(disk - 1, t)

(***************************************************************************)
(* Define all possible actions that disks can perform.                     *)
(***************************************************************************)
Move(disk, from, to) ==
  /\ CanMoveOff(disk, from)
  /\ CanMoveTo(disk, to)
  /\ tower' = [tower EXCEPT ![from] = @ - 2^disk, ![to] = @ + 2^disk]

(***************************************************************************)
(* We define the formula Spec to be the complete specification, asserting  *)
(* of a behavior that it begins in a state satisfying Init, and that every *)
(* step either satisfies Next or else leaves the pair <<big, small>>       *)
(* unchanged.                                                              *)
(***************************************************************************)
Next == \E disk \in 1..D, from \in 1..N, to \in 1..N :
          /\ from # to
          /\ Move(disk, from, to)

Spec == Init /\ [][Next]_tower

(***************************************************************************)
(* The final configuration has all disks on the right tower. If TLC is set *)
(* to run with an invariant rightTower # 2^N-1, it will search for         *)
(* configurations in which this invariant is violated. If violation can be *)
(* found, the stack trace shows the steps to solve the Hanoi problem.      *)
(***************************************************************************)
NotSolved == tower[N] # (D * (D + 1)) \div 2

(***************************************************************************)
(* We find a solution by having TLC check if NotSolved is an invariant,    *)
(* which will cause it to print out an "error trace" consisting of a       *)
(* behavior ending in a state where NotSolved is false. With three disks,  *)
(* and three towers the puzzle can be solved in seven moves.               *)
(* The minimum number of moves required to solve a Tower of Hanoi puzzle   *)
(* generally is 2n - 1, where n is the number of disks. Thus, the counter- *)
(* examples shown by TLC will be of length 2n-1                            *)
(***************************************************************************)
THEOREM Spec => []NotSolved
=============================================================================
\* Modification History
\* Last modified Tue May 17 14:55:33 CEST 2016 by markus
\* Created Sun Jul 17 10:20:57 CEST 2011 by markus