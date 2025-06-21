---- MODULE TowersOfHanoi ----
EXTENDS Naturals, FiniteSets, Sequences

(***************************************************************************)
(* Towers are represented by natural numbers                               *)
(***************************************************************************)
CONSTANT Towers

(***************************************************************************)
(* all towers are empty except all disks are on the first Tower            *)
(***************************************************************************)
VARIABLES tower, disk

(***************************************************************************)
(* All less significant bits are 0                                         *)
(***************************************************************************)
IsPowerOfTwo(i) == CHOOSE k \in 0..31 : i = 2^k

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
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + Sum([y \in S \ {x} |-> f[y]])

(***************************************************************************)
(* D is number of disks and N number of towers                             *)
(***************************************************************************)
D == 3
N == 3

(***************************************************************************)
(* Towers of Hanoi with N towers                                           *)
(***************************************************************************)
Init == /\ tower = [t \in Towers |-> IF t = 1 THEN 2^D - 1 ELSE 0]
        /\ disk = [d \in 1..D |-> 1]

(***************************************************************************)
(* The total sum of all towers must amount to the disks in the system      *)
(***************************************************************************)
Invariant == Sum(tower) = 2^D - 1

(***************************************************************************)
(* Towers are naturals in the interval (0, 2^D]                           *)
(***************************************************************************)
TypeInvariant == /\ tower \in [Towers -> 0..(2^D - 1)]
                 /\ disk \in [1..D -> Towers]

(***************************************************************************)
(* Now we define of the initial predicate, that specifies the initial      *)
(* values of the variables.                                                *)
(***************************************************************************)
Empty(t) == tower[t] = 0

(***************************************************************************)
(* TRUE iff the disk is located on the given tower                         *)
(***************************************************************************)
OnTower(d, t) == disk[d] = t

(***************************************************************************)
(* TRUE iff disk is the smallest disk on tower                             *)
(***************************************************************************)
SmallestOnTower(d, t) == /\ OnTower(d, t)
                         /\ \A e \in 1..D : ~OnTower(e, t) \/ d <= e

(***************************************************************************)
(* TRUE iff disk can be moved off of tower                                 *)
(***************************************************************************)
CanMoveOff(d, t) == /\ OnTower(d, t)
                    /\ SmallestOnTower(d, t)

(***************************************************************************)
(* TRUE iff disk can be moved to the tower                                 *)
(***************************************************************************)
CanMoveTo(d, t) == /\ ~OnTower(d, t)
                   /\ (Empty(t) \/ \E e \in 1..D : /\ OnTower(e, t)
                                                  /\ d < e)

(***************************************************************************)
(* Define all possible actions that disks can perform.                     *)
(***************************************************************************)
Move(d, t) == /\ CanMoveOff(d, disk[d])
              /\ CanMoveTo(d, t)
              /\ tower' = [tower EXCEPT ![disk[d]] = @ - 2^(d-1),
                                       ![t] = @ + 2^(d-1)]
              /\ disk' = [disk EXCEPT ![d] = t]

(***************************************************************************)
(* We define the formula Spec to be the complete specification, asserting  *)
(* of a behavior that it begins in a state satisfying Init, and that every *)
(* step either satisfies Next or else leaves the pair <<big, small>>       *)
(* unchanged.                                                              *)
(***************************************************************************)
Next == \E d \in 1..D, t \in Towers : Move(d, t)

Spec == Init /\ [][Next]_<<tower, disk>>

(***************************************************************************)
(* The final configuration has all disks on the right tower. If TLC is set *)
(* to run with an invariant rightTower # 2^N-1, it will search for         *)
(* configurations in which this invariant is violated. If violation can be *)
(* found, the stack trace shows the steps to solve the Hanoi problem.      *)
(***************************************************************************)
NotSolved == tower[N] # 2^D - 1

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