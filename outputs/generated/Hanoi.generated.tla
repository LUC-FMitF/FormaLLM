---- MODULE Hanoi ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(***************************************************************************)
(* Towers are represented by natural numbers                               *)
(***************************************************************************)
CONSTANT Towers

(***************************************************************************)
(* all towers are empty except all disks are on the first Tower            *)
(***************************************************************************)
VARIABLE towers

(***************************************************************************)
(* All less significant bits are 0                                         *)
(***************************************************************************)
IsPowerOfTwo(i) == CHOOSE k \in 0..31 : i = 2^k

(***************************************************************************)
(* Remaining tower does not change                                         *)
(***************************************************************************)
PowersOfTwo(n) == {i \in 1..n : IsPowerOfTwo(i)}

(***************************************************************************)
(* No need to try to move onto the same tower (Move(...) prevents it too)  *)
(***************************************************************************)
Sum(f) == LET S == DOMAIN f IN IF S = {} THEN 0 ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + Sum([f EXCEPT ![x] = NULL])

(***************************************************************************)
(* Modification History                                                    *)
(* Last modified Tue May 17 14:55:33 CEST 2016 by markus                   *)
(* Created Sun Jul 17 10:20:57 CEST 2011 by markus                         *)
(***************************************************************************)
Disks(D, N) == PowersOfTwo(D) \cup {i \in 1..(N - D) : TRUE}

(***************************************************************************)
(* D is number of disks and N number of towers                             *)
(***************************************************************************)
TowersInvariant(D, N) == /\ towers \in [Towers -> SUBSET Disks(D, N)]
                          /\ Sum(towers) = (2^D) - 1

(***************************************************************************)
(* Towers of Hanoi with N towers                                           *)
(***************************************************************************)
Init(D, N) == towers = [t \in Towers |-> IF t = 1 THEN Disks(D, N) ELSE {}]

(***************************************************************************)
(* The total sum of all towers must amount to the disks in the system      *)
(***************************************************************************)
IsEmpty(tower) == towers[tower] = {}

(***************************************************************************)
(* Towers are naturals in the interval (0, 2^D]                           *)
(***************************************************************************)
HasDisk(tower, disk) == disk \in towers[tower]

(***************************************************************************)
(* Now we define of the initial predicate, that specifies the initial      *)
(* values of the variables.                                                *)
(***************************************************************************)
IsSmallest(tower, disk) == /\ HasDisk(tower, disk)
                           /\ \A d \in towers[tower] : d >= disk

(***************************************************************************)
(* TRUE iff the tower is empty                                             *)
(***************************************************************************)
CanMoveFrom(tower, disk) == /\ HasDisk(tower, disk)
                            /\ IsSmallest(tower, disk)

(***************************************************************************)
(* TRUE iff the disk is located on the given tower                         *)
(***************************************************************************)
CanMoveTo(tower, disk) == /\ IsEmpty(tower)
                          \/ ~IsSmallest(tower, disk)

(***************************************************************************)
(* TRUE iff disk is the smallest disk on tower                             *)
(***************************************************************************)
Move(disk, from, to) == /\ CanMoveFrom(from, disk)
                        /\ CanMoveTo(to, disk)
                        /\ towers' = [towers EXCEPT ![from] = towers[from] \ {disk},
                                                      ![to] = towers[to] \cup {disk}]

(***************************************************************************)
(* TRUE iff disk can be moved off of tower                                 *)
(***************************************************************************)
Next == \E disk \in Disks(D, N), from \in Towers, to \in Towers \ from : Move(disk, from, to)

(***************************************************************************)
(* TRUE iff disk can be moved to the tower                                 *)
(***************************************************************************)
Spec(D, N) == Init(D, N) /\ [][Next]_towers

(***************************************************************************)
(*                                                                         *)
(***************************************************************************)
NotSolved == towers[Towers] # Disks(D, N)

(***************************************************************************)
(* Define all possible actions that disks can perform.                     *)
(***************************************************************************)
THEOREM Spec(D, N) => []TowersInvariant(D, N)

(***************************************************************************)
(* We define the formula Spec to be the complete specification, asserting  *)
(* of a behavior that it begins in a state satisfying Init, and that every *)
(* step either satisfies Next or else leaves the pair <<big, small>>       *)
(* unchanged.                                                              *)
(***************************************************************************)
THEOREM Spec(D, N) => <>~NotSolved

(***************************************************************************)
(* The final configuration has all disks on the right tower. If TLC is set *)
(* to run with an invariant rightTower # 2^N-1, it will search for         *)
(* configurations in which this invariant is violated. If violation can be *)
(* found, the stack trace shows the steps to solve the Hanoi problem.      *)
(***************************************************************************)
=============================================================================