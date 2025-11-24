---- MODULE Hanoi ----

(***************************************************************************)
(* Towers are represented by natural numbers                                  *)
(* All less significant bits are 0                                            *)
(* No need to try to move onto the same tower (Move(...) prevents it too)     *)
(* Modification History                                                        *)
(* Last modified Tue May 17 14:55:33 CEST 2016 by markus                      *)
(* Created Sun Jul 17 10:20:57 CEST 2011 by markus                            *)
(***************************************************************************)
CONSTANTS D, N (* Number of disks and towers *)
VARIABLES Towers (* Towers[i] is the i-th tower *)

(* All towers are empty except all disks are on the first Tower *)
Init == FORALL i \in 0..D-1: Towers[i] = 0

(* TRUE iff i is a power of two *)
PowerOfTwo(i) == EXISTS j \in NATURAL: i = 2^j

(* A set of all powers of two up to n *)
PowersOfTwo <= {i \in 0..D-1: PowerOfTwo(i)}

(* Copied from TLA+'s Bags standard library. The sum of f[x] for all x in DOMAIN f. *)
Sum(f) == SUMMATION i \in DOMAIN f: f[i]

(* Towers are naturals in the interval (0, 2^D] *)
ValidTowers == FORALL i \in PowersOfTwo: Towers[i] \in NATURAL

(* TRUE iff the tower is empty *)
Empty(tower) == Tower = 0

(* TRUE iff the disk is located on the given tower *)
DiskOnTower(disk, tower) == Disk = Towers[tower]

(* TRUE iff disk is the smallest disk on tower *)
SmallestDisk(disk, tower) == FORALL i \in 0..D-1: DISK[i] <> tower OR (DISK[i] = tower AND i > disk)

(* TRUE iff disk can be moved off of tower *)
CanMoveOff(disk, tower) == DiskOnTower(disk, tower) AND SmallestDisk(disk, tower)

(* TRUE iff disk can be moved to the tower *)
CanMoveTo(disk, tower) == CanMoveOff(disk, tower) AND (tower = 0 OR Towers[tower-1] > Disk)

(* Define all possible actions that disks can perform. *)
Next == IF EXISTS i \in 0..D-1: EXISTS j \in 0..N-1: CanMoveTo(i, j): Towers' = Towers + [j -> Towers[j] + 1]

(* Spec is the complete specification, asserting of a behavior that it begins in *)
(* a state satisfying Init, and that every step either satisfies Next or else leaves *)
(* the pair <<big, small>> unchanged. *)
Spec == Init /\ WF_B[Next](Big \/ Small)

(* The final configuration has all disks on the right tower. If TLC is set to run with an invariant *)
(* rightTower = 2^N-1, it will search for configurations in which this invariant is violated. *)
rightTower == Towers[D] = D

NotSolved == EXISTS i \in 0..D-1: Towers[i] <> 0
====