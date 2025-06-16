---- MODULE TowersOfHanoi ----
EXTENDS Naturals, FiniteSets, Sequences

(***************************************************************************)
(* Towers are represented by natural numbers                               *)
(* all towers are empty except all disks are on the first Tower            *)
(* All less significant bits are 0                                         *)
(* Remaining tower does not change                                         *)
(* No need to try to move onto the same tower (Move(...) prevents it too)  *)
(* Modification History                                                    *)
(* Last modified Tue May 17 14:55:33 CEST 2016 by markus                   *)
(* Created Sun Jul 17 10:20:57 CEST 2011 by markus                         *)
(***************************************************************************)

CONSTANTS D, N

VARIABLES towers

IsPowerOfTwo(i) == i \in {2^k : k \in 0..D}

PowersOfTwo(n) == {2^k : k \in 0..n}

Sum(f) == LET S == {x \in DOMAIN f : f[x] /= 0} IN
          IF S = {} THEN 0 ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + Sum([f EXCEPT ![x] = 0])

TowerInvariant == /\ towers \in [1..N -> Nat]
                  /\ \A t \in 1..N : towers[t] \in PowersOfTwo(D)
                  /\ Sum(towers) = 2^D - 1

Init == /\ towers = [t \in 1..N |-> IF t = 1 THEN 2^D - 1 ELSE 0]
        /\ TowerInvariant

IsEmpty(tower) == tower = 0

HasDisk(disk, tower) == tower % 2^disk = 2^(disk - 1)

IsSmallestDisk(disk, tower) == /\ HasDisk(disk, tower)
                               /\ ~HasDisk(disk + 1, tower)

CanMoveDisk(disk, tower) == /\ ~IsEmpty(tower)
                            /\ IsSmallestDisk(disk, tower)

CanMoveToDisk(disk, tower) == /\ IsEmpty(tower)
                              \/ ~IsSmallestDisk(disk - 1, tower)

Move(disk, from, to) == /\ CanMoveDisk(disk, towers[from])
                        /\ CanMoveToDisk(disk, towers[to])
                        /\ towers' = [towers EXCEPT ![from] = towers[from] - 2^(disk - 1),
                                                      ![to] = towers[to] + 2^(disk - 1)]
                        /\ TowerInvariant

Next == \E disk \in 1..D, from \in 1..N, to \in 1..N :
        /\ from # to
        /\ Move(disk, from, to)

Spec == Init /\ [][Next]_towers

NotSolved == towers[N] # 2^D - 1

Invariant == TowerInvariant /\ NotSolved

=============================================================================