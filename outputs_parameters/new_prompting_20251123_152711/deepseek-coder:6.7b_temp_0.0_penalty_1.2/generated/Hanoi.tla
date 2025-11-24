---- MODULE Hanoi ----

(**************************************************************************)
(* Towers of Hanoi                                                            *)
(**************************************************************************)
CONSTANTS   N, D \* Number of towers and disks.
VARIABLES   t[0..N-1], d[0..D-1]  \* The state of each tower/disk.
-------------------------------------------------------------------------------
(* Helper functions *)
PowerOfTwo(n) == EXISTS m : NATURAL, n = 2^m    (* TRUE iff n is a power of two *)
PowersOfTwo <= {x : x \in NATURAL | PowerOfTwo(x)}  (* Set of all powers of two up to n *)
Sum[f](s) == SUM{i: s} f(i)   (* Copied from TLA+'s Bags standard library. The sum of f[x] for all x in DOMAIN f. *)
-------------------------------------------------------------------------------
(* Invariants and predicates *)
EmptyTower(t) == EMPTYSET t  \* TRUE iff the tower is empty
DiskOnTower(d, t) == d INDOMAIN t   (* TRUE iff disk is located on given tower *)
SmallestDisk(d1, d2) == Cardinality[{i : i < D | (Cardinality[t] = 0 OR t[i+1] > d2)}] = SINGLETON {i : i < D & DiskOnTower(d1, t) AND NOT EmptyTower(PREIMAGE[t](CARDINALITY)[{i}])}
CanMoveOff(d, t) == EXISTS m: NATURIAL, (m = CARDINALITY[t] OR d <> t[m])  (* TRUE iff disk can be moved off of tower *)
CanMoveTo(d1, d2, t) == ~EmptyTower(PREIMAGE[t](CARDINALITY)[{0}]) AND (Cardinality[t] = 0 OR Cardinality[Intersection[{i : i < D & DiskOnTower(d2, t)}, PREIMAGE[t](lambda x: d1 > x)]] > 0)  (* TRUE iff disk can be moved to tower *)
-------------------------------------------------------------------------------
(* Initial state and next step formula *)
Init == [n \in NATURAL | (Cardinality[{i : i < D & n = 2^(D-i)} U {j: j < Cardinality[t] AND t[j+1] = d FORALL j}]  (* Initial state where all disks are on the first tower *)
Next == [n \in NATURAL | (Cardinality[{i : i < D & n = 2^(D-i)} U {j: j < Cardinality[t] AND t[j+1] = d FORALL j}]  (* Next step formula where all disks are on the first tower *)
-------------------------------------------------------------------------------
(* Specification and invariants *)
Spec == [n \in NATURAL | (Cardinality[{i : i < D & n = 2^(D-i)} U {j: j < Cardinality[t] AND t[j+1] = d FORALL j}]  (* Specification where all disks are on the first tower *)
rightTower == EXISTS m, s: NATURAL, (m > 0 IMPLIES CanMoveOff(d, PREIMAGE[s](CARDINALITY)[{i}]) AND DiskOnTower(d, t) AND Cardinality[t] = d + 1 FORALL i : m..D-1)]  (* TRUE iff all disks are on the right tower *)
NotSolved == EXISTS s: NATURAL, (Cardinality[{i : i < D & CanMoveOff(d, PREIMAGE[s](CARDINALITY)[{i}])}] > 0 OR Cardinality[t] = d + 1 FORALL t IN DOMAIN f)]  (* TRUE iff not all disks are on the right tower *)
-------------------------------------------------------------------------------
(* Specification and invariants *)
Spec == [n \in NATURAL | (Cardinality[{i : i < D & n = 2^(D-i)} U {j: j < Cardinality[t] AND t[j+1] = d FORALL j}]  (* Specification where all disks are on the first tower *)
rightTower == EXISTS m, s: NATURAL, (m > 0 IMPLIES CanMoveOff(d, PREIMAGE[s](CARDINALITY)[{i}]) AND DiskOnTower(d, t) AND Cardinality[t] = d + 1 FORALL i : m..D-1)]  (* TRUE iff all disks are on the right tower *)
NotSolved == EXISTS s: NATURAL, (Cardinality[{i : i < D & CanMoveOff(d, PREIMAGE[s](CARDINALITY)[{i}])}] > 0 OR Cardinality[t] = d + 1 FORALL t IN DOMAIN f)]  (* TRUE iff not all disks are on the right tower *)
=============================================================================