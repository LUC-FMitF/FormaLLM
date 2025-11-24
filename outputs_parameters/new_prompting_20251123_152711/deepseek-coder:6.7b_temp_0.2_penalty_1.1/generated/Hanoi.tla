---- MODULE Hanoi ----

(**************************************************************************)
(* Towers of Hanoi with N towers                                          *)
(* Each tower is represented by a natural number and all towers are empty   *)
(* except for the first one, where all disks are located.                  *)
(* No need to try to move onto the same tower (Move(...) prevents it too)  *)
(* Modification History                                                    *)
(* Last modified Tue May 17 14:55:33 CEST 2016 by markus                   *)
(* Created Sun Jul 17 10:20:57 CEST 2011 by markus                       *)
(**************************************************************************)
(* A set of all powers of two up to n                                    *)
(**************************************************************************)
PowersOfTwo(n) == {i : 0 <= i < n | IsPowerOfTwo(i)}
IsPowerOfTwo(x) == EXISTS y . 2^y = x

(* Towers are represented by natural numbers and all towers are empty except for the first one, where all disks are located. *)
Tower[n] == {i : 0 <= i < n}
EmptyTower == {}

(* No need to try to move onto the same tower (Move(...) prevents it too) *)
Move(from_, to_) == IF from_ /= EmptyTower THEN {to_' = to_ U {old MAX from_}, from_' = old MIN from_ - 1} ELSE from_

(* Disk is the smallest disk on tower *)
IsSmallestDiskOnTower(tower, disk) == LET max_disk = MAX tower IN disk = max_disk

(* Disk can be moved off of tower *)
CanMoveOffOfTower(from_, to_) == EXISTS x . from_ U {x} = to_ AND IsSmallestDiskOnTower(to_, x)

(* Disk can be moved to the tower *)
CanMoveToTower(from_, to_) == LET max_disk = MAX from_ IN EXISTS x . to_ U {x} = from_ AND (NOT EXISTS y . from_ U {y} = to_ OR x > max_disk)

(* Define all possible actions that disks can perform *)
Next(from_, to_) == IF CanMoveOffOfTower(from_, to_) THEN Move(from_, to_) ELSE from_

(* Specification of the initial state and transition relation *)
Init == {0 : Tower[n], 1 : EmptyTower, 2 : EmptyTower}
NextState(state) == {i : i IN DOMAIN state /\ next = Next(state[i], (i + 1) MOD n) |-> IF next = state[i] THEN state ELSE next}
Spec == [Init & PowersOfTwo(n)] -> A [F "NextState" & PowersOfTwo(n)]

(* Invariant: all disks are on the right tower *)
rightTower # 2^n - 1
====