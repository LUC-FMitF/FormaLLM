---- MODULE Hanoi ----
(*********************************************************)
(* Towers are represented by natural numbers             *)
(* all towers are empty except all disks are on the first Tower *)
(* No need to try to move onto the same tower (Move(...) prevents it too) *)
(*********************************************************)

CONSTANT N = 3; (* number of towers *)
CONSTANT D = 3; (* number of disks *)

(* Initial predicate that specifies the initial values of the variables *)
Init == [
  tower[i] = (i = 0) /\ (i > 0) -> 0 : i \in 0..D,
  top[i] = (i = 0) /\ (i > 0) -> (2^D - 1) - (2^(D - i) - 1) : i \in 0..D
]

(* Predicate for tower being empty *)
Empty(t) == (tower[0] = 0)

(* Predicate for disk being located on the given tower *)
On(t, d) == (tower[d] > 0)

(* Predicate for disk being the smallest disk on tower *)
Smallest(t, d) == (tower[t] = d)

(* Predicate for disk can be moved off of tower *)
CanMoveOff(t) == (tower[t] > 0)

(* Predicate for disk can be moved to the tower *)
CanMoveTo(t) == (tower[t] = 0) \/ (tower[t] > 0 /\ tower[t - 1] > 0)

(* Actions that disks can perform *)
Move(t1, t2) == tower[t1] = tower[t1] - 1 /\ tower[t2] = tower[t2] + 1

(* Specification *)
Spec == [
  Init,
  [
    [] top[t] = (t = 0) /\ (t > 0) -> (2^D - 1) - (2^(D - t) - 1) : t \in 0..D
  ]
]

=============================================================================
====