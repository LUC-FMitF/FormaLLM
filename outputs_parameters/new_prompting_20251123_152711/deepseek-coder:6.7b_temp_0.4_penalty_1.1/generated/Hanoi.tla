---- MODULE Hanoi ----

(***************************************************************************)
(* Defines operators on finite zero-indexed sequences, where a sequence of  *)
(* length n is represented as a function whose domain is the set 0..(n-1)   *)
(* (the set {0, 1, ... , n-1}).                                             *)
(***************************************************************************)

CONSTANTS D, N (* Number of disks and towers respectively *)
VARIABLES tower[N], disk[D] (* The towers and disks *)

Init == \* Initial state. All disks are on the first tower.
    /\ [i \in 0..(D-1) -> EXISTS j \in 0..(N-1) : tower[j][i] = disk[i]]
    /\ [i \in 0..(N-1) -> LENGTH(tower[i]) = 0 OR Cardinality(tower[i]) = i + 1]
    /\ EXISTS j \in 0..(D-1) : disk[j] = j + 1 (* All disks are distinct *)
    /\ N > 0 AND D > 0 (* Number of towers and disks must be positive *)

Next == \* Next state. A disk can be moved from one tower to another if it is the topmost disk on a tower or it is smaller than the topmost disk on the other tower.
    [i, j \in 0..(N-1)] /\ (LENGTH(tower[j]) = 0 OR EXISTS k \in 0..(LENGTH(tower[j]) - 1) : tower[j][k] > tower[i][0])
    ==> [i, j \in 0..(N-1)] /\ IF LENGTH(tower[i]) > 0 THEN tower[j] = Append(tower[j], tower[i][0]) ELSE tower[j] = tower[j] FI
    [] OTHERWISE FALSE

Inv_RightTower == \* An invariant that checks if all disks are on the rightmost tower.
    EXISTS i \in 0..(N-1) : LENGTH(tower[i]) = D - i

Spec == [<>] /\ Init /\ [](Next <> Inv_RightTower)
====