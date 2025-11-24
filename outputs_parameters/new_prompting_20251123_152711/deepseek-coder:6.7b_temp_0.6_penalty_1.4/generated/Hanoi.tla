---- MODULE Hanoi ----
(****************************************************)
(* Towers of Hanoi with N disks                    *)
(****************************************************)

CONSTANTS Disk, Tower = {0, ..., N-1} \* The set of all disks and towers.
VARIABLES DiskOnTower[Disk -> Tower] \* A mapping from disks to towers.

Init == \* The initial predicate.
     /\ Domain(DiskOnTower) = {0}
     /\ DiskOnTower' = [d \in Disk |-> IF d = 0 THEN 0 ELSE 1]

Next[s] == \* A state formula for the next state.
    EXISTS d, t, u ELEMENT OF s: 
        DOMAIN {d} UNION (DOMAIN(DiskOnTower) - {t}) INTER SELF.POWERSET(Nat)
     /\ DiskOnTower' = [IF DiskOnTower[u] = t THEN u ELSE DiskOnTower[u]] 

Spec == \* The complete specification.
    Init /\ WFRec(Next, "")
====