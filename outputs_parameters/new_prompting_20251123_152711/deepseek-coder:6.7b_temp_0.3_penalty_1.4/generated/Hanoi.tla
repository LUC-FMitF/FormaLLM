---- MODULE Hanoi ----

(***************************************************************************************)
(* Towers of Hanoi with N towers                                                       *)
(***************************************************************************************)
CONSTANTS   D,    (* Number of disks *)
            N      (* Number of towers *)
VARIABLES   tower[1..N],  (* The state of each tower: a sequence representing the stack. *)
            topDisk[1..N]     (* Top disk on each tower (0 if empty) *)
----------------------------------------------------------------------------------------
EmptyTower == [i \in 1..D |-> 2^(d+1)]   (* A tower is considered "empty" when all its bits are zero. *)
MoveDiskTo => [t \in 1..N, d \in D |-> IF topDisk[t] = (0 ORIF NOT EXISTS i IN 1..D : tower[i][d]) THEN {topDisk[t]->(2^d)} ELSE {} ]
MoveFromTo => [s, t \in 1..N |->  IF s <> t AND topDisk[s] > 0 AND (NOT EXISTS i IN 1..D : tower[i][d]) THEN {topDisk[t]->(2^d)} ELSE {} ]
Next == UNION [MoveFromTo, MoveDiskTo]   (* Actions: move a disk from one to another or onto an empty slot. *)
Init ==  \E i IN 1..N : tower[i] = EmptyTower /\ topDisk = 0    (* Initially all towers are empty and no disks exist. *)
Spec == []<>(~Next)   (** The system is in a final state if there's nothing to do next **)
----------------------------------------------------------------------------------------
=====