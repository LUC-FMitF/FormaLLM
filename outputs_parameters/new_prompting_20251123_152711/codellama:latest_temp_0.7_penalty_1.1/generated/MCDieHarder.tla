---- MODULE MCDieHarder ----

(**************************************************************************)
(* The following definitions duplicate the original Die Hard problem.     *)
(**************************************************************************)

CONSTANTS Goal     \* The goal value for the game.
    = 4             (* The goal value for the game. *)

Jug      \* The capacity of the jug.
    <- MCJug         (* The capacity of the jug. *)

Capacity \* A function whose domain is the set of values of Jug.
    <- MCCapacity  (* A function whose domain is the set of values of Jug. *)

**************************************************************************)
(**************************************************************************)
(* Define a function MCCapacity and have the configuration file TLC to     *)
(* substitute MCCapacity for Capacity.  Since we need to know the value of *)
(* Jug to define Capacity (which is a function having Jug as its domain),  *)
(* we also define MCJug and tell TLC to substitute it for Jug.             *)
(**************************************************************************)

MCJug <- CHOOSE j : 0 <= j /\ j < 6
MCCapacity <- [j \in MCJug |-> IF j = 5 THEN 4 ELSE 2]

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved
====