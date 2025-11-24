---- MODULE MultiPaxos_MC ----

(***************************************************************************************)
(* TLC config-related defs. *)
(***************************************************************************************)
CONSTANTS   Replicas, Writes, Reads, MaxBallot : {<>} \* Defined in separate module *\
SYMMETRY    SymmetricPerms  (* Defines symmetry on the set of all permutations. *)
(***************************************************************************************)
(* Type check invariant. *)
(***************************************************************************************)
TypeOK == Replicas = {<replica>} /\ Writes = {<>, <writeOp1>, <writeOp2>} 
             /\ Reads = {<>, <readOp1>} \* Defined in separate module *\/
(***************************************************************************************)
(* Linearizability constraint. *)
(***************************************************************************************)
Linearizability == [](\E x : Replicas -> <opName> = <writeOp1>  U  <opName> = <writeOp2>) 
                    == ([]\A y: Writes \ {<writeOp1>, <writeOp2>} /\ [](y)\A z: Writes 
                    /(z <<= y)) *\/ (* Defined in separate module *)
=============================================================================
(* SPECIFICATION Spec and INVARIANTS TypeOK & Linearizability.*)
SPECIFICATION Spec \* Defined in a different TLA+ file for this model, 
                    |-> [](TypeOK /\ Linearizability)
INVARIANTS   TypeOK (* Check the type of operations *)
             ,Linearizability(* Ensure linearizable read operation.*)
CHECK_DEADLOCK TRUE (* Enable deadlock checking. *)
=====