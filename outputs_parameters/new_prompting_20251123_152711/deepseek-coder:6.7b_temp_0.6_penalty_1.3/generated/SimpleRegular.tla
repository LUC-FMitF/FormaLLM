---- MODULE SimpleRegular ----
(***************************************************************************)
(* This module implements a simple algorithm using regular registers.       *)
(* The algorithm is an N-process algorithm shared-memory algorithm, in which *)
(* each process i has a shared register x[i] that it writes and is read by   *)
(* process x[(i-1) % N]. Each process i also has a local register y[i]     *)
(* that only it can access.                                                 *)
(***************************************************************************)

EXTENDS FiniteSets, Naturals, Sequences

\* Global variables
VARIABLES x == [i \in 0..N-1 |-> {0}], y == [i \in 0..N-1 |-> {0}]

(* Process definition *)
PROCEDURE (proc \in 0..N-1)
BEGIN
    a1: x[self] := {0,1};   (* Write two different values to register x[i] *)
    a2: x[self] := {1};     (* Overwrite the value in register x[i] with 1 *)
    b: WITH (v \in x[(self-1) % N]) DO y[self] := v;   (* Read and store the value from register x[(i-1) % N] to y[i] *)
END Proc

(* Type invariant for SimpleRegular *)
TypeOK == UNCHANGED /\ (\forall i \in 0..N-1 . (x[i] \subseteq {0,1})) /\ y[self] = x[(self+1) % N]

(* Inductive invariant for SimpleRegular *)
Inv == Initially(TypeOK) AND 
    [~(a1 U a2)] ==> (\forall i \in 0..N-1 . (x[i] = {0,1}) /\ y[self] = x[(self+1) % N])

(* Proof of correctness of the algorithm *)
PCorrect ==  EXISTS m \in Nat . [m >= 5](TypeOK /\ Inv) 
AND [][m < 5](TypeOK)
*******************************************************************************)
====
CONSTANT N = 8
SPECIFICATION Spec == <<SimpleRegular>>
INVARIANTS PCorrect TypeOK Inv
====