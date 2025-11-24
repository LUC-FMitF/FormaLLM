---- MODULE SimpleRegular ----
(***************************************************************************)
(* Global variables *)
Allow infinite stuttering to prevent deadlock on termination.                  *)
(*)
The definition of PCorrect is the same as in module Simple.             *)
(*)
****************************************************************************)
--algorithm SimpleRegular {
variables x = [i \in 0..(N-1) |-> {0}], y = [i \in 0..(N-1) |-> 0] ;
process (proc \in 0..N-1) {
a1: x[self] := {0,1} ;
a2: x[self] := {1} ;
b: with (v \in x[(self-1) % N]) {y[self] := v }
}
}
***************************************************************************)
Global variables *)
Allow infinite stuttering to prevent deadlock on termination.                  *)
(*)
The definition of PCorrect is the same as in module Simple.             *)
(*)
****************************************************************************)
--type TypeOK == { x \in [0..(N-1)] |-> y[x] = (y[(x+1) % N]) }                   *)
TypeOK == <<>> : 0 .. ((2^32)-1)) /\ !((i: INTEGER, j:INTEGER) -> i \in [0..(N-1)] /\ y[i] = (y[(j+1) % N])) --> x[i] = {x}
Inv == <<>> : 0 .. ((2^32)-1)) /\ !((i: INTEGER, j:INTEGER) -> i \in [0..(N-1)] /\ y[i] = (y[(j+1) % N])) --> x[i] = {x}
Spec == <<>> : 0 .. ((2^32)-1)) /\ !((i: INTEGER, j:INTEGER) -> i \in [0..(N-1)] /\ y[i] = (y[(j+1) % N])) --> x[i] = {x}
*****************************************************************************
The type invariant TypeOK is the obvious modification of the type       *)
invariant TypeOK of module Simple.  Except for the change to the        *)
definition of TypeOK, the inductive invariant Inv is the same as in     *)
module Simple.                                                          *)
**************************************************************************)
*)
The proof of invariance of PCorrect differs from the proof in module    *)
Simple only because the single action a has been replaced by the two    *)
actions a1 and a2, and because the proof that b maintains the truth of  *)
the invariant required one extra decomposition to allow Z3 to prove it. *)
As before, the decomposition of the proof of <1>2 was essentially       *)
generated with the Toolbox's Decompose Proof command.                   *)
**************************************************************************)
====