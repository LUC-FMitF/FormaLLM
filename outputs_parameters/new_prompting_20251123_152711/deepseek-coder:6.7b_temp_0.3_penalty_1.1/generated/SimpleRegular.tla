---- MODULE SimpleRegular ----
(***************************************************************************)
(* This module implements a simple algorithm using regular registers.       *)
(***************************************************************************)

EXTENDS FiniteSets, Naturals, Sequences
  
\* Constants
CONSTANT N == 8

\* Global variables
VARIABLE x == [i \in 0..(N-1) |-> {0}], y == [i \in 0..(N-1) |-> {0}]

\* Process definition
PROCEDURE (proc \in 0..N-1)
  a1: x[self] := {0,1}
  a2: x[self] := {1}
  b: WITH (v \in x[(self-1) % N]) [y[self] := v ]

\* Type invariant for the algorithm of module SimpleRegular.
TYPE INVARIANT TypeOK ==
  FORALL i \in 0..(N-1), y[i] \in UNION {v | v \in x[j], j \in 0..(N-1)}

\* Inductive invariant for the algorithm of module SimpleRegular.
INDUCTIVE INVARIANT Inv ==
  [~x' = x /\ ~y' = y] ==> (FORALL i \in 0..(N-1), y[i] \in UNION {v | v \in x[j], j \in 0..(N-1)})

\* Proof of correctness for the algorithm of module SimpleRegular.
PROOF OF CORRECTNESS PCorrect ==
  [~x' = x /\ ~y' = y] ==> (FORALL i \in 0..(N-1), y[i] \in UNION {v | v \in x[j], j \in <｜begin▁of▁sentence｜>})
====