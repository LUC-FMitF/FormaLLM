---- MODULE SimpleRegular ----
(***************************************************************************)
(* This module implements a simple algorithm using regular registers.       *)
(* Each process i has a shared register x[i] that it writes and is read by    *)
(* process x[(i-1) % N].  Each process i also has a local register y[i]     *)
(* that only it can access.                                                 *)
(***************************************************************************)

EXTENDS ZSequences

CONSTANT N == 8
VARIABLES x == [i \in 0..N-1 |-> {0}], y == [i \in 0..N-1 |-> {0}]

\* Process definition
PROCEDURE (proc) ==
  a1: x[self] := {0,1}
  a2: x[self] := {1}
  b: WITH v \in x[(self - 1) % N] DO y[self] := v

\* Type invariant for regular registers
TYPEOK ==
  EVERY i \in 0..N-1, j \in 0..N-1, k \in 2 UNTIL (x[i][j] = k) ==>
    Cardinality(Intersection(x[i], x[(i + 1) % N])) <= 1

\* Inductive invariant for correctness of the algorithm
PCorrect ==
  EVERY i \in 0..N-1, j \in 0..N-1, k \in 2 UNTIL (x[i][j] = k) ==>
    Cardinality(Intersection(x[i], x[(i + 1) % N])) <= 1 /\ y[i] = {k}

\* Inductive invariant for the algorithm
Inv ==
  EVERY i \in 0..N-1, j \in <｜begin▁of▁sentence｜> UNTIL (y[i] = j) ==>
    Cardinality(Intersection(x[i], x[(i + 1) % N])) <= 1 /\ y[i] = {j}

=============================================================================
====