---- MODULE Consensus ----
(***************************************************************************)
(* The consensus problem requires a set of processes to choose a single     *)
(* value. This module specifies the problem by specifying exactly what      *)
(* the requirements are for choosing a value.                               *)
(***************************************************************************)

EXTENDS FiniteSets, Naturals, Sequences
  
\* The set of all values that can be chosen
CONSTANT Value = {v1, v2, v3}

VARIABLE chosen \in Powerset(Value)

MACRO Choose() == when (chosen = {}) [(v \in Value) -> (chosen := {v})]

OPERATION Consensus == 
  lbl: WHILE TRUE DO 
    Choose() 
  END

\* The safety property that at most one value is chosen. We first define the 
type-correctness invariant TypeOK, and then define Inv to be the inductive 
invariant that asserts TypeOK and that the cardinality of the set `chosen' 
is at most 1. We then prove that, in any behavior satisfying the safety 
specification Spec, the invariant Inv is true in all states. This means that 
at most one value is chosen in any behavior.
*//*
\* The following lemma asserts that Inv is an inductive invariant of the    *)
(* next-state action Next. It is the key step in proving that Inv is an    *)
(* invariant of (true in every behavior allowed by) specification Spec.     *)
*\*)
\* We now define LiveSpec to be the algorithm's specification with the      *)
(* added fairness condition of weak fairness of the next-state relation,    *)
(* which asserts that execution does not stop if some action is enabled.    *)
(* The temporal formula Success asserts that some value is chosen.          *)
\* Below, we prove that LiveSpec implies that Success holds eventually.     *)
(* This means that, in every behavior satisfying LiveSpec, some value will  *)
(* be chosen.                                                               *)
*\*)
\* For liveness, we need to assume that there exists at least one value.    *)
*\*/

INVARIANT TypeOK(s) == (chosen \in Powerset(Value))

INVARIANT Inv == 
  [](chosen = {}) /\ Cardinality(chosen) <= 1

PROPERTY Success == 
  EXISTS v \in Value : (chosen = {v})

SPECIFICATION LiveSpec == 
  Init /\ [][]Next_vars /\ ENABLED(Choose())

CHECK_DEADLOCK FALSE
====