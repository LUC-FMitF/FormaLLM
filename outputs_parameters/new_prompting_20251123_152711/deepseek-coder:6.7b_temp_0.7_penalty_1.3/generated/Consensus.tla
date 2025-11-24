---- MODULE Consensus ----
(***************************************************************************)
(* The consensus problem requires a set of processes to choose a single     *)
(* value.  This module specifies the problem by specifying exactly what     *)
(* the requirements are for choosing a value.                               *)
(***************************************************************************)

EXTENDS FiniteSets, Naturals, Sequences
  
\* Global variables
Value == {v1, v2, v3}  (* The set of all values that can be chosen *)

VARIABLE chosen == {}  (* The variable `chosen' to represent the set of all chosen values *)

\* Macro Choose() describes the action of changing the value of `chosen' from its initial
value 0 to the value v for an arbitrary value v in Value.
*)
MACRO Choose() == { when \chosen = {} /\ v \in Value; [(v = |> \chosen)] }

\* The algorithm stops after executing a Choose() action. Technically,
the algorithm deadlocks after executing a Choose() action because
control is at a statement whose execution is never enabled. 
*)
ALGORITHM Consensus == {
  variable chosen = {}
  macro Choose()
  { lbl: while (TRUE) { Choose() } }
}

\* The PlusCal translator writes the TLA+ translation of this algorithm below. 
The formula Spec is the TLA+ specification described by the algorithm's code. *)
SPECIFICATION LiveSpec == Init /\ [Next]_vars
  where vars = <|chosen, pc|>
        and Next = Next /\ (vars'=vars)
        
(* We now prove that Inv is an invariant, meaning that it is true in every 
state in every behavior. Before trying to prove it, we should first     *)
use TLC to check that it is true. It's hardly worth bothering to        *)
*)
TO PROVE INVARIANT Inv == FORALL {behaviour} (TypeOK(chosen) /\ CARDINALITY(chosen) <= 1)
  (* We now define the type-correctness invariant TypeOK. It asserts that chosen is a subset of Value *)
  TO PROVE INVARIANT TypeOK == CHOOSE(chosen) SUBSET Value
  
(* Here is our proof that Livespec implies Success. The overall approach   
to the proof follows the rule WF1 discussed in                           *)
*)
TO PROVE PROPERTY Success == EXISTS {behaviour} (CARDINALITY(chosen) > 0)
====