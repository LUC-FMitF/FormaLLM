---- MODULE Consensus ----
(***************************************************************************)
(* The consensus problem requires a set of processes to choose a single     *)
(* value.  This module specifies the problem by specifying exactly what     *)
(* the requirements are for choosing a value.                               *)
(***************************************************************************)

EXTENDS FiniteSets, Naturals, Sequences
  
CONSTANT Value \in PowerSet(UNIVERSE) (* The set of all values that can    *)
                                      (* be chosen.                         *)

VARIABLE chosen \in PowerSet(Value) (* The variable `chosen' represents the *)
                                   (* set of all chosen values.             *)

(* Macro to describe the action of changing the value of `chosen' from {}   *)
(* to {v} for a nondeterministically chosen v in the set Value.           *)
MACRO Choose() ==
  when chosen = {} /\ (v \in Value)
    [chosen := {v}]

OPERATOR Next(vars) == 
  EXTENSION OF ([Choose]_vars)

(* The algorithm stops after executing a Choose() action.                  *)
ALGORITHM Consensus ==
  <<Init, Next>> /\ ([][Next]_vars == Init /\ Next /\ ~(chosen = {}))

(* We put the Choose() action inside a `while' statement that loops       *)
(* forever.  Of course, only a single Choose() action can be performed in   *)
(* any execution.                                                         *)
OPERATOR LiveSpec == ([Consensus]_vars /\ ~(chosen = {}))

(* The temporal formula Success asserts that some value is chosen.          *)
DEFINE SUCCESS == EXISTS {v \in Value} (chosen = {v})

(* We now prove that LiveSpec implies that Success holds eventually.       *)
THEOREM Liveness == ~(LiveSpec /\ ~SUCCESS) ==> ?n ELEMENTOF Naturals : 
  FORALL {i \in n..Inf} (FORALL {vars \in StateOf(LiveSpec, i)} SUCCESS)
====