---- MODULE Consensus ----
(***************************************************************************)
(* The consensus problem requires a set of processes to choose a single     *)
(* value. This module specifies the problem by specifying exactly what      *)
(* the requirements are for choosing a value.                               *)
(***************************************************************************)

(* We let the constant parameter Value be the set of all values that can    *)
(* be chosen.                                                               *)
(***************************************************************************)

CONSTANT Value = {v1, v2, v3} (* The possible values to choose from *)

VARIABLE chosen = {} (* Initially no value has been chosen *)

OPERATION Choose() = 
  IF cardinality(chosen) = 0 THEN
    WITH v \in Value DO
      chosen := {v} (* Choose a single value *)

(* The algorithm stops after executing a Choose() action. Technically,
   the algorithm deadlocks after executing a Choose() action because
   control is at a statement whose execution is never enabled. Formally,
   termination is simply deadlock that we want to happen. However, adding 
   the 'while' loop makes the TLA+ representation of the algorithm a tiny bit simpler. *)
OPERATION Algorithm() = 
  WHILE TRUE DO
    Choose() (* Execute the Choose operation indefinitely *)

(* The PlusCal translator writes the TLA+ translation of this algorithm
   below. The formula Spec is the TLA+ specification described by the
   algorithm's code. For now, you should just understand its two
   subformulas Init and Next. Formula Init is the initial predicate and
   describes all possible initial states of an execution. Formula Next is
   the next-state relation; it describes the possible state changes
   (changes of the values of variables), where unprimed variables
   represent their values in the old state and primed variables represent
   their values in the new state. *)

(* We now prove the safety property that at most one value is chosen. 
   The formula Spec asserts that all possible initial states are allowed, 
   and each step satisfies either Next (so it is a step allowed by the 
   next-state relation) or it is a "stuttering step" that leaves all the 
   variables unchanged. *)
SPECIFICATION Spec = 
  Init /\ [][Next]_vars
WHERE vars = <chosen, pc> (* where pc stands for program counter *)

(* We now prove that Inv is an invariant, meaning that it is true in every 
   state in every behavior. Before trying to prove it, we should first    
   use TLC to check that it is true. It's hardly worth bothering to       
   either check or prove the obvious fact that Inv is an invariant, but    
   it's a nice tiny exercise. Model checking is instantaneous when Value  
   is set to any small finite set. *)
INVARIANT Inv = TypeOK /\ (cardinality(chosen) <= 1)
(* We now define LiveSpec to be the algorithm's specification with the     
   added fairness condition of weak fairness of the next-state relation,   
   which asserts that execution does not stop if some action is enabled. *)
SPECIFICATION LiveSpec = Spec /\ ENABLED(Choose) (* weak fairness *)
(* The temporal formula Success asserts that some value is chosen. 
   This means that, in every behavior satisfying LiveSpec, some value will 
   be chosen. We now define LiveSpec to be the algorithm's specification with 
   the added fairness condition of weak fairness of the next-state relation, 
   which asserts that execution does not stop if some action is enabled. *)
FORMULA Success = EXISTS v \in Value . (chosen = {v}) (* Some value has been chosen *)
(* Here is our proof that Livespec implies Success. The overall approach   
   to the proof follows the rule WF1 discussed in                           *)
(***************************************************************************)
====