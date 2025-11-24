---- MODULE Consensus ----
(***************************************************************************)
(* The consensus problem requires a set of processes to choose a single     *)
(* value.  This module specifies the problem by specifying exactly what     *)
(* the requirements are for choosing a value.                               *)
(* We let the constant parameter Value be the set of all values that can    *)
(* be chosen.                                                               *)
(* We now specify the safety property of consensus as a trivial algorithm  *)
(* that describes the allowed behaviors of a consensus algorithm.  It uses  *)
(* the variable `chosen' to represent the set of all chosen values.  The    *)
(* algorithm is trivial; it allows only behaviors that contain a single    *)
(* state-change in which the variable `chosen' is changed from its initial  *)
(* value ∅ to the value {v} for an arbitrary value v in Value.  The        *)
(* algorithm itself does not specify any fairness properties, so it also    *)
(* allows a behavior in which `chosen' is not changed.  We could use a      *)
(* translator option to have the translation include a fairness requirement,*)
(* but we don't bother because it is easy enough to add it by hand to the   *)
(* safety specification that the translator produces.                       *)
(***************************************************************************)

--algorithm Consensus {
variable chosen = {};
macro Choose() { when chosen = {}; with v \in Value { chosen := {v} } }
{ lbl: while (TRUE) { Choose() } }
}

-- PlusCal translator writes the TLA+ translation of this algorithm below.
-- The formula Spec is the TLA+ specification described by the algorithm's code.
-- For now, you should just understand its two subformulas Init and Next.
-- Formula Init is the initial predicate and describes all possible initial
-- states of an execution. Formula Next is the next-state relation; it
-- describes the possible state changes (changes of the values of variables),
-- where unprimed variables represent their values in the old state and
-- primed variables represent their values in the new state.

CONSTANT Value = {v1, v2, v3}
INVARIANT TypeOK(chosen) == ((chosen = {}) OR (chosen = {v} FOR SOME v IN Value))
INVARIANT Inv(chosen) == (Cardinality(chosen) <= 1)
PROPERTY Success == (EXISTS v IN Value : (chosen = {v}))
SPECIFICATION LiveSpec == (Init /\ [][Next]_vars) /\ (Next /\ (vars' = vars))
}
====