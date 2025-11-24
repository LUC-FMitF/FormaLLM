---- MODULE MCConsensus ----

(***************************************************************************)
(* Checking                                                                *)
(* )
(* Inv /\ [Next]_chosen 		=> Inv'					*)
(* )
(* which is equivalent to checking                                          *)
(* )
(* Inv /\ [][Next]_chosen 		=> []Inv 					*)
(* )
(* which asserts that Inv is an invariant of the spec                       *)
(* )
(* Inv /\ [][Next]_chosen                                               *)
(***************************************************************************)

CONSTANTS Value = {"a", "b", "c"}
VARIABLES chosen

Inv == \* The invariant
  [x \in Value |-> x \in chosen]

Next == \* The next-state relation
  \/ \E x \in Value : chosen' = chosen \cup {x}

ISpec == \* Initialize state with Init and transition with Next
  Inv /\ [][Next]_chosen

=============================================================================
====

(* TLC Configuration *)
(* CONSTANTS Value = {"a", "b", "c"} *)
(* SPECIFICATION ISpec *)
(* INVARIANT Inv *)
(* CHECK_DEADLOCK FALSE *)

This TLA+ module defines a simple spec where the set of chosen values is an invariant. The next-state relation allows us to choose a new value to add to the set of chosen values. The invariant asserts that the chosen set contains only values from the set of possible values. The spec is initialized with the invariant and the next-state relation. The TLC configuration also specifies that we want to check for deadlocks but we don't want to check for them in this spec.
====