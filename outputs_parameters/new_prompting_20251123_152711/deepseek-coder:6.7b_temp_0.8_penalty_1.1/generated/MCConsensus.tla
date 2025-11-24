---- MODULE MCConsensus ----

(***************************************************************************)
(* Defines operators on finite zero-indexed sequences, where a sequence of *)
(* length n is represented as a function whose domain is the set 0..(n-1)   *)
(* (the set {0, 1, ... , n-1}).                                             *)
(***************************************************************************)

CONSTANTS Value = {"a", "b", "c"}

VARIABLES chosen \* The chosen element

Inv == []chosen  IN Value

ISpec == ~[][Next]_chosen => []Inv

=============================================================================
====

TLC Configuration:

CONSTANTS Value = {"a", "b", "c"}
SPECIFICATION ISpec
INVARIANT Inv
CHECK_DEADLOCK FALSE
***************************************************************************)
Checking                                                                 *)
*)
Inv /\ [Next]_chosen => Inv'                                        *)
*)
which is equivalent to checking                                          *)
*)
Inv /\ [][Next]_chosen => []Inv                                      *)
*)
which asserts that Inv is an invariant of the spec                       *)
*)
Inv /\ [][Next]_chosen                                               *)
***************************************************************************)
====