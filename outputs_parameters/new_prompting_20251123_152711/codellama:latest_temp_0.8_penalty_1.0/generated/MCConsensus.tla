---- MODULE MCConsensus ----

(***************************************************************************)
(*                                                                         *)
(*       Checking                                                          *)
(*                                                                         *)
(***************************************************************************)
CONSTANTS Value = {"a", "b", "c"}   \* The set of all values.
VARIABLES chosenValue : VALUE        \* A variable to keep track of the chosen value.
------------------------------------------------------------------------------
ISpec ==                              \* The spec is a temporal formula: ISpec_v = v /\ [][Next]_<<chosenValue>>
    /\ chosenValue \in Value           \* Choose one value from {a, b, c}.
    /\ []{}         :> Next            \* Apply the next-state relation.
INIT ==                               \* The initial predicate.
    /\ chosenValue = "a"
    
Inv ==  \* An invariant that is always true at any state in the spec.
/\ []ISpec_v
=============================================================================
====