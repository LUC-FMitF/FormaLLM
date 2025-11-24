---- MODULE MCConsensus ----
module ISpec

CONSTANTS Value = {"a", "b", "c"}

VARIABLES chosen, spec

INITIAL 
chosen = "a"
spec = "a"

INVARIANT Inv
/\ chosen ∈ Value
/\ spec ∈ Value

ACTION chosen = "b"
ACTION chosen = "c"

CHECK ISpec
/\ chosen ∈ Value
/\ spec ∈ Value
/\ chosen = spec

END
====