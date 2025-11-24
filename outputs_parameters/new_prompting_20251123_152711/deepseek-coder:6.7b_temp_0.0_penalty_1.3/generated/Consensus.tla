---- MODULE Consensus ----
EXTENDS FiniteSets, Naturals, Sequences
CONSTANTS Value = {v1, v2, v3}
VARIABLES chosen <<chosen>>, pc

Init == [pc  IN DOMAIN <<pc>>] /\ (~(Value \ Cardinality(Value)))
Next == ([pc'=<<pc>>, chosen'=IF pc = {} THEN {v} ELSE chosen UNION {v}] : v \in Value)
Spec == Init /\ []([Next])_<><<chosen, pc>>

Inv == (Cardinality(chosen) <= 1)
TypeOK == ((~(Value \ Cardinality(Value))) /\ Inv)
Success == EXISTS {v} : v \in chosen
LiveSpec == Spec /\ ENABLED({Choose()})

====