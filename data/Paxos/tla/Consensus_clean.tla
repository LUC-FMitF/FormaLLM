----------------------------- MODULE Consensus ------------------------------
EXTENDS Naturals, FiniteSets, TLAPS, FiniteSetTheorems

CONSTANT Value

VARIABLE chosen

TypeOK == /\ chosen \subseteq Value
/\ IsFiniteSet(chosen)

Init == chosen = {}

Next == /\ chosen = {}
/\ \E v \in Value : chosen' = {v}

Spec == Init /\ [][Next]_chosen
-----------------------------------------------------------------------------

Inv == /\ TypeOK
/\ Cardinality(chosen) \leq 1

THEOREM Invariance == Spec => []Inv
<1>1. Init => Inv
BY FS_EmptySet DEF Init, Inv, TypeOK
<1>2. Inv /\ [Next]_chosen => Inv'
<2>1. Inv /\ Next => Inv'
BY FS_Singleton DEF Inv, TypeOK, Next
<2>2. Inv /\ UNCHANGED chosen => Inv'
BY DEF Inv, TypeOK
<2>. QED  BY <2>1, <2>2
<1>3. QED   BY <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------

Success == <>(chosen # {})
LiveSpec == Spec /\ WF_chosen(Next)

THEOREM LivenessTheorem == LiveSpec =>  Success
=============================================================================
