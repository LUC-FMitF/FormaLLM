----------------------------- MODULE Consensus ------------------------------

EXTENDS Naturals, FiniteSets, FiniteSetTheorems, TLAPS

CONSTANT Value

VARIABLE chosen

vars == << chosen >>

Init ==
/\ chosen = {}

Next == /\ chosen = {}
/\ \E v \in Value:
chosen' = {v}

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

TypeOK == /\ chosen \subseteq Value
/\ IsFiniteSet(chosen)

Inv == /\ TypeOK
/\ Cardinality(chosen) \leq 1

LEMMA InductiveInvariance ==
Inv /\ [Next]_vars => Inv'
<1>. SUFFICES ASSUME Inv, [Next]_vars
PROVE  Inv'
OBVIOUS
<1>1. CASE Next

BY <1>1, FS_EmptySet, FS_Singleton DEF Inv, TypeOK, Next
<1>2. CASE vars' = vars
BY <1>2 DEF Inv, TypeOK, vars
<1>3. QED
BY <1>1, <1>2 DEF Next

THEOREM Invariance == Spec => []Inv
<1>1.  Init => Inv
BY FS_EmptySet DEF Init, Inv, TypeOK
<1>2.  QED
BY PTL, <1>1, InductiveInvariance DEF Spec

-----------------------------------------------------------------------------

LiveSpec == Spec /\ WF_vars(Next)
Success == <>(chosen # {})

ASSUME ValueNonempty == Value # {}

LEMMA EnabledNext ==
(ENABLED <<Next>>_vars) <=> (chosen = {})
BY ValueNonempty, ExpandENABLED DEF Next, vars

THEOREM LiveSpec => Success
<1>1. [][Next]_vars /\ WF_vars(Next) => [](Init => Success)
<2>1. Init' \/ (chosen # {})'
BY DEF Init
<2>2. Init /\ <<Next>>_vars => (chosen # {})'
BY DEF Init, Next, vars
<2>3. Init => ENABLED <<Next>>_vars
BY EnabledNext DEF Init
<2>. QED  BY <2>1, <2>2, <2>3, PTL DEF Success
<1>2. QED  BY <1>1, PTL DEF LiveSpec, Spec, Success

-----------------------------------------------------------------------------

THEOREM LiveSpecEquals ==
LiveSpec <=> Spec /\ ([]<><<Next>>_vars \/ []<>(chosen # {}))
<1>1. (chosen # {}) <=> ~(chosen = {})
OBVIOUS
<1>2. ([]<>~ENABLED <<Next>>_vars) <=> []<>(chosen # {})
BY <1>1, EnabledNext, PTL
<1>4. QED
BY <1>2, PTL DEF LiveSpec
=============================================================================
