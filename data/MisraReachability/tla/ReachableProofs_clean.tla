-------------------------- MODULE ReachableProofs --------------------------

EXTENDS Reachable, ReachabilityProofs, TLAPS

THEOREM Thm1 == Spec => []Inv1

<1>1. Init => Inv1
BY RootAssump DEF Init, Inv1, TypeOK
<1>2. Inv1 /\ [Next]_vars => Inv1'

<2> SUFFICES ASSUME Inv1,
[Next]_vars
PROVE  Inv1'
OBVIOUS
<2>1. CASE a
BY <2>1, SuccAssump DEF Inv1, TypeOK, a
<2>2. CASE UNCHANGED vars
BY <2>2 DEF Inv1, TypeOK, vars
<2>3. QED
BY <2>1, <2>2 DEF Next, Terminating
<1>3. QED
BY <1>1, <1>2, PTL DEF Spec

THEOREM Thm2 == Spec => [](TypeOK /\ Inv2)

<1>1. Inv1 => TypeOK /\ Inv2
BY Reachable1 DEF Inv1, Inv2, TypeOK
<1> QED
BY <1>1, Thm1, PTL

THEOREM Thm3 == Spec => []Inv3

<1>1. Init => Inv3
BY RootAssump DEF Init, Inv3, TypeOK, Reachable
<1>2. TypeOK /\ TypeOK' /\ Inv2 /\ Inv2' /\ Inv3 /\ [Next]_vars => Inv3'

<2> SUFFICES ASSUME TypeOK,
TypeOK',
Inv2,
Inv2',
Inv3,
[Next]_vars
PROVE  Inv3'
OBVIOUS

<2>1. /\ Reachable' = Reachable
/\ ReachableFrom(vroot)' = ReachableFrom(vroot')
/\ ReachableFrom(marked \cup vroot)' = ReachableFrom(marked' \cup vroot')
OBVIOUS
<2>2. CASE a

<3> USE <2>2 DEF a

<3>1. CASE vroot = {}
BY <2>1, <3>1 DEF Inv3, TypeOK
<3>2. CASE vroot # {}

<4>1. PICK v \in vroot :
IF v \notin marked
THEN /\ marked' = (marked \cup {v})
/\ vroot' = vroot \cup Succ[v]
ELSE /\ vroot' = vroot \ {v}
/\ UNCHANGED marked
BY <3>2

<4>2. CASE v \notin marked

<5>1. /\ ReachableFrom(vroot') = ReachableFrom(vroot)
/\ v \in ReachableFrom(vroot)
BY <4>1, <4>2, Reachable2 DEF TypeOK
<5>2. QED
BY <5>1, <4>1, <4>2, <5>1, <2>1 DEF Inv3
<4>3. CASE v \in marked

<5>1. marked' \cup vroot' = marked \cup vroot
BY <4>1, <4>3
<5>2. QED
BY <5>1, <2>1 DEF Inv2, Inv3
<4>4. QED
BY <4>2, <4>3
<3>3. QED
BY <3>1, <3>2
<2>3. CASE UNCHANGED vars

BY <2>1, <2>3 DEF Inv3, TypeOK, vars
<2>4. QED
BY <2>2, <2>3 DEF Next, Terminating
<1>3. QED
BY <1>1, <1>2, Thm2, PTL DEF Spec

THEOREM Spec => []((pc = "Done") => (marked = Reachable))

<1>1. Inv1 => ((pc = "Done") => (vroot = {}))
BY DEF Inv1, TypeOK
<1>2. Inv3 /\ (vroot = {}) => (marked = Reachable)
BY Reachable3 DEF Inv3
<1>3. QED
BY <1>1, <1>2, Thm1, Thm3, PTL
=============================================================================
