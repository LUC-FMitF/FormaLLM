---------------------------- MODULE FindHighest -----------------------------

EXTENDS Sequences, Naturals, Integers, TLAPS

VARIABLES f, h, i, pc

max(a, b) == IF a >= b THEN a ELSE b

vars == << f, h, i, pc >>

Init ==
/\ f \in Seq(Nat)
/\ h = -1
/\ i = 1
/\ pc = "lb"

lb == /\ pc = "lb"
/\ IF i <= Len(f)
THEN /\ h' = max(h, f[i])
/\ i' = i + 1
/\ pc' = "lb"
ELSE /\ pc' = "Done"
/\ UNCHANGED << h, i >>
/\ f' = f

Terminating == pc = "Done" /\ UNCHANGED vars

Next == lb
\/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

TypeOK ==
/\ f \in Seq(Nat)
/\ i \in 1..(Len(f) + 1)
/\ i \in Nat
/\ h \in Nat \cup {-1}

THEOREM TypeInvariantHolds == Spec => []TypeOK

PROOF

<1>a. Init => TypeOK
BY DEFS Init, TypeOK

<1>b. TypeOK /\ UNCHANGED vars => TypeOK'
BY DEFS TypeOK, vars

<1>c. TypeOK /\ Next => TypeOK'
<2>a. TypeOK /\ lb => TypeOK'
BY DEFS TypeOK, lb, max
<2>b. TypeOK /\ Terminating => TypeOK'
BY DEFS TypeOK, Terminating, vars
<2> QED BY <2>a, <2>b DEF Next
<1> QED BY PTL, <1>a, <1>b, <1>c DEF Spec

InductiveInvariant ==
\A idx \in 1..(i - 1) : f[idx] <= h

THEOREM InductiveInvariantHolds == Spec => []InductiveInvariant
PROOF
<1>a. Init => InductiveInvariant
BY DEFS Init, InductiveInvariant
<1>b. InductiveInvariant /\ UNCHANGED vars => InductiveInvariant'
BY DEFS InductiveInvariant, vars
<1>c. InductiveInvariant /\ TypeOK /\ TypeOK' /\ Next => InductiveInvariant'
<2>a. InductiveInvariant /\ Terminating => InductiveInvariant'
BY DEFS InductiveInvariant, Terminating, vars
<2>b. InductiveInvariant /\ TypeOK /\ lb => InductiveInvariant'
BY DEFS InductiveInvariant, TypeOK, lb, max
<2> QED BY <2>a, <2>b DEF Next

<1> QED BY PTL, <1>a, <1>b, <1>c, TypeInvariantHolds DEF Spec

DoneIndexValue == pc = "Done" => i = Len(f) + 1

THEOREM DoneIndexValueThm == Spec => []DoneIndexValue
PROOF
<1>a. Init => DoneIndexValue
BY DEF Init, DoneIndexValue
<1>b. DoneIndexValue /\ UNCHANGED vars => DoneIndexValue'
BY DEFS DoneIndexValue, vars
<1>c. DoneIndexValue /\ TypeOK /\ Next => DoneIndexValue'
<2>a. DoneIndexValue /\ Terminating => DoneIndexValue'
BY DEFS DoneIndexValue, Terminating, vars
<2>b. DoneIndexValue /\ TypeOK /\ lb => DoneIndexValue'
BY DEFS DoneIndexValue, TypeOK, lb
<2> QED BY <2>a, <2>b DEF Next
<1> QED BY PTL, <1>a, <1>b, <1>c, TypeInvariantHolds DEF Spec

Correctness ==
pc = "Done" =>
\A idx \in DOMAIN f : f[idx] <= h

THEOREM IsCorrect == Spec => []Correctness
<1>1. TypeOK /\ InductiveInvariant /\ DoneIndexValue => Correctness
BY DEF TypeOK, InductiveInvariant, DoneIndexValue, Correctness
<1>. QED
BY <1>1, TypeInvariantHolds, InductiveInvariantHolds, DoneIndexValueThm, PTL

=============================================================================
