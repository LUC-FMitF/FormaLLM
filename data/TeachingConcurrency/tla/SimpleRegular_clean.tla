--------------------------- MODULE SimpleRegular ---------------------------

EXTENDS Integers, TLAPS

CONSTANT N
ASSUME NAssump ==  (N \in Nat) /\ (N > 0)

VARIABLES x, y, pc

vars == << x, y, pc >>

ProcSet == (0..N-1)

Init ==
/\ x = [i \in 0..(N-1) |-> {0}]
/\ y = [i \in 0..(N-1) |-> 0]
/\ pc = [self \in ProcSet |-> "a1"]

a1(self) == /\ pc[self] = "a1"
/\ x' = [x EXCEPT ![self] = {0,1}]
/\ pc' = [pc EXCEPT ![self] = "a2"]
/\ y' = y

a2(self) == /\ pc[self] = "a2"
/\ x' = [x EXCEPT ![self] = {1}]
/\ pc' = [pc EXCEPT ![self] = "b"]
/\ y' = y

b(self) == /\ pc[self] = "b"
/\ \E v \in x[(self-1) % N]:
y' = [y EXCEPT ![self] = v]
/\ pc' = [pc EXCEPT ![self] = "Done"]
/\ x' = x

proc(self) == a1(self) \/ a2(self) \/ b(self)

Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
/\ UNCHANGED vars

Next == (\E self \in 0..N-1: proc(self))
\/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

-----------------------------------------------------------------------------

PCorrect == (\A i \in 0..(N-1) : pc[i] = "Done") =>
(\E i \in 0..(N-1) : y[i] = 1)

TypeOK == /\ x \in [0..(N-1) -> (SUBSET {0, 1}) \ {{}}]
/\ y \in [0..(N-1) -> {0,1}]
/\ pc \in [0..(N-1) -> {"a1", "a2", "b", "Done"}]

Inv ==  /\ TypeOK
/\ \A i \in 0..(N-1) : (pc[i] \in {"b", "Done"}) => (x[i] = {1})
/\ \/ \E i \in 0..(N-1) : pc[i] /= "Done"
\/ \E i \in 0..(N-1) : y[i] = 1

THEOREM Spec => []PCorrect
<1> USE NAssump DEF ProcSet
<1>1. Init => Inv
<2>1. Init => 0 \in 0..(N-1) /\ pc[0] /= "Done"
BY DEF Init
<2>. QED  BY <2>1 DEF Init, Inv, TypeOK
<1>2. Inv /\ [Next]_vars => Inv'
<2> SUFFICES ASSUME Inv,
[Next]_vars
PROVE  Inv'
OBVIOUS
<2>1. ASSUME NEW self \in 0..N-1,
a1(self)
PROVE  Inv'
BY <2>1 DEF a1, Inv, TypeOK
<2>2. ASSUME NEW self \in 0..N-1,
a2(self)
PROVE  Inv'
BY <2>2 DEF a2, Inv, TypeOK
<2>3. ASSUME NEW self \in 0..N-1,
b(self)
PROVE  Inv'
<3> SUFFICES ASSUME NEW v \in x[(self-1) % N],
y' = [y EXCEPT ![self] = v]
PROVE  Inv'
BY <2>3 DEF b
<3> QED
BY <2>3, Z3 DEF b, Inv, TypeOK
<2>4. CASE UNCHANGED vars
BY <2>4 DEF TypeOK, Inv, vars
<2>5. QED
BY <2>1, <2>2, <2>3, <2>4 DEF Next, Terminating, proc
<1>3. Inv => PCorrect
BY DEF Inv, TypeOK, PCorrect
<1>4. QED
BY <1>1, <1>2, <1>3, PTL DEF Spec
======================================
