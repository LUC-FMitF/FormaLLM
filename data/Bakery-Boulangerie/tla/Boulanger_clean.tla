------------------------------ MODULE Boulanger ----------------------------

EXTENDS Integers, TLAPS

CONSTANT N
ASSUME N \in Nat

Procs == 1..N

a \prec b == \/ a[1] < b[1]
\/ (a[1] = b[1]) /\ (a[2] < b[2])

VARIABLES num, flag, pc, unchecked, max, nxt, previous

vars == << num, flag, pc, unchecked, max, nxt, previous >>

ProcSet == (Procs)

Init ==
/\ num = [i \in Procs |-> 0]
/\ flag = [i \in Procs |-> FALSE]

/\ unchecked = [self \in Procs |-> {}]
/\ max = [self \in Procs |-> 0]
/\ nxt = [self \in Procs |-> 1]
/\ previous = [self \in Procs |-> -1]
/\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
/\ pc' = [pc EXCEPT ![self] = "e1"]
/\ UNCHANGED << num, flag, unchecked, max, nxt, previous >>

e1(self) == /\ pc[self] = "e1"
/\ \/ /\ flag' = [flag EXCEPT ![self] = ~ flag[self]]
/\ pc' = [pc EXCEPT ![self] = "e1"]
/\ UNCHANGED <<unchecked, max>>
\/ /\ flag' = [flag EXCEPT ![self] = TRUE]
/\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
/\ max' = [max EXCEPT ![self] = 0]
/\ pc' = [pc EXCEPT ![self] = "e2"]
/\ UNCHANGED << num, nxt, previous >>

e2(self) == /\ pc[self] = "e2"
/\ IF unchecked[self] # {}
THEN /\ \E i \in unchecked[self]:
/\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {i}]
/\ IF num[i] > max[self]
THEN /\ max' = [max EXCEPT ![self] = num[i]]
ELSE /\ TRUE
/\ max' = max
/\ pc' = [pc EXCEPT ![self] = "e2"]
ELSE /\ pc' = [pc EXCEPT ![self] = "e3"]
/\ UNCHANGED << unchecked, max >>
/\ UNCHANGED << num, flag, nxt, previous >>

e3(self) == /\ pc[self] = "e3"
/\ \/ /\ \E k \in Nat:
num' = [num EXCEPT ![self] = k]
/\ pc' = [pc EXCEPT ![self] = "e3"]
\/ /\ num' = [num EXCEPT ![self] = max[self] + 1]
/\ pc' = [pc EXCEPT ![self] = "e4"]
/\ UNCHANGED << flag, unchecked, max, nxt, previous >>

e4(self) == /\ pc[self] = "e4"
/\ \/ /\ flag' = [flag EXCEPT ![self] = ~ flag[self]]
/\ pc' = [pc EXCEPT ![self] = "e4"]
/\ UNCHANGED unchecked
\/ /\ flag' = [flag EXCEPT ![self] = FALSE]
/\ unchecked' = [unchecked EXCEPT ![self] = IF num[self] = 1
THEN 1..(self-1)
ELSE Procs \ {self}]
/\ pc' = [pc EXCEPT ![self] = "w1"]
/\ UNCHANGED << num, max, nxt, previous >>

w1(self) == /\ pc[self] = "w1"
/\ IF unchecked[self] # {}
THEN /\ \E i \in unchecked[self]:
nxt' = [nxt EXCEPT ![self] = i]
/\ ~ flag[nxt'[self]]
/\ previous' = [previous EXCEPT ![self] = -1]
/\ pc' = [pc EXCEPT ![self] = "w2"]
ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
/\ UNCHANGED << nxt, previous >>
/\ UNCHANGED << num, flag, unchecked, max >>

w2(self) == /\ pc[self] = "w2"
/\ IF \/ num[nxt[self]] = 0
\/ <<num[self], self>> \prec <<num[nxt[self]], nxt[self]>>
\/  /\ previous[self] # -1
/\ num[nxt[self]] # previous[self]
THEN /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {nxt[self]}]
/\ IF unchecked'[self] = {}
THEN /\ pc' = [pc EXCEPT ![self] = "cs"]
ELSE /\ pc' = [pc EXCEPT ![self] = "w1"]
/\ UNCHANGED previous
ELSE /\ previous' = [previous EXCEPT ![self] = num[nxt[self]]]
/\ pc' = [pc EXCEPT ![self] = "w2"]
/\ UNCHANGED unchecked
/\ UNCHANGED << num, flag, max, nxt >>

cs(self) == /\ pc[self] = "cs"
/\ TRUE
/\ pc' = [pc EXCEPT ![self] = "exit"]
/\ UNCHANGED << num, flag, unchecked, max, nxt, previous >>

exit(self) == /\ pc[self] = "exit"
/\ \/ /\ \E k \in Nat:
num' = [num EXCEPT ![self] = k]
/\ pc' = [pc EXCEPT ![self] = "exit"]
\/ /\ num' = [num EXCEPT ![self] = 0]
/\ pc' = [pc EXCEPT ![self] = "ncs"]
/\ UNCHANGED << flag, unchecked, max, nxt, previous >>

p(self) == ncs(self) \/ e1(self) \/ e2(self) \/ e3(self) \/ e4(self)
\/ w1(self) \/ w2(self) \/ cs(self) \/ exit(self)

Next == (\E self \in Procs: p(self))

Spec == /\ Init /\ [][Next]_vars
/\ \A self \in Procs : WF_vars((pc[self] # "ncs") /\ p(self))

MutualExclusion == \A i,j \in Procs : (i # j) => ~ /\ pc[i] = "cs"
/\ pc[j] = "cs"
-----------------------------------------------------------------------------

TypeOK == /\ num \in [Procs -> Nat]
/\ flag \in [Procs -> BOOLEAN]
/\ unchecked \in [Procs -> SUBSET Procs]
/\ max \in [Procs -> Nat]
/\ nxt \in [Procs -> Procs]
/\ pc \in [Procs -> {"ncs", "e1", "e2", "e3",
"e4", "w1", "w2", "cs", "exit"}]
/\ previous \in [Procs -> Nat \cup {-1}]

Before(i,j) == /\ num[i] > 0
/\ \/ pc[j] \in {"ncs", "e1", "exit"}
\/ /\ pc[j] = "e2"
/\ \/ i \in unchecked[j]
\/ max[j] >= num[i]
\/ (j > i) /\ (max[j] + 1 = num[i])
\/ /\ pc[j] = "e3"
/\ \/ max[j] >= num[i]
\/ (j > i) /\ (max[j] + 1 = num[i])
\/ /\ pc[j] \in {"e4", "w1", "w2"}
/\ <<num[i],i>> \prec <<num[j],j>>
/\ (pc[j] \in {"w1", "w2"}) => (i \in unchecked[j])
\/ /\ num[i] = 1
/\ i < j

Inv == /\ TypeOK
/\ \A i \in Procs :
/\ (pc[i] \in {"ncs", "e1", "e2"}) => (num[i] = 0)
/\ (pc[i] \in {"e4", "w1", "w2", "cs"}) => (num[i] # 0)
/\ (pc[i] \in {"e2", "e3"}) => flag[i]
/\ (pc[i] = "w2") => (nxt[i] # i)
/\ (pc[i] \in {"e2", "w1", "w2"}) => i \notin unchecked[i]
/\ (pc[i] \in {"w1", "w2"}) =>
\A j \in (Procs \ unchecked[i]) \ {i} : Before(i, j)
/\ /\ pc[i] = "w2"
/\ \/ (pc[nxt[i]] = "e2") /\ (i \notin unchecked[nxt[i]])
\/ pc[nxt[i]] = "e3"
=> max[nxt[i]] >= num[i]
/\ /\ pc[i] = "w2"
/\ previous[i] # -1
/\ previous[i] # num[nxt[i]]
/\ pc[nxt[i]] \in {"e4", "w1", "w2", "cs"}
=> Before(i, nxt[i])
/\ (pc[i] = "cs") => \A j \in Procs \ {i} : Before(i, j)
-----------------------------------------------------------------------------

THEOREM Spec => []MutualExclusion
<1> USE N \in Nat DEFS Procs, TypeOK, Before, \prec, ProcSet

<1>1. Init => Inv
BY SMT DEF Init, Inv

<1>2. Inv /\ [Next]_vars => Inv'
<2> SUFFICES ASSUME Inv,
[Next]_vars
PROVE  Inv'
OBVIOUS
<2>1. ASSUME NEW self \in Procs,
ncs(self)
PROVE  Inv'
BY <2>1, Z3 DEF ncs, Inv
<2>2. ASSUME NEW self \in Procs,
e1(self)
PROVE  Inv'
<3>. /\ pc[self] = "e1"
/\ UNCHANGED << num, nxt, previous >>
BY <2>2 DEF e1
<3>1. CASE /\ flag' = [flag EXCEPT ![self] = ~ flag[self]]
/\ pc' = [pc EXCEPT ![self] = "e1"]
/\ UNCHANGED <<unchecked, max>>
BY <3>1 DEF Inv
<3>2. CASE /\ flag' = [flag EXCEPT ![self] = TRUE]
/\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
/\ max' = [max EXCEPT ![self] = 0]
/\ pc' = [pc EXCEPT ![self] = "e2"]
BY <3>2 DEF Inv
<3>. QED  BY <3>1, <3>2, <2>2 DEF e1
<2>3. ASSUME NEW self \in Procs,
e2(self)
PROVE  Inv'
<3>. /\ pc[self] = "e2"
/\ UNCHANGED << num, flag, nxt, previous >>
BY <2>3 DEF e2
<3>1. ASSUME NEW  i \in unchecked[self],
unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {i}],
num[i] > max[self],
max' = [max EXCEPT ![self] = num[i]],
pc' = [pc EXCEPT ![self] = "e2"]
PROVE  Inv'
BY <3>1, Z3 DEF Inv
<3>2. ASSUME NEW  i \in unchecked[self],
unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {i}],
~(num[i] > max[self]),
max' = max,
pc' = [pc EXCEPT ![self] = "e2"]
PROVE  Inv'
BY <3>2, Z3 DEF Inv
<3>3. CASE /\ unchecked[self] = {}
/\ pc' = [pc EXCEPT ![self] = "e3"]
/\ UNCHANGED << unchecked, max >>
BY <3>3, Z3 DEF Inv
<3>. QED  BY <3>1, <3>2, <3>3, <2>3 DEF e2
<2>4. ASSUME NEW self \in Procs,
e3(self)
PROVE  Inv'
<3>. /\ pc[self] = "e3"
/\ UNCHANGED << flag, unchecked, max, nxt, previous >>
BY <2>4 DEF e3
<3>1. CASE /\ \E k \in Nat: num' = [num EXCEPT ![self] = k]
/\ pc' = [pc EXCEPT ![self] = "e3"]
BY <3>1, Z3 DEF Inv
<3>2. CASE /\ num' = [num EXCEPT ![self] = max[self] + 1]
/\ pc' = [pc EXCEPT ![self] = "e4"]
BY <3>2, Z3 DEF Inv
<3>. QED  BY <3>1, <3>2, <2>4 DEF e3
<2>5. ASSUME NEW self \in Procs,
e4(self)
PROVE  Inv'
<3>. /\ pc[self] = "e4"
/\ UNCHANGED << num, max, nxt, previous >>
BY <2>5 DEF e4
<3>1. CASE /\ flag' = [flag EXCEPT ![self] = ~ flag[self]]
/\ pc' = [pc EXCEPT ![self] = "e4"]
/\ UNCHANGED unchecked
BY <3>1, Z3 DEF Inv
<3>2. CASE /\ flag' = [flag EXCEPT ![self] = FALSE]
/\ num[self] = 1
/\ unchecked' = [unchecked EXCEPT ![self] = 1..(self-1)]
/\ pc' = [pc EXCEPT ![self] = "w1"]
BY <3>2, Z3 DEF Inv
<3>3. CASE /\ flag' = [flag EXCEPT ![self] = FALSE]
/\ num[self] # 1
/\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
/\ pc' = [pc EXCEPT ![self] = "w1"]
BY <3>3, Z3 DEF Inv
<3>. QED  BY <3>1, <3>2, <3>3, <2>5 DEF e4
<2>6. ASSUME NEW self \in Procs,
w1(self)
PROVE  Inv'
<3>. /\ pc[self] = "w1"
/\ UNCHANGED << num, flag, unchecked, max >>
BY <2>6 DEF w1
<3>1. CASE /\ unchecked[self] # {}
/\ \E i \in unchecked[self]:
nxt' = [nxt EXCEPT ![self] = i]
/\ ~ flag[nxt'[self]]
/\ previous' = [previous EXCEPT ![self] = -1]
/\ pc' = [pc EXCEPT ![self] = "w2"]
BY <3>1, Z3 DEF Inv
<3>2. CASE /\ unchecked[self] = {}
/\ pc' = [pc EXCEPT ![self] = "cs"]
/\ UNCHANGED << nxt, previous >>
BY <3>2, Z3 DEF Inv
<3>. QED  BY <3>1, <3>2, <2>6 DEF w1
<2>7. ASSUME NEW self \in Procs,
w2(self)
PROVE  Inv'
<3>. /\ pc[self] = "w2"
/\ UNCHANGED << num, flag, max, nxt >>
BY <2>7 DEF w2
<3>1. CASE /\ \/ num[nxt[self]] = 0
\/ <<num[self], self>> \prec <<num[nxt[self]], nxt[self]>>
\/  /\ previous[self] # -1
/\ num[nxt[self]] # previous[self]
/\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {nxt[self]}]
/\ unchecked'[self] = {}
/\ pc' = [pc EXCEPT ![self] = "cs"]
/\ UNCHANGED previous
BY <3>1, Z3 DEF Inv
<3>2. CASE /\ \/ num[nxt[self]] = 0
\/ <<num[self], self>> \prec <<num[nxt[self]], nxt[self]>>
\/  /\ previous[self] # -1
/\ num[nxt[self]] # previous[self]
/\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {nxt[self]}]
/\ unchecked'[self] # {}
/\ pc' = [pc EXCEPT ![self] = "w1"]
/\ UNCHANGED previous
BY <3>2, Z3 DEF Inv
<3>3. CASE /\ ~ \/ num[nxt[self]] = 0
\/ <<num[self], self>> \prec <<num[nxt[self]], nxt[self]>>
\/  /\ previous[self] # -1
/\ num[nxt[self]] # previous[self]
/\ previous' = [previous EXCEPT ![self] = num[nxt[self]]]
/\ pc' = [pc EXCEPT ![self] = "w2"]
/\ UNCHANGED unchecked
BY <3>3, Z3 DEF Inv
<3>. QED  BY <3>1, <3>2, <3>3, <2>7 DEF w2
<2>8. ASSUME NEW self \in Procs,
cs(self)
PROVE  Inv'
BY <2>8, Z3 DEF cs, Inv
<2>9. ASSUME NEW self \in Procs,
exit(self)
PROVE  Inv'
<3>. /\ pc[self] = "exit"
/\ UNCHANGED << flag, unchecked, max, nxt, previous >>
BY <2>9 DEF exit
<3>1. CASE /\ \E k \in Nat: num' = [num EXCEPT ![self] = k]
/\ pc' = [pc EXCEPT ![self] = "exit"]
BY <3>1, Z3 DEF Inv
<3>2. CASE /\ num' = [num EXCEPT ![self] = 0]
/\ pc' = [pc EXCEPT ![self] = "ncs"]
BY <3>2, Z3 DEF Inv
<3>. QED  BY <3>1, <3>2, <2>9 DEF exit
<2>10. CASE UNCHANGED vars
BY <2>10, Z3 DEF vars, Inv
<2>11. QED
BY <2>1, <2>10, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF Next, p

<1>3. Inv => MutualExclusion
BY SMT DEF Inv, MutualExclusion

<1>4. QED
BY <1>1, <1>2, <1>3, PTL DEF Spec
------------------------------------------------------------------------------
Trying(i) == pc[i] = "e1"
InCS(i)   == pc[i] = "cs"
DeadlockFree == (\E i \in Procs : Trying(i)) ~> (\E i \in Procs : InCS(i))
StarvationFree == \A i \in Procs : Trying(i) ~> InCS(i)
=============================================================================
