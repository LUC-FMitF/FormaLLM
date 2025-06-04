------------------------- MODULE ReachabilityProofs -------------------------

EXTENDS Reachability, NaturalsInduction

LEMMA Reachable0 ==
\A S \in SUBSET Nodes :
\A n \in S : n \in ReachableFrom(S)

<1> SUFFICES ASSUME NEW S \in SUBSET Nodes,
NEW n \in S
PROVE  n \in ReachableFrom(S)
OBVIOUS

<1>1. ExistsPath(n,n)

<2> USE DEF ExistsPath, IsPathFromTo
<2> WITNESS <<n>> \in Seq(Nodes)
<2> QED
OBVIOUS
<1>2. QED
PROOF BY <1>1 DEF ReachableFrom, ExistsPath

LEMMA Reachable1 ==
\A S, T \in SUBSET Nodes :
(\A n \in S : Succ[n] \subseteq (S \cup T))
=> (S \cup ReachableFrom(T)) = ReachableFrom(S \cup T)

<1> SUFFICES ASSUME NEW S \in SUBSET Nodes, NEW T \in SUBSET Nodes,
\A n \in S : Succ[n] \subseteq (S \cup T)
PROVE  (S \cup ReachableFrom(T)) = ReachableFrom(S \cup T)
OBVIOUS

<1>1. (S \cup ReachableFrom(T)) \subseteq ReachableFrom(S \cup T)

<2>1. \A n \in S : n \in ReachableFrom(S)
BY Reachable0
<2>2. QED
BY <2>1 DEF ReachableFrom
<1>2. ReachableFrom(S \cup T) \subseteq (S \cup ReachableFrom(T))

<2> SUFFICES ASSUME NEW n \in ReachableFrom(S)
PROVE  n \in S \cup ReachableFrom(T)
BY  DEF ReachableFrom

<2> DEFINE R(i) ==
\A m \in S, q \in Nodes :
(\E p \in Seq(Nodes) : /\ IsPathFromTo(p,m,q)
/\ Len(p) = i+1)
=> (q \in S \cup ReachableFrom(T))
<2>1. \A i \in Nat : R(i)

<3>1. R(0)

<4> SUFFICES ASSUME NEW m \in S, NEW q \in Nodes,
NEW p \in Seq(Nodes),
/\ IsPathFromTo(p,m,q)
/\ Len(p) = 0+1
PROVE  q \in S \cup ReachableFrom(T)
OBVIOUS
<4> QED
BY DEF IsPathFromTo
<3>2. ASSUME NEW i \in Nat, R(i)
PROVE  R(i+1)

<4> SUFFICES ASSUME NEW m \in S, NEW q \in Nodes,
NEW p \in Seq(Nodes),
/\ IsPathFromTo(p,m,q)
/\ Len(p) = (i+1)+1
PROVE  q \in S \cup ReachableFrom(T)
BY DEF R

<4>1. /\ Tail(p) \in Seq(Nodes)
/\ IsPathFromTo(Tail(p), p[2], q)
/\ Len(Tail(p)) = i+1
BY  DEF IsPathFromTo

<4>2. p[2] \in S \cup T
BY DEF IsPathFromTo

<4>3. CASE p[2] \in S
BY <3>2, <4>1, <4>3
<4>4. CASE p[2] \in T
BY <4>1, <4>4 DEF ReachableFrom, ExistsPath
<4>5. QED
BY <4>2, <4>3, <4>4
<3> HIDE DEF R
<3>3. QED
BY <3>1, <3>2, NatInduction

<2>2. PICK m \in S, p \in Seq(Nodes) :
IsPathFromTo(p,m,n)
BY DEF ReachableFrom, ExistsPath

<2>3. R(Len(p)-1) => n \in S \cup ReachableFrom(T)
BY <2>2 DEF IsPathFromTo

<2> HIDE DEF R

<2>4. QED
BY <2>1, <2>2, <2>3 DEF IsPathFromTo
<1>3. QED
BY <1>1, <1>2

LEMMA Reachable2 ==
\A S \in SUBSET Nodes: \A n \in S :
/\ ReachableFrom(S) = ReachableFrom(S \cup Succ[n])
/\ n \in ReachableFrom(S)
<1> SUFFICES ASSUME NEW S \in SUBSET Nodes,
NEW n \in S
PROVE  /\ ReachableFrom(S) = ReachableFrom(S \cup Succ[n])
/\ n \in ReachableFrom(S)
OBVIOUS
<1>1. ReachableFrom(S) = ReachableFrom(S \cup Succ[n])

<2>1. ReachableFrom(S) \subseteq ReachableFrom(S \cup Succ[n])

BY DEF ReachableFrom
<2>2.ReachableFrom(S \cup Succ[n])  \subseteq ReachableFrom(S)

<3> SUFFICES ReachableFrom(Succ[n]) \subseteq ReachableFrom(S)
BY DEF ReachableFrom
<3> SUFFICES ASSUME NEW m \in Succ[n], NEW o \in Nodes,
ExistsPath(m, o)
PROVE  ExistsPath(n, o)
BY DEF ReachableFrom
<3>1. PICK p \in Seq(Nodes) : IsPathFromTo(p, m, o)
BY DEF ExistsPath
<3> DEFINE q == <<n>> \o p
<3>2. (q \in Seq(Nodes)) /\ IsPathFromTo(q, n, o)
BY <3>1, SuccAssump  DEF IsPathFromTo
<3>3. QED
BY <3>2 DEF ExistsPath
<2>3. QED
BY <2>1, <2>2

<1>2. n \in ReachableFrom(S)
BY Reachable0
<1>3. QED
BY <1>1, <1>2

LEMMA Reachable3 ==  ReachableFrom({}) = {}
BY DEF ExistsPath, ReachableFrom
=============================================================================
