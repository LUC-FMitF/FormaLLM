------------------------------ MODULE SpanTreeTest ------------------------------

EXTENDS Integers, FiniteSets, Randomization

CONSTANTS Nodes, Root, MaxCardinality

ASSUME /\ Root \in Nodes
/\ MaxCardinality \in Nat
/\ MaxCardinality >= Cardinality(Nodes)

VARIABLES mom, dist, Edges
vars == <<mom, dist, Edges>>

Nbrs(n) == {m \in Nodes : {m, n} \in Edges}

TypeOK == /\ mom \in [Nodes -> Nodes]
/\ dist \in [Nodes -> Nat]
/\ \A e \in Edges : (e \subseteq Nodes) /\ (Cardinality(e) = 2)

Init == /\ mom = [n \in Nodes |-> n]
/\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality]
/\ Edges \in {E \in SUBSET (SUBSET Nodes) : \A e \in E : Cardinality(e) = 2}

Next == \E n \in Nodes :
\E m \in Nbrs(n) :
/\ dist[m] < 1 + dist[n]
/\ \E d \in (dist[m]+1) .. (dist[n] - 1) :
/\ dist' = [dist EXCEPT ![n] = d]
/\ mom'  = [mom  EXCEPT ![n] = m]
/\ Edges' = Edges

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
-----------------------------------------------------------------------------
PostCondition ==
\A n \in Nodes :
\/ /\ n = Root
/\ dist[n] = 0
/\ mom[n] = n
\/ /\ dist[n] = MaxCardinality
/\ mom[n] = n
/\ \A m \in Nbrs(n) : dist[m] = MaxCardinality
\/ /\ dist[n] \in 1..(MaxCardinality-1)
/\ mom[n] \in Nbrs(n)
/\ dist[n] = dist[mom[n]] + 1

Safety == []((~ ENABLED Next) => PostCondition)

Liveness == <>PostCondition

=============================================================================
