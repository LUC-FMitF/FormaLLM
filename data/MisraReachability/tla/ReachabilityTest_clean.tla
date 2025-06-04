-------------------------- MODULE ReachabilityTest --------------------------

EXTENDS Integers, FiniteSets, TLAPS, TLC

CONSTANTS Nodes, SuccSet

P(Succ) == INSTANCE ReachabilityProofs

Test == <<\A Succ \in SuccSet : P(Succ)!Reachable0,
\A Succ \in SuccSet : P(Succ)!Reachable1,
\A Succ \in SuccSet : P(Succ)!Reachable2,
\A Succ \in SuccSet : P(Succ)!Reachable3 >>
----------------------------------------------------------------------------

SuccSet1 == [Nodes -> SUBSET Nodes]

RandomSucc(x) ==
LET RECURSIVE RS(_,_)
RS(F, D) == IF D = {}
THEN F
ELSE LET d == CHOOSE d \in D : TRUE
S == RandomElement(SUBSET Nodes)
IN  RS(F @@ (d :> S), D \ {d})
IN RS(<< >>, Nodes)

SuccSet2(n) == {RandomSucc(i) : i \in 1..n}

============================================================================
