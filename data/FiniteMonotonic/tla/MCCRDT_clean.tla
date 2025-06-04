------------------------------- MODULE MCCRDT ---------------------------------
EXTENDS CRDT, FiniteSetsExt, TLC

ASSUME TLCGet("-Dtlc2.tool.impl.Tool.cdot") = "true"

Constraint ==
\A n \in Node : counter[n][n] <= 3

Reduction ==
LET m == Min({counter[n][o] : n, o \in Node}) IN
counter' = [ n \in Node |-> [ o \in Node |-> counter[n][o] - m ] ]

IncrementAndReduction(n) ==
Increment(n) \cdot Reduction

GossipAndReduction(n, o) ==
Gossip(n,o) \cdot Reduction

ReductionNext ==
\E n, o \in Node :
\/ Increment(n)
\/ Gossip(n, o)
\/ IncrementAndReduction(n)
\/ GossipAndReduction(n, o)

=============================================================================
