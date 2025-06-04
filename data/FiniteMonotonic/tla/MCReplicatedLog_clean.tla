--------------------------- MODULE MCReplicatedLog ----------------------------
EXTENDS ReplicatedLog, FiniteSetsExt, TLC

ASSUME TLCGet("-Dtlc2.tool.impl.Tool.cdot") = "true"

Constraint ==

/\ Len(log) < 5
/\ \A n \in Node : Len(log) - executed[n] < 5

Reduction ==
LET m == Min(Range(executed)) IN
/\ executed' = [ n \in Node |-> executed[n] - m ]
/\ log' = SubSeq(log, m + 1, Len(log))

WriteTxAndReduction(n, tx) ==
WriteTx(n, tx) \cdot Reduction

ExecuteTxAndReduction(n) ==
ExecuteTx(n) \cdot Reduction

ReductionNext ==
\E n \in Node :
\/ ExecuteTx(n)
\/ ExecuteTxAndReduction(n)
\/ \E tx \in Transaction:
\/ WriteTx(n, tx)
\/ WriteTxAndReduction(n, tx)

=============================================================================
