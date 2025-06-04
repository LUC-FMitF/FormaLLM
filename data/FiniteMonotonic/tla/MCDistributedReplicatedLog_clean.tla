---- MODULE MCDistributedReplicatedLog ----
EXTENDS DistributedReplicatedLog, FiniteSetsExt

ASSUME

Cardinality(Servers) > 1

----

ASSUME IsFiniteSet(Values)

DropCommonPrefix ==
LET commonPrefixBound == Len(LongestCommonPrefix(Range(cLogs)))
Drop(seq, idx) == SubSeq(seq, idx + 1, Len(seq))
IN [ s \in Servers |-> Drop(cLogs[s], commonPrefixBound) ]

====
