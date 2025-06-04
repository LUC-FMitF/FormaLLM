---------------------------- MODULE MCConsensus -----------------------------
EXTENDS Consensus

ITypeOK == chosen \in SUBSET Value

IInv == /\ ITypeOK
/\ Cardinality(chosen) \leq 1

ISpec == IInv /\ [][Next]_chosen
=============================================================================
