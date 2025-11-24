---- MODULE Majority ----


EXTENDS FiniteSets, Naturals, Sequences, ZSequences

CONSTANTS 
  EmptyZSeq,
  ZIndices,
  ZSeqOfLength,
  ZSeq,
  ZLen,
  ZSeqFromSeq,
  SeqFromZSeq,
  a_preceq_b,
  Rotation,
  Rotations,
  EmptySet,
  FiniteSets,
  Naturals,
  Sequences

VARIABLES 
  seq,
  pos,
  cand,
  count,
  prefix,
  prefixCount,
  totalCount

ASSIGN 
  pos == 0,
  cand == EmptySet,
  count == 0,
  prefix == EmptyZSeq,
  prefixCount == 0,
  totalCount == 0

=============================================================================
====

DEFINE
  NextPos() == IF pos + 1 > ZLen(seq) THEN pos ELSE pos + 1,

  NextCand() == IF prefixCount > totalCount - prefixCount THEN cand ELSE EmptySet,

  NextCount() == IF pos = 0 THEN 0 ELSE IF cand = EmptySet THEN 0 ELSE IF seq[pos] = cand THEN count + 1 ELSE count - 1,

  NextPrefix() == IF pos = 0 THEN EmptyZSeq ELSE prefix,

  NextPrefixCount() == IF pos = 0 THEN 0 ELSE prefixCount,

  NextTotalCount() == IF pos = 0 THEN 0 ELSE totalCount + 1

=============================================================================
====

INVARIANTS
  InvPrefix == prefixCount <= totalCount,

  InvCand == (cand = EmptySet) OR (prefixCount > totalCount - prefixCount),

  InvCount == (cand = EmptySet) OR (count = totalCount - prefixCount),

  InvTotalCount == totalCount = SUM [i \in ZIndices(seq) |-> IF seq[i] = cand THEN 1 ELSE 0],

  InvPos == pos >= 0 AND pos <= ZLen(seq) + 1,

  InvSeq == seq \in ZSeq(VALUES seq),

  InvResult == (cand = EmptySet) OR (EXISTS [i \in ZIndices(seq) |-> IF seq[i] = cand THEN 1 ELSE 0] >= (ZLen(seq) + 1) / 2)

=============================================================================
====

SPECIFICATION
  Spec == [
    [] (pos = 0 AND cand = EmptySet AND count = 0 AND prefix = EmptyZSeq AND prefixCount = 0 AND totalCount = 0),
    [] (pos = 0 IMPLIES (cand = EmptySet IMPLIES (count = 0 IMPLIES (prefix = EmptyZSeq IMPLIES (prefixCount = 0 IMPLIES (totalCount = 0 IMPLIES InvSeq))))))
  ]

  CONSTANT Inv == InvPrefix AND InvCand AND InvCount AND InvTotalCount AND InvPos AND InvResult

  TRANSITIONS
    /\ pos' = NextPos(),
       cand' = NextCand(),
       count' = NextCount(),
       prefix' = NextPrefix(),
       prefixCount' = NextPrefixCount(),
       totalCount' = NextTotalCount(),
       Inv /\ (seq[pos] = cand IMPLIES (cand' = cand AND count' = count + 1 AND prefixCount' = prefixCount + 1 AND totalCount' = totalCount + 1))

  INITIALIZATION
    /\ pos = 0,
       cand = EmptySet,
       count = 0,
       prefix = EmptyZSeq,
       prefixCount = 0,<｜begin▁of▁sentence｜>
====