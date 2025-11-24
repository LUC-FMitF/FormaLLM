---- MODULE Majority ----
EXTENDS FiniteSets, Naturals, Sequences, ZSequences

CONSTANTS 
  EmptySeq == <<>>,
  NoCand == NULL,
  LowerBound == 0

VARIABLES
  seq == EmptySeq, (* input sequence of values, never changes *)
  nextPos == LowerBound, (* next position of sequence to be checked *)
  cand == NoCand, (* current candidate for having a majority *)
  lb == LowerBound, (* lower bound for the number of occurrences of the candidate so far *)
  indexes == EmptyZSeq (* set of indexes in the prefix of the sequence strictly before j holding v *)

(* number of times v occurs in that prefix *)
PREFIXCOUNT(v) == LET pos == ZIndices(indexes) IN Sum(pos, i => seq[i] = v)

(* number of times v occurs in all of the sequence *)
GLOBALCOUNT(v) == Sum(indexes, i => seq[i] = v)

(* main correctness property: cand can be the only value that has a majority *)
CORRECTNESS == 
  (cand = NoCand AND lb < GLOBALCOUNT(cand)) 
  OR 
  (seq[nextPos] = cand AND lb <= PREFIXCOUNT(cand) < GLOBALCOUNT(cand))

(* inductive invariant for proving correctness *)
INVARIANT == 
  cand = NoCand OR 
  EXISTS x IN seq[nextPos .. ZLen(seq) - 1] /\ 
    (PREFIXCOUNT(x) > lb OR (seq[nextPos] = x AND PREFIXCOUNT(x) = lb AND GLOBALCOUNT(x) > GLOBALCOUNT(cand)))

(* Operations *)
NEXT ==
  IF nextPos = ZLen(seq)
  THEN EmptyOp
  ELSE 
    IF seq[nextPos] = cand
    THEN Skip
    ELSE 
      IF GLOBALCOUNT(seq[nextPos]) > lb
      THEN 
        cand := seq[nextPos],
        lb := GLOBALCOUNT(seq[nextPos]),
        indexes := Union(indexes, {nextPos})
      FI,
      Skip

SPECIFICATION == Init /\ [](Next /\ CORRECTNESS)

INVARIANTS == 
  INIT == Init /\ nextPos = LowerBound /\ cand = NoCand /\ lb = LowerBound
  NEXT == CORRECTNESS /\ INVARIANT
====