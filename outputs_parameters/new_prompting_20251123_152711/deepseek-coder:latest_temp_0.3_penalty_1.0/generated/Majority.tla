---- MODULE Majority ----

(***************************************************************************)
(* input sequence of values, never changes *)
(* next position of sequence to be checked *)
(* current candidate for having a majority *)
(* lower bound for the number of occurrences of the candidate so far *)
(* set of indexes in the prefix of the sequence strictly before j holding v *)
(* number of times v occurs in that prefix *)
(* number of times v occurs in all of the sequence *)
(* main correctness property: cand can be the only value that has a majority *)
(* inductive invariant for proving correctness *)
(***************************************************************************)

LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences

\* input sequence of values
InputSeq == <<0, 1, 2, 2, 3>>

\* next position of sequence to be checked
NextPos == 3

\* current candidate for having a majority
Cand == 2

\* lower bound for the number of occurrences of the candidate so far
LowerBound == 2

\* set of indexes in the prefix of the sequence strictly before j holding v
Indexes == 2 -> [0, 1, 2]

\* number of times v occurs in that prefix
TimesInPrefix == 2

\* number of times v occurs in all of the sequence
TimesInAll == 3

\* main correctness property: cand can be the only value that has a majority
CorrectnessProperty ==
  LET
    s == InputSeq
    n == NextPos
    c == Cand
    lb == LowerBound
    i == Indexes
    ti == TimesInPrefix
    t == TimesInAll
    RECURSIVE CheckMajority(s, n, c, lb, i, ti, t)
    CheckMajority(s, n, c, lb, i, ti, t) ==
      CASE i = n
      THEN s[n] ≥ lb → ti ≥ t
      ELSE s[i] ≠ s[n] → CheckMajority(s, n, c, lb, i + 1, ti, t)
  IN CheckMajority(s, n, c, lb, 0, ti, t)

\* inductive invariant for proving correctness
InductiveInvariant 
  LET
    s == InputSeq
    n == NextPos
    c == Cand
    lb == LowerBound
    i == Indexes
    ti == TimesInPrefix
    t == TimesInAll
    RECURSIVE CheckMajority(s, n, c, lb, i, ti, t)
    CheckMajority(s, n, c, lb, i, ti, t) ==
      CASE i = n
      THEN s[n] ≥ lb → ti ≥ t
      ELSE s[i] ≠ s[n] → CheckMajority(s, n, c, lb, i + 1, ti, t)
  IN CheckMajority(s, n, c, lb, 0, ti, t)

=============================================================================
====