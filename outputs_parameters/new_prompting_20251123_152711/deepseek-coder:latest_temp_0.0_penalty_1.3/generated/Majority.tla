---- MODULE Majority ----

(***************************************************************************)
(* Boyer, J.S. Moore: MJRTY – A Fast Majority Vote Algorithm.               *)
(***************************************************************************)

CONSTANTS  seq,               \* Input sequence of values, never changes.
            j,                \* Next position of sequence to be checked.
            cand,            \* Current candidate for having a majority.
            lowerBound,     \* Lower bound for the number of occurrences of the candidate so far.
            prev,           \* Set of indexes in the prefix of the sequence strictly before j holding v.
            timesV,        \* Number of times v occurs in that prefix.
            timesAll,     \* Number of times v occurs in all of the sequence.

\* Main correctness property: cand can be the only value that has a majority.

\* Inductive invariant for proving correctness.

\* Algorithm takes as input a sequence of values, makes one pass over the sequence, and reports an element cand such that no element other than cand may have an absolute majority in the sequence.

LOCAL INSTANCE Sequences
  
BoyerMooreMajorityVote == 
  RECURSIVE BoyerMooreMajorityVote(_, 0, 0, 0, 0, 0)
  RECURSIVE BoyerMooreMajorityVote(seq, j, cand, lowerBound, timesV, timesAll) 
    IF j = seq.Cardinality
    THEN cand
    ELSE 
      RECURSIVE BoyerMooreMajorityVote(seq, j+1, cand, lowerBound+1, timesAll, seq.Cardinality)
END BoyerMooreMajorityVote

=============================================================================
====