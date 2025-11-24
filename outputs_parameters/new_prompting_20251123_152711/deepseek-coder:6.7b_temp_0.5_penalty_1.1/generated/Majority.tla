---- MODULE Majority ----
EXTENDS FiniteSets, Integers1, Sequences

CONSTANTS n == \* maximum sequence length for model checking
         2 * n

VARIABLES seq[0..n-1] /\ cand, nextPos, lowerBound, countPrefix, totalCount == \* input sequence of values, next position to be checked, current candidate, lower bound and counts

ASSUME Initially(totalCount = 0) 
   AND Initially(lowerBound = n DIV 2 + 1)
   AND Initially(nextPos = 0)
   AND \* inductive invariant for proving correctness
     [](Cardinality(seq[i] : i \in nextPos..n-1) <= n DIV 2
        /\ (totalCount > 0 ==> totalCount >= lowerBound)
        /\ (cand = seq[nextPos] /\ lowerBound > n DIV 2 ==> totalCount - Cardinality(seq[i] : i \in nextPos..n-1) <= n DIV 2))
   AND \* main correctness property: cand can be the only value that has a majority
     [](totalCount > n DIV 2 /\ seq[nextPos] = cand ==> totalCount - Cardinality(seq[i] : i \in nextPos..n-1) <= n DIV 2))
   AND \* number of times v occurs in that prefix
     [](countPrefix = Cardinality(seq[i] : i \in 0..nextPos) - (seq[nextPos] = cand)))
   AND \* set of indexes in the prefix strictly before j holding v
     [](Cardinality({i | i \in 0..nextPos /\ seq[i] = cand} : nextPos > n DIV 2))
   AND \* number of times v occurs in all of the sequence
     [](totalCount = Cardinality(seq[i] : i \in 0..n-1) - (seq[nextPos] = cand)))
   AND \* lower bound for the number of occurrences of the candidate so far
     [](lowerBound = totalCount DIV 2 + 1))
=============================================================================
SPECIFICATION MajorityVote == EXISTS x. TotalOrder(x)

TLC Configuration:
CONSTANTS n = 100
====