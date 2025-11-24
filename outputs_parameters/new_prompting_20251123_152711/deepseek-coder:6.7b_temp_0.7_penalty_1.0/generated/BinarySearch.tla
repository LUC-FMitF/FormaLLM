---- MODULE BinarySearch 

EXTENDS FiniteSets, Naturals, Sequences, ZSequences

CONSTANTS Values, SortedSeqs

VARIABLES seq \in SortedSeqs, val \in Values,
low = 1, high = Len(seq), result = 0;

--fair algorithm BinarySearch 
BEGIN
variables seq \in SortedSeqs, val \in Values,
low = 1, high = Len(seq), result = 0 ;
{ a: while (low <= high AND result = 0) 
with (mid = (low + high) \ 2, mval = seq[mid]) 
{
if (mval = val) 
then {result := mid}
else if (val < mval) 
then {high := mid - 1}
else {low := mid + 1}
}
END
}

--invariant resultCorrect
BEGIN
ASSUME {
  (result = 0 OR val = seq[result])
  AND result <= Len(seq)
  AND (\forall i \in 1..(result-1), seq[i] < val)
  AND (\forall i \in (result+1)..Len(seq), val < seq[i])
}
SHOW {
  (result = 0 OR val = seq[result])
  AND result <= Len(seq)
  AND (\forall i \in 1..(result-1), seq[i] < val)
  AND (\forall i \in (result+1)..Len(seq), val < seq[i])
}
END

-- model for sequences
Seq(S) == UNION {[1..i -> S] : i \in 0..3}

\* TLC configuration
\* Allow infinite stuttering to prevent deadlock on termination.
\* Global variables 
\* Fairness of the algorithm is proved by invariance of formula resultCorrect.
ALGORITHM == BinarySearch
INVARIANT == resultCorrect
DEADLOCK == TRUE
END
====