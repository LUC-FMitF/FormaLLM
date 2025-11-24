---- MODULE BinarySearch ----
VARIANT resultCorrect IS CORRECT :==
    (low <= high /\ result = 0) IMPLIES EXISTS {i : seq[i] = val} 
        [(val \in SortedSeqs) => GLOBAL MAXIMUM {i : seq[i] = val}] ELSE 0;
====