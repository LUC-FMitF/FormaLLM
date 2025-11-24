---- MODULE Majority ----

(*******************************************************************************
Boyer and Moore's majority vote algorithm.
*******************************************************************************)

CONSTANTS   Val,             \* The set of all values.
            EmptySeq         \* The empty sequence.

VARIABLES   seq,              \* Input sequence of values.
            nextPos,          \* Next position to be checked.
            cand,             \* Current candidate for majority.
            lowBound,         \* Lower bound on the number of occurrences of cand so far.
            prefixIndices,     \* Set of indices in the prefix strictly before j holding v.
            countV,           \* Number of times v occurs in that prefix.
            totalCountV       \* Total number of times v occurs in all sequence.
            
ASSUME      seq  /\ Cardinality(DOMAIN nextPos) = Cardinality(seq)

\* Definitions used for stating correctness.
LOCAL FUNCTION Majority(s, i, c, lb, pi, countv, totalcountv) ==
    IF i > len[s] THEN
        (c = s[0], lb > 1/2 * len[s])
    ELSE 
        IF s[i] = s[0] THEN
            Majority(s, i + 1, c, lb, pi UNION {i}, countv + 1, totalcountv + 1)
        ELSE
            Majority(s, i + 1, c, lb, pi, countv, totalcountv + 1)
        ENDIF;
    ENDIF;

\* Main correctness property.
MAJORITYPROP == cand /\ lowBound > 1/2 * Cardinality(seq)

\* Inductive invariant for proving correctness.
INVARIANT  ==  (cand = s[0]) AND (lowBound <= 1/2 * len[s] + countV) AND
               (totalCountV >= 1/2 * Cardinality(DOMAIN prefixIndices))

\* Next state relation.
Next == \E i: nextPos /\ seq[i] = cand : 
          [seq'        == UpdateSeq(seq, i, cand),
           nextPos      == If Else (i + 1 > len[seq]) Then EmptySet Else {i + 1},
           cand         == s[0],
           lowBound     == 1/2 * Cardinality(DOMAIN prefixIndices) + countV,
           prefixIndices== If Else (s[0] = seq[i]) Then pi UNION {i} Else pi,
           countV       == If Else (s[0] = seq[i]) Then countv + 1 Else countv,
           totalCountV  == If Else (s[0] = seq[i]) Then totalcountv + 1 Else totalcountv]

\* Specification.
Spec == Init /\ []Next
===============================================================================
====
TLC Configuration:
CONSTANTS  Val = {...} (* Set of all values *)
SPECIFICATION Spec
INVARIANTS  INVARIANT, MAJORITYPROP
====