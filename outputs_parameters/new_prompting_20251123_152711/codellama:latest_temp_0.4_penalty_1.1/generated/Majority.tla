---- MODULE Majority ----

(****************************************************************************)
(* The algorithm takes as input a sequence of values, makes one pass over   *)
(* the sequence, and reports an element cand such that no element other     *)
(* than cand may have an absolute majority in the sequence.                 *)
(****************************************************************************)
VARIABLES seq : [0 .. (LenSeq-1)] -> Values  \* input sequence of values, never changes
         j    : Nat                           \* next position of sequence to be checked
         cand : Value                        \* current candidate for having a majority
         lb   : Nat                          \* lower bound for the number of occurrences of the candidate so far
         is   : [0 .. (j-1)] -> Bool         \* set of indexes in the prefix of the sequence strictly before j holding v
         n    : Nat                          \* number of times v occurs in that prefix
         m    : Nat                          \* number of times v occurs in all of the sequence
-----------------------------------------------------------------------------
Values == {a, b}  \* set of values a and b for which we want to find an element with majority
Nat     == [0 .. (LenSeq-1)]  \* natural numbers up to LenSeq-1
****************************************************************************)
Init ==   \* initial predicate: seq is the input sequence, j = 0, cand = a, lb = 0, and is empty.
    /\ seq[j] = a
    /\ j = 0
    /\ cand = a
    /\ lb = 0
    /\ is = <<>>
-----------------------------------------------------------------------------
Next ==   \* next state: update candidate, lower bound, and set of indexes holding v.
    [
      seq' |-> seq[j+1],
      j'    |-> j + 1,
      cand' |-> IF n = m THEN a ELSE b ENDIF,
      lb'   |-> IF n > m THEN 0 ELSE lb + 1 ENDIF,
      is'   |-> [k \in DOMAIN is WHERE k < j : seq[k] <> v] UNION {j}
    ]
-----------------------------------------------------------------------------
Correct ==   \* main correctness property: cand can be the only value that has a majority.
    /\ (cand = a \/ cand = b)
    ==> (n > m \/ n = 0) => cand = a
=============================================================================
INVARIANTS [](Correct /\ lb <= LenSeq - j)
=============================================================================
CONSTANT Values == {a,b}
CONSTANT Nat    == [0 .. (LenSeq-1)]
****************************************************************************)
====