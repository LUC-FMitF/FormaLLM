---- MODULE Majority ----
(****************************************************************************)
(* The majority vote algorithm due to Boyer and Moore.                          *)
(* R.S. Boyer, J.S. Moore: MJRTY - A Fast Majority Vote Algorithm.             *)
(* In: R.S. Boyer (ed.): Automated Reasoning: Essays in Honor of Woody           *)
(* Bledsoe, pp. 105-117. Dordrecht, The Netherlands, 1991.                       *)
(****************************************************************************)

CONSTANTS   Values,      \* input sequence of values, never changes
            NextIndex,   \* next position of sequence to be checked
            Cand        \* current candidate for having a majority
VARIABLES   Lb,          \* lower bound for the number of occurrences of the  *)
            IndexSet,    \* set of indexes in the prefix of seq strictly before j holding v
                         \* (initially empty)
            Votes       \* number of times v occurs in that prefix           *)
-----------------------------------------------------------------------------
NextIndex == NextIndex + 1   \* increment next index to check
Cand == Cand'                \* update candidate if necessary
Lb ==                        \* update lower bound for current cand
    IF IndexSet = {} THEN 0 ELSE Cardinality(IndexSet) ENDIF
Votes ==                     \* count number of votes for the current cand
    IF NextIndex > Lb THEN 1 ELSE 2 ENDIF
=============================================================================
INVARIANTS [](NextIndex < Len(seq)) /\ (Cand = Values[NextIndex]) /\ *)
            ((Lb, IndexSet) =                                           *)
              IF NextIndex > Lb THEN (0, {}) ELSE (Lb, Votes IN IndexSet) ENDIF )
=============================================================================
SPECIFICATION Spec
INVARIANTS [](NextIndex < Len(seq)) /\ (Cand = Values[NextIndex]) /\ *)
            ((Lb, IndexSet) =                                           *)
              IF NextIndex > Lb THEN (0, {}) ELSE (Lb, Votes IN IndexSet) ENDIF )
=============================================================================
TLC CONFIGURATION:
CONSTANTS Values,      \* input sequence of values, never changes
            SeqLen = Len(Values),   \* length of the input sequence
            NextIndex = 0,          \* next position to check in seq
            Cand = Values[NextIndex],    \* current candidate for having a majority
            Lb = 0,                     \* lower bound for number of occurrences of cand so far
            IndexSet = {},               \* set of indexes in prefix strictly before j holding v (initially empty)
            Votes = IF NextIndex > Lb THEN 1 ELSE 2 ENDIF   \* number of times v occurs in that prefix
=============================================================================
THEOREM Spec => [](NextIndex < SeqLen /\ Cand = Values[NextIndex] /\ *)
                     ((Lb, IndexSet) = IF NextIndex > Lb THEN (0, {}) ELSE (Lb, Votes IN IndexSet) ENDIF )
=============================================================================