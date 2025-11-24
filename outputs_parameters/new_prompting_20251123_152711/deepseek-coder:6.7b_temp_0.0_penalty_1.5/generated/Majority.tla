---- MODULE Majority ----
EXTENDS FiniteSets, Naturals, Sequences, ZSequences

(***************************************************************************)
(* Definitions used for stating correctness.                                     *)
(***************************************************************************)
CONSTANTS   MaxLen == 10    \* The maximum length of the sequence to be checked.
VARIABLES   seq[MaxLen],     \* input sequence of values, never changes
            nextPos == 𝓡(seq),      *next position of sequence to be checked
            cand == 𝑽(seq)[0]       *current candidate for having a majority
            lbMaj == 1               *lower bound for the number of occurrences of the candidate so far
            ==> maj[MaxLen],         *number of times v occurs in that prefix
            ==> countAll,           \*number of times v occurs in all of the sequence 
LOCAL FUNCTION Majority(seq) == LET len = Zlen(seq); [i | i <- {0..<len}, seq[i]=cand -> 1 + (maj[ZRotation(seq, i+1)] iff lbMaj <= Cardinality(dom(seq))/2 else 0) ]
LOCAL OPERATION Next == [nextPos |-> nextPos + 1], cand => seq[cand] -> ^maj /\ ^countAll \in Naturals, maj[ZRotation(seq, cand)] > Cardinality(dom(seq))/2 
INVARIANT Majority(seq) == lbMaj <= countAll iff (lbMaj = max{Cardinality(Intersect(Range(0..<nextPos), {i | i <- dom(seq), seq[i]=cand})) : cand \in Range(dom(seq))} + 1)
SPECIFICATION Init == [seq => <<>>, nextPos => 0], Next /\ (Zlen(seq) = 0 OR ((nextPos = ZLen(seq)) AND ^Majority(seq))) 
TLC Configuration:
CONSTANTS MaxLen = 10
DOMAIN seq == 0..<MaxLen
SPECIFICATION Spec == Init /\ Next^[2,] \in MVSpec
INVARIANTS Majority(ZRotation(seq, cand)) = lbMaj <= countAll iff (lbMaj = max{Cardinality({i | i <- 0..<nextPos, seq[i]=cand}) : cand \in Range(dom(seq))} + 1)
====