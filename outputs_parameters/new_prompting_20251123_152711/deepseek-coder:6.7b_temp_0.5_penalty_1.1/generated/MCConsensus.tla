---- MODULE MCConsensus ----

(*******************************************************************************************************)
(* Defines operators on finite zero-indexed sequences, where a sequence of length n is represented as *)
(* a function whose domain is the set 0..(n-1) (the set {0, 1, ... , n-1}).                            *)
(*******************************************************************************************************)

EXTENDS FiniteSets, Naturals, Sequences

CONSTANTS Value = {"a", "b", "c"} \* The set of all values.

VARIABLES s \* A zero-indexed sequence.

\* The empty zero-indexed sequence
EmptyZSeq == {}

\* The set of valid indices for zero-indexed sequence s
ZIndices(s) == IF s = EmptyZSeq THEN {} ELSE DOMAIN s

\* The length of zero-indexed sequence s
ZLen(s) == IF s = EmptyZSeq THEN 0 ELSE Cardinality(DOMAIN s)

\* Converts from a one-indexed sequence to a zero-indexed sequence
ZSeqFromSeq(seq) == IF seq = {} THEN EmptyZSeq ELSE [i \in 0..(Len(seq)-1) |-> seq[i+1]]

\* Converts from a zero-indexed sequence to a one-indexed sequence
SeqFromZSeq(zseq) == IF zseq = EmptyZSeq THEN {} ELSE [i \in 1..ZLen(zseq) |-> zseq[i-1]]

\* Rotate the string s to the left by r indices
Rotation(s, r) == IF s = EmptyZSeq THEN EmptyZSeq ELSE [i \in ZIndices(s) |-> s[(i + r) % ZLen(s)]]

\* The set of all rotations of zero-indexed sequence s
Rotations(s) == IF s = EmptyZSeq THEN {} ELSE {[shift |-> r, seq |-> Rotation(s, r)] : r \in ZIndices(s)}

\* The set of all zero-indexed sequences.
ZSequences == UNION {{i \in Naturals |-> i} : s \in Sequences}

Inv == [Next]_chosen => Inv'  (* An invariant *)

ISpec == Init /\ [][Next]_<<s>>_chosen => ISpec'

TLC_CONFIG
CONSTANTS Value = {"a", "b", "c"}
SPECIFICATION ISpec
INVARIANT Inv
CHECK_DEADLOCK FALSE
=============================================================================
====