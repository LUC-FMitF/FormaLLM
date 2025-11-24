---- MODULE ZSequences 
------------------------------ MODULE MajorityProof ----------------------------
(***************************************************************************)
(* Defines operators on finite zero-indexed sequences, where a sequence of  *)
(* length n is represented as a function whose domain is the set 0..(n-1)   *)
(* (the set 
{0, 1, 
... 
, n-1}).                                                                  *)
(***************************************************************************)

CONSTANTS 
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

VARIABLES 
    ZSeqOfLength == [n \in Nat |-> {0 .. (n - 1)} -> FiniteSets],
    ZSeq == UNION {ZSeqOfLength[n] : n \in Nat},
    ZLen == [s \in ZSeq |-> IF s = EmptyZSeq THEN 0 ELSE Cardinality(DOMAIN s)],
    ZSeqFromSeq == [seq \in Sequences |-> IF seq = EmptySeq THEN EmptyZSeq ELSE [i \in 0..(Len(seq)-1) |-> seq[i+1]]],
    SeqFromZSeq == [zseq \in ZSeq |-> IF zseq = EmptyZSeq THEN EmptySeq ELSE [i \in 1..ZLen[zseq] |-> zseq[i-1]]],
    Rotation == [s, r \in ZSeq |-> IF s = EmptyZSeq THEN EmptyZSeq ELSE [i \in ZIndices[s] |-> s[(i + r) % ZLen[s]]]],
    Rotations == [s \in ZSeq |-> IF s = EmptyZSeq THEN {} ELSE {[shift, seq] : shift \in ZIndices[s], seq \in Rotation[s, shift]}]

(* The empty zero-indexed sequence *)
EmptyZSeq == <<>>

(* The set of valid indices for zero-indexed sequence s *)
ZIndices[s] == IF s = EmptyZSeq THEN {} ELSE DOMAIN s

(* The set of all zero-indexed sequences of elements in S with length n *)
ZSeqOfLength[n] == IF n = 0 THEN {EmptyZSeq} ELSE [0 .. (n - 1) -> S]

(* The set of all zero-indexed sequences of elements in S *)
ZSeq == UNION {ZSeqOfLength[n] : n \in Nat}

(* The length of zero-indexed sequence s *)
ZLen[s] == IF s = EmptyZSeq THEN 0 ELSE Cardinality(DOMAIN s)

(* Converts from a one-indexed sequence to a zero-indexed sequence *)
ZSeqFromSeq[seq] == IF seq = EmptySeq THEN EmptyZSeq ELSE [i \in 0..(Len(seq)-1) |-> seq[i+1]]

(* Converts from a zero-indexed sequence to a one-indexed sequence *)
SeqFromZSeq[zseq] == IF zseq = EmptyZSeq THEN EmptySeq ELSE [i \in 1..ZLen[zseq] |-> zseq[i-1]]

(* Rotate the string s to the left by r indices *)
Rotation[s, r] == IF s = EmptyZSeq THEN EmptyZSeq ELSE [i \in ZIndices[s] |-> s[(i + r) % ZLen[s]]]

(* The set of all rotations of zero-indexed sequence s *)
Rotations[s] == IF s = EmptyZSeq THEN {} ELSE {[shift, seq] : shift \in ZIndices[s], seq \in Rotation[s, shift]}

(* Lexicographic order on zero-indexed sequences a and b *)
a \preceq b ==
  LET
    s1len == ZLen[a],
    s2len == ZLen[b],
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len /\ i = s2len -> s1len <= s2len
       [] s1[i] < s2[i] -> TRUE
       [] s1[i] > s2[i] -> FALSE
       [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(a, b, 0)

(* Inductive invariant *)
INDUCTIVE INV ZSequencesInv ==
  [] EmptyZSeq \in ZSeq /\
  [] [i \in ZIndices[s] |-> x] \in ZSeq /\
  [] ZLen[s] = ZLen[Rotation[s, 1]] /\
  [s \in ZSeq] ZLen[s] = Cardinality[s] /\
  [s \in ZSeq] ZSeqFromSeq[SeqFromZSeq[s]] = s /\
  [s \in ZSeq] SeqFromZSeq[ZSeqFromSeq[s]] = s /\
  [s \in ZSeq] Cardinality[Rotations[s]] = ZLen[s] /\
  [s, r \in ZSeq] Rotation[s, r] = [i \in ZIndices[s] |-> s[(i + r) % ZLen[s]

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

=============================================================================
====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,
    FiniteSets = {<x : x \in Nat>},
    Sequences = {<x : x \in FiniteSets>}

SPECIFICATION ZSequencesSpec == [s \in ZSeq] ZLen[s] = Cardinality[s]

INVARIANTS ZSequencesInv

====

CONSTANTS
    EmptyZSeq = <<>>,
    Nat = 0..INF,<｜begin▁of▁sentence｜>


A: The expression `[s \in ZSeq] ZLen[s] = Cardinality[s]` is not a valid Mathematica syntax. It seems you are trying to express a property of a set, but it's not clear what `ZSeq`, `ZLen`, and `Cardinality` are referring to.

If `ZSeq` is a sequence of integers, `ZLen[s]` should be the length of the sequence. If `Cardinality[s]` refers to the number of elements in a set `s`, you could express this as `Length[ZSeq] == Cardinality[s]`.

If `ZLen[s]` is a function that takes a sequence `s` and returns its length, and `Cardinality[s]` is a function that takes a set `s` and returns its size, you could express this as `ZLen[s] == Cardinality[s]`.

Without more context, it's hard to give a more specific answer. Could you please provide more details?
====