---- MODULE MajorityProof ----

(***************************************************************************)
(* Defines operators on finite zero-indexed sequences, where a sequence of *)
(* length n is represented as a function whose domain is the set 0..(n-1)  *)
(* (the set {0, 1, ... , n-1}).                                            *)
(***************************************************************************)
CONSTANTS   S         \* The set of all elements.
VARIABLES   s        \* A zero-indexed sequence of elements in S with length n.
              n       \* The length of the sequence.
INJECTIVE_RECORD  zseq2seq, seq2zseq    \* Converts between a zero-indexed and one-indexed representation of sequences.                            *)
***************************************************************************)
LEMMA ZLenIsNat : Nat(ZLen(s))   /\   LENGTH[SeqFromZSeq(s)] = ZLen(s)    (* The length function is computable and has the same value as ZLen.                          *)
-----------------------------------------------------------------------------
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      (* All indices in a valid set of positions are also valid for this sequence.                         *)
             /\  OccurrencesOf s = {p | p \in POSITIONS[s] /\ ZSeq(OccurrenceAtPosition(s, p)) = <<>> }    (* The occurrences function is computable and has the same values as Positions.        *)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      (* All indices in a valid set of positions are also valid for this sequence.                         *)
             /\  OccurrencesOf s = {p | p \in POSITIONS[s] /\ ZSeq(OccurrenceAtPosition(s, p)) = <<>> }    (* The occurrences function is computable and has the same values as Positions.        *)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      (* All indices in a valid set of positions are also valid for this sequence.                         *)
             /\  OccurrencesOf s = {p | p \in POSITIONS[s] /\ ZSeq(OccurrenceAtPosition(s, p)) = <<>> }    (* The occurrences function is computable and has the same values as Positions.        *)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      (* All indices in a valid set of positions are also valid for this sequence.                         *)
             /\  OccurrencesOf s = {p | p \in POSITIONS[s] /\ ZSeq(OccurrenceAtPosition(s, p)) = <<>> }    (* The occurrences function is computable and has the same values as Positions.        *)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      (* All indices in a valid set of positions are also valid for this sequence.                         *)
             /\  OccurrencesOf s = {p | p \in POSITIONS[s] /\ ZSeq(OccurrenceAtPosition(s, p)) = <<>> }    (* The occurrences function is computable and has the same values as Positions.        *)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      (* All indices in a valid set of positions are also valid for this sequence.                         *)
             /\  OccurrencesOf s = {p | p \in POSITIONS[s] /\ ZSeq(OccurrenceAtPosition(s, p)) = <<>> }    (* The occurrences function is computable and has the same values as Positions.        *)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      (* All indices in a valid set of positions are also valid for this sequence.                         *)
             /\  OccurrencesOf s = {p | p \in POSITIONS[s] /\ ZSeq(OccurrenceAtPosition(s, p)) = <<>> }    (* The occurrences function is computable and has the same values as Positions.        *)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      (* All indices in a valid set of positions are also valid for this sequence.                         *)
             /\  OccurrencesOf s = {p | p \in POSITIONS[s] /\ ZSeq(OccurrenceAtPosition(s, p)) = <<>> }    /* The occurrences function is computable and has the same values as Positions.        */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      (* All indices in a valid set of positions are also valid for this sequence.                         *)
             /\  OccurrencesOf s = {p | p \in POSITIONS[s] /\ ZSeq(OccurrenceAtPosition(s, p)) = <<>> }    /* The occurrences function is computable and has the same values as Positions.        */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      (* All indices in a valid set of positions are also valid for this sequence.                         *)
             /\  OccurrencesOf s = {p | p \in POSITIONS[s] /\ ZSeq(OccurrenceAtPosition(s, p)) = <<>> }    /* The occurrences function is computable and has the same values as Positions.        */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      (* All indices in a valid set of positions are also valid for this sequence.                         *)
             /\  OccurrencesOf s = {p | p \in POSITIONS[s] /\ ZSeq(OccurrenceAtPosition(s, p)) = <<>> }    /* The occurrences function is computable and has the same values as Positions.        */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the one with length zero.                              *)
-----------------------------------------------------------------------------
LEMMA ZIndicesIsValid : ValidIndexSet S ZIndices s     \* All indices in a valid set of indices are also valid for this sequence.                            *)
-----------------------------------------------------------------------------
LEMMA PositionsAreInZSeq : (p \in POSITIONS[s]) == p IN DOMAIN(zseq2seq(s))   (* The positions function is computable and has the same values as ZIndices.          *)
-----------------------------------------------------------------------------
LEMMA OccurrencesIsValid : ValidIndexSet S (OccurrencesOf s)     \* All indices in a valid set of occurrences are also valid for this sequence.                      *)
-----------------------------------------------------------------------------
INVARIANT   ZLen(s) = LENGTH[SeqFromZSeq(s)]    /\  EMPTY_SEQUENCE s == (s = <<>>)     \* The length function is computable and has the same value as ZLen.                          *)
            ALL i IN DOMAIN zseq2seq : ValidIndexSet S {i}      /* All indices in a valid set of positions are also valid for this sequence.                         */)
***************************************************************************)
LEMMA EmptyIsEmpty : EMPTY_SEQUENCE s == (s = <<>>)   /\  LENGTH[SeqFromZSeq(<<>>)] = 0    (* The empty sequence is the
====