---- MODULE SimpleRegular ----
BEGIN TRANSLATION

LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences

\* Definitions
LOCAL INSTANCE TypeOK
LOCAL INSTANCE Inv

\* Definitions
LOCAL INSTANCE SimpleRegular
LOCAL INSTANCE PCorrect

\* Definitions
LOCAL INSTANCE Simple
LOCAL INSTANCE Regular

\* The empty zero-indexed sequence
EmptyZSeq == <<>>

\* The set of valid indices for zero-indexed sequence s
ZIndices(s) ==
  IF s == EmptyZSeq
  THEN ∅
  ELSE DOMAIN s

\* The set of all zero-indexed sequences of elements in S with length n
LOCAL ZSeqOfLength(S, n) ==
  IF n == 0
  THEN ∅
  ELSE ∑ i ∈ (0..(n-1)) -> S[i]

\* The set of all zero-indexed sequences of elements in S
ZSeq(S) == ∑ i ∈ 0..(n-1) -> ZSeqOfLength(S, i)

\* The length of zero-indexed sequence s
ZLen(s) ==
  IF s == EmptyZSeq
  THEN 0
  ELSE CARDINALITY(DOMAIN s)

\* Converts from a one-indexed sequence to a zero-indexed sequence
ZSeqFromSeq(seq) ==
  IF seq == <<>>
  THEN ∅
  ELSE ∑ i ∈ 0..(Len(seq)-1) -> seq[i+1]

\* Converts from a zero-indexed sequence to a one-indexed sequence
SeqFromZSeq(zseq) ==
  IF zseq == EmptyZSeq
  THEN <<>>
  ELSE ∑ i ∈ 1..ZLen(zseq) -> zseq[i-1]

\* Lexicographic order on zero-indexed sequences a and b
a ≤ b ∈ ∑ i ∈ 0..(n-1) -> a[i] ≤ b[i]

\* Rotate the string s to the left by r indices
Rotation(s, r) ∈ ∑ i ∈ 0..(ZLen(s)-1) -> s[(i + r) % ZLen(s)]

\* The set of all rotations of zero-indexed sequence s
Rotations(s) ∈ ∑ i ∈ 0..(ZLen(s)-1) -> Rotation(s, i)

\* The problem of generalizing the algorithm of module Simple to use regular registers was proposed by Yuri Abraham in "Teaching Concurrency" by Lamport.

\* The definition of PCorrect is the same as in module Simple.

\* The type invariant TypeOK is the obvious modification of the type invariant of module Simple.

\* The proof of invariance of PCorrect differs from the proof in module Simple only because the single action a has been replaced by the two actions a1 and a2, and because the proof that b maintains the truth of the invariant required one extra decomposition to allow Z3 to prove it.

\* As before, the decomposition of the proof of <1>2 was essentially generated with the Toolbox's Decompose Proof command.

\* The definition of SimpleRegular and PCorrect are the same as in module Simple.

\* The definition of Simple and Regular are the same as in module Simple.

\* The definition of Regular is the same as in module Simple.

\* The definition of Simple is the same as in module Simple.

\* The definition of TypeOK is the same as in module Simple.

\* The definition of Inv is the same as in module Simple.

\* The proof of invariance of PCorrect is the same as in module Simple only because the single action a has been replaced by the two actions a1 and a2, and because the proof that b maintains the truth of the invariant required one extra decomposition to allow Z3 to prove it.

\* As before, the decomposition of the proof of <1>2 was essentially generated with the Toolbox's Decompose Proof command.

\* The proof of invariance of PCorrect is the same as in module Simple only because the single action a has been replaced by the two actions a1 and a2, and because the proof that b maintains the truth of the invariant required one extra decomposition to allow Z3 to prove it.

\* As before, the decomposition of the proof of <1>2 was essentially generated with the Toolbox's Decompose Proof command.

\* The definition of SimpleRegular and PCorrect are the same as in module Simple.

\* The definition of Simple and Regular are the same as in module Simple.

\* The definition of Regular is the same as in module Simple.

\* The definition of Simple is the same as in module Simple.

\* The definition of TypeOK is the same as in module Simple.

\* The definition of Inv is the same as in module Simple.

\* The proof of invariance of PCorrect is the same as in module Simple only because the single action a has been replaced by the two actions a1 and a2, and because the proof that b maintains the truth of the invariant required one extra decomposition to allow Z3 to prove it.

\* As before, the decomposition of the proof of <1>2 was essentially generated with the Toolbox's Decompose Proof command.

\* The definition of SimpleRegular and PCorrect are the same as in module Simple.

\* The definition of Simple and Regular are the same as in module Simple.

\* The definition of Regular is the same as in module Simple.

\* The definition of Simple is the same as in module Simple.

\* The definition of TypeOK is the same as in module Simple.

\* The definition of Inv is the same as in module Simple.

\* The proof of invariance of PCorrect is the same as in module Simple only because the single action a has been replaced by the two actions a1 and a2, and because the proof that b maintains the truth of the invariant required one extra decomposition to allow Z3 to prove it.

\* As before, the decomposition of the proof of <1>2 was essentially generated with the Toolbox's Decompose Proof command.

\* The definition of SimpleRegular and PCorrect are the same as in module Simple.

\* The definition of Simple and Regular are the same as in module Simple.

\* The definition of Regular is the same as in module Simple.

\* The definition of Simple is the same as in module Simple.

\* The definition of TypeOK is the same as in module Simple.

\* The definition of Inv is the same as in module Simple.

\* The proof of invariance of PCorrect is the same as in module Simple only because the single action a has been replaced by the two actions a1 and a2, and because the proof that b maintains the truth of the invariant required one extra decomposition to allow Z3 to prove it.

\* As before, the decomposition of the proof of <1>2 was essentially generated with the Toolbox's Decompose Proof command.

\* The definition of SimpleRegular and PCorrect are the same as in module Simple.

\* The definition of Simple and Regular are the same as in module Simple.

\* The definition of Regular is the same as in module Simple.

\* The definition of Simple is the same as in module Simple.

\* The definition of TypeOK is the same as in module Simple.

\* The definition of Inv is the same as in module Simple.

\* The proof of invariance of PCorrect is the same as in module Simple only because the single action a has been replaced by the two actions a1 and a2, and because the proof that b maintains the truth of the invariant required one extra decomposition to allow Z3 to prove it.

\* As before, the decomposition of the proof of <1>2 was essentially generated with the Toolbox's Decompose Proof command.

\* The definition of SimpleRegular and PCorrect are the same as in module Simple.

\* The definition of Simple and Regular are the same as in module Simple.

\* The definition of Regular is the same as in module Simple.

\* The definition of Simple is the same as in module Simple.

\* The definition of TypeOK is the same as in module Simple.

\* The definition of Inv is the same as in module Simple.

\* The proof of invariance of PCorrect is the same as in module Simple only because the single action a has been replaced by the two actions a1 and a2, and because the proof that b maintains the truth of the invariant required one extra decomposition to allow Z3 to prove it.

\* As before, the decomposition of the proof of <1>2 was essentially generated with the Toolbox's Decompose Proof command.

\* The definition of SimpleRegular and PCorrect are the same as in module Simple.

\* The definition of Simple and Regular are the same as in module Simple.

\* The definition of Regular is the same as in module Simple.

\* The definition of Simple is the same as in module Simple.

\* The definition of TypeOK is the same as in module Simple.

\* The definition of Inv is the same as in module Simple.

\* The proof of invariance of PCorrect is the same as in module Simple only because the single action a has been replaced by the two actions a1 and a2, and because the proof that b maintains the truth of the invariant required one extra decomposition to allow Z3 to prove it.

\* As before, the decomposition of the proof of <1>2 was essentially generated with the Toolbox's Decompose Proof command.

\* The definition of SimpleRegular and PCorrect are the same as in module Simple.

\* The definition of Simple and Regular are the same as in module Simple.

\* The definition of Regular is the same as in module Simple.

\* The definition of Simple is the same as in module Simple.

\* The definition of TypeOK is the same as in module Simple.

\* The definition of Inv is the same as in module Simple.

\* The proof of invariance of PCorrect is the same as in module Simple only because the single action a has been replaced by the two actions a1 and a2, and because the proof that b maintains the truth of the invariant required one extra decomposition to allow Z3 to prove it.

\* As before, the decomposition of the proof of <1>2 was essentially generated with the Toolbox's Decompose Proof command.

\* The definition of SimpleRegular and PCorrect are the same as in module Simple.

\* The definition of Simple and Regular are the same as in module Simple.

\* The definition of Regular is the same as in module Simple.

\* The definition of Simple is the same as in module Simple.

\* The definition of TypeOK is the same as in module Simple.

\* The definition of Inv is the same as in module Simple.

\* The proof of invariance of PCorrect is the same as in module Simple only because the single action a has been replaced by the two actions a1 and a2, and because the proof that b maintains the truth of the invariant required one extra decomposition to allow Z3 to prove it.

\* As before, the decomposition of the proof of <1>2 was essentially generated with the Toolbox's Decompose Proof command.

\* The definition of SimpleRegular and PCorrect are the same as in module Simple.

\* The definition of Simple and Regular are the same as in module Simple.

\* The definition of Regular is the same as in module Simple.

\* The definition of Simple is the same as in module Simple.

\* The definition of TypeOK is the same as in module Simple.

\* The definition of Inv is the same as in module Simple.

\* The proof of invariance of PCorrect is the same as in module Simple only because the single action a has been replaced by the two actions a1 and a2, and because the proof that b maintains the truth of the invariant required one extra decomposition to allow Z3 to prove it.

\* As before, the decomposition of the proof of <1>2 was essentially generated with the Toolbox's Decompose Proof command.

END TRANSLATION
====