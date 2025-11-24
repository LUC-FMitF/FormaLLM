---- MODULE Consensus ----
(***************************************************************************)
(* We let the constant parameter Value be the set of all values that can   *)
(* be chosen.                                                              *)
(***************************************************************************)
CONSTANT Value = {v1, v2, v3}

\* The empty zero-indexed sequence
EmptyZSeq == <<>>

\* The set of valid indices for zero-indexed sequence s
ZIndices(s) ==
  IF s = EmptyZSeq
  THEN {}
  ELSE DOMAIN s

\* The set of all zero-indexed sequences of elements in S with length n
LOCAL ZSeqOfLength(S, n) ==
  IF n = 0
  THEN {EmptyZSeq}
  ELSE [0 .. (n - 1) -> S]

\* The set of all zero-indexed sequences of elements in S
ZSeq(S) == UNION {ZSeqOfLength(S, n) : n \in Nat}

\* The length of zero-indexed sequence s
ZLen(s) ==
  IF s = EmptyZSeq
  THEN 0
  ELSE Cardinality(DOMAIN s)

\* Converts from a one-indexed sequence to a zero-indexed sequence
ZSeqFromSeq(seq) ==
  IF seq = <<>>
  THEN EmptyZSeq
  ELSE [i \in 0..(Len(seq)-1) |-> seq[i+1]]

\* Converts from a zero-indexed sequence to a one-indexed sequence
SeqFromZSeq(zseq) ==
  IF zseq = EmptyZSeq
  THEN <<>>
  ELSE [i \in 1..ZLen(zseq) |-> zseq[i-1]]

\* Lexicographic order on zero-indexed sequences a and b
a \preceq b ==
  LET
    s1len == ZLen(a)
    s2len == ZLen(b)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(a, b, 0)

\* Rotate the string s to the left by r indices
Rotation(s, r) ==
  IF s = EmptyZSeq
  THEN EmptyZSeq
  ELSE [i \in ZIndices(s) |-> (ZLen(s) - i + r) MOD ZLen(s)]

\* The type-correctness invariant TypeOK, and then define Inv *)
(* to be the inductive invariant that asserts TypeOK and that    *)
(* the cardinality of the set `chosen' is at most 1.               *)
INVARIANT TypeOK == <<>> : Value -> TRUE                          (*)
INVARIANT Inv == (TypeOK /\ ZLen(chosen) <= 1) &&                (*)
                   [[pc] \in Next |-> chosen = {} ||                    *\*)
                      [pc] \in Next && pc' = <<>> : Value -> TRUE     *)

\* The specification of the algorithm, which asserts that Init is  *)
(* a temporal formula satisfied by an execution and that each step *)
(* satisfies either Next or it is a "stuttering step" that leaves   *)
(* all the variables unchanged.                                      *)
SPECIFICATION LiveSpec == (Init /\ [][Next]_vars) &&              (*)
                            [[pc] \in Next || pc' = <<>> : Value -> TRUE  *\*)

\* The property Success asserts that some value is chosen.         *)
PROPERTY Success == (chosen <> {})                                     (*)

(* We now prove the safety property that at most one value is       *)
(* chosen.  We first define the type-correctness invariant TypeOK,*)
(* and then define Inv to be the inductive invariant that asserts    *)
(* TypeOK and that the cardinality of the set `chosen' is at most   *)
(* 1.                                                                 *)
INVARIANT TypeOK == <<>> : Value -> TRUE                          (*)
INVARIANT Inv == (TypeOK /\ ZLen(chosen) <= 1) &&                (*)
                   [[pc] \in Next |-> chosen = {} ||                    *\*)
                      [pc] \in Next && pc' = <<>> : Value -> TRUE     *)

(* We now prove that Inv is an invariant, meaning that it is true in  *)
(* every state in every behavior. Before trying to prove this, we   *)
(* should first use TLC to check that it is true. It's hardly worth *)
(* bothering to either check or prove the obvious fact that Inv is an*)
(* invariant, but it's a nice tiny exercise.                         *)
**************************************************************************)
====