---- MODULE ClientCentric ----

(***************************************************************************)
(* Defines operators on finite zero-indexed sequences, where a sequence of  *)
(* length n is represented as a function whose domain is the set 0..(n-1)   *)
(* (the set 

(***************************************************************************)

LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
  
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
  IF seq = EmptyZSeq
  THEN EmptyZSeq
  ELSE [i \in 0..(Len(seq)-1) |-> seq[i+1]]

\* Converts from a zero-indexed sequence to a one-indexed sequence
SeqFromZSeq(zseq) ==
  IF zseq = EmptyZSeq
  THEN EmptyZSeq
  ELSE [i \in 1..ZLen(zseq) |-> zseq[i-1]]

\* Lexicographic order on zero-indexed sequences a and b
a \preceq b ==
  LET
    s1len == ZLen(a)
    s2len == ZLen(b)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len /\ i = s2len -> s1len <= s2len
       [] s1[i] < s2[i] -> TRUE
       [] s1[i] > s2[i] -> FALSE
       [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(a, b, 0)

\* Rotate the string s to the left by r indices
Rotation(s, r) ==
  IF s = EmptyZSeq
  THEN EmptyZSeq
  ELSE [i \in ZIndices(s) |-> s[(i + r) % ZLen(s)]]

\* The set of all rotations of zero-indexed sequence s
Rotations(s) ==
  IF s = EmptyZSeq
  THEN {}
  ELSE {[
      shift |-> r,
      seq   |-> Rotation(s, r)
     ] : r \in ZIndices(s)
   }

=============================================================================
====

CONSTANTS
Keys == {...}
Values == {...}
InitValue == {...}

\* Helpers representing Reads and Writes
READ(k,v) == [k -> v]
WRITE(k,v) == [k -> v]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* An execution e for a set of transactions
Execution == Seq(ExecutionElem)

\* An `ExecutionElem` is a sequence of `Transaction`s with their corresponding parent state.
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* Definition 1: s -T-> s' == [(k,v) \in s /\ (k,v) \notin s'] => k \in W_T /\ w(k,v) \in \sigma_T => (k,v) \in s.
\* Definition 2: w(k,v) -to-> r(k,v)
\* Definition 3: s -*-> s_p: restrict the valid read states for the operations in T to be no later than sp
\* Definition 4: the write set of T comprises the keys that T updates: WT = {k|w(k, v) \in \sigma T}.

\* Check types in derived specification
/\ InitValue \in Values
/\ PrintT(State)

\* Read Committed
ReadCommitted(transactions) ==
  \E execution \in executions(initialState, transactions):
    \A transaction \in transactions: CT_RC(transaction, execution)

\* Read Uncommitted
ReadUncommitted(transactions) ==
  \E execution \in executions(initialState, transactions):
    \A transaction \in transactions: CT_RU(transaction, execution)

\* Snapshot Isolation
SnapshotIsolation(transactions) ==
  \E execution \in executions(initialState, transactions):
    \A transaction \in transactions: CT_SI(transaction, execution)

\* Serializability commit test
SerializabilityDebug(initialState, transactions) ==
  \* if no executions satisfy commit test, print all executions
  /\ ~\E execution \in executions(initialState, transactions):
    \A transaction \in transactions: CT_SER(transaction, execution)
  =>
  \A execution \in executions(initialState, transactions): PrintT(<<"Execution not Serializable:",execution>>)
  \* fall back to normal check
  /\ ~\E execution \in executions(initialState, transactions):
    \A transaction \in transactions: CT_SER(transaction, execution)

\* Check types in derived specification
/\ InitValue \in Values
/\ PrintT(State)
====