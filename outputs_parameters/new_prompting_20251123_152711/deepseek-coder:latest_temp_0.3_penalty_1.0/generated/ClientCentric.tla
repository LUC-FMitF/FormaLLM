---- MODULE ClientCentric ----
MODULE TLC_Config

CONSTANTS
  INIT_VALUE  _|_
  TIMESTAMP   _|_

SPECIFICATION Spec

INVARIANTS
  InitValue  _|_
  TimeStamp  _|_

LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences

\* The empty zero-indexed sequence
EmptyZSeq == <<>>

\* The set of valid indices for zero-indexed sequence s
ZIndices(s) ==
  IF s  EQ  EmptyZSeq
  THEN  {}
  ELSE DOMAIN s

\* The set of all zero-indexed sequences of elements in S with length n
LOCAL ZSeqOfLength(S, n) ==
  IF n  EQ 0
  THEN  {EmptyZSeq}
  ELSE  [0  ..  (n  - 1)  -> S]

\* The set of all zero-indexed sequences of elements in S
ZSeq(S) == UNION  {ZSeqOfLength(S, n)  : n  \in Nat}

\* The length of zero-indexed sequence s
ZLen(s) ==
  IF s  EQ  EmptyZSeq
  THEN 0
  ELSE Cardinality(DOMAIN s)

\* Converts from a one-indexed sequence to a zero-indexed sequence
ZSeqFromSeq(seq) ==
  IF seq  EQ  _|_
  THEN EmptyZSeq
  ELSE [i  \in 0  ..  (ZLen(seq)  - 1)  -> seq[i+ 1]]

\* Converts from a zero-indexed sequence to a one-indexed sequence
SeqFromZSeq(zseq) ==
  IF zseq  EQ  _|_
  THEN <<>>
  ELSE [i  \in 1  ..  ZLen(zseq)  -> zseq[i- 1]]

\* Lexicographic order on zero-indexed sequences a and b
a  \preceq b ==
  LET
    s1len  EQ  ZLen(a)
    s2len  EQ  ZLen(b)
    RECURSIVE IsLexLeq(_,  _,  _)
    IsLexLeq(s1, s2, i)  EQ
      CASE i  EQ  s1len  /\ i  EQ s2len  -> s1len  LESS s2len
       [] s1[i]  LESS s2[i]  -> FALSE
       [] s1[i]  GREATER s2[i]  -> TRUE
       [] OTHER  -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(a, b, 0)

\* Rotate the string s to the left by r indices
Rotation(s, r) ==
  IF s  EQ  EmptyZSeq
  THEN EmptyZSeq
  ELSE [i  \in ZIndices(s)  -> s[(i +  r)  % ZLen(s)]]

\* The set of all rotations of zero-indexed sequence s
Rotations(s) ==
  IF s  EQ  EmptyZSeq
  THEN  {}
  ELSE  [
      {
          shift  :  r,
          seq     :  Rotation(s, r)
      }  :  r  \in ZIndices(s)
  ]

\* State
State  EQ  [k  \in Keys  -> InitValue]  *

\* Transaction
Transaction  EQ  [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* Transaction TimeStamp
TimeStamp  EQ  [t1  \preceq t2  -> ~E (t1  -  t2 )  \in TIMESTAMP]

\* Execution
Execution  EQ  [parentState: State, transaction: Transaction, resultState: State]

\* ExecutionElem
ExecutionElem  EQ  [parentState: State, transaction: Transaction, resultState: State]

\* Read states
ReadStates  EQ  [s  -*-> s_p  -> ~E (s  -  s_p )  \in s]

\* CTI
CTI  EQ  [t: Transaction  -> e: Execution  -> e  IN  t  -> TRUE]

\* Executions
Executions  EQ  [e  \in  T  -> e  IN  transactions  -> TRUE]

\* CT_SER
CT_SER  EQ  [t: Transaction  -> e: Execution  -> e  IN  T  -> t  IN  e  -> TRUE]

\* CT_SSER
CT_SSER  EQ  [t: Transaction  -> e: Execution  -> e  IN  T  -> t  IN  e  -> t  IN  T  -> TRUE]

\* Snapshot Isolation
SnapshotIsolation  EQ  [T: Seq(Transaction)  -> t: Transaction  -> s_T: State  -> s_T  IN  T  -> s_T  EQ  s_T′  -> s_T′  IN  T  -> TRUE]

\* Strict Serializability
StrictSerializability  EQ  [T: Seq(Transaction)  -> t: Transaction  -> s_T: State  -> s_T  IN  T  -> s_T  EQ  s_T′  -> s_T′  IN  T  -> s_T  EQ  s_T′  -> TRUE]

\* Read Committed
ReadCommitted  EQ  [T: Seq(Transaction)  -> t: Transaction  -> s_T: State  -> s_T  IN  T  -> s_T  EQ  s_T′  -> s_T′  IN  T  -> s_T  EQ  s_T′  -> TRUE]

\* Check types in derived specification
CheckTypes  EQ  [T: Seq(Transaction)  -> t: Transaction  -> s_T: State  -> s_T  IN  T  -> s_T  EQ  s_T′  -> s_T′  IN  T  -> s_T  EQ  s_T′  -> TRUE]

\* PrintT
PrintT  EQ  [t: Transaction  -> e: Execution  -> e  IN  t  -> TRUE]

\* Serializability
Serializability  EQ  [T: Seq(Transaction)  -> t: Transaction  -> s_T: State  -> s_T  IN  T  -> s_T  EQ  s_T′  -> s_T′  IN  T  -> s_T  EQ  s_T′  -> TRUE]

\* SerializabilityDebug
SerializabilityDebug  EQ  [s: State  -> transactions: Seq(Transaction)  -> s  IN  transactions  -> TRUE]

END SPECIFICATION Spec

END MODULE TLC_Config
====