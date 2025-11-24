---- MODULE ClientCentric ----

(***************************************************************************)
(* TODO InitValue could be bottom (_|_)                                     *)
(***************************************************************************)

CONSTANT Keys == {0, 1, 2}
CONSTANT Values == {0, 1, 2}
CONSTANT InitValue == 0

LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences

\* A database `State` is represented by keys with corresponding values
DATATYPE State == [k \in Keys |-> v \in Values]

\* An `Operation` is a read or write of a key and value
DATATYPE Operation ==
  Read(k \in Keys)
/ Write(k \in Keys, v \in Values)

\* A `Transaction` is a total order of `Operation`s
DATATYPE Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* For simplicity we store start and commit in a lookup function
FUNCTION Start(t: Transaction) == t.start
FUNCTION Commit(t: Transaction) == t.commit

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s`
FUNCTION IsCompleteFor(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w

\* readStatesForEmptyTransaction contains all previous states, to ensure that empty txns do not incorrectly invalidate the checked isolation level
CONSTANT readStatesForEmptyTransaction == {[k \in Keys |-> InitValue] : k \in Keys}

\* The write set of T comprises the keys that T updates: WT = {k|w(k, v) ∈ ΣT }.
\* For simplicity of exposition, we assume that a transaction only writes a key once.
FUNCTION WriteSet(T: Seq(Transaction)) ==
  LET
    w == {}
  IN \A t \in T:
    IF t = Read(k)
    THEN k \in w
    ELSE k \in w /\ v \in Values

\* By convention, write operations have read states too: for a write operation in T , they include all states in Se up to and including T ’s parent state.
FUNCTION ReadStates(T: Seq(Transaction)) ==
  LET
    s_p == ParentState(T)
    w == WriteSet(T)
  IN {[k \in Keys |-> InitValue] : k \in w} UNION {s_p}

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s`
FUNCTION IsCompleteFor(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
    ELSE k \in s /\ v \in w
  /\ w <= s_p

\* A state `s` is consistent with `T` in `e` if every operation in `T` can read from `s` and the write set of T is a subset of the keys in `s`.
FUNCTION IsConsistentWith(s: State, T: Seq(Transaction)) ==
  LET
    s_p == ParentState(s, T)
    w == WriteSet(T)
  IN \A op \in T.ops:
    IF op = Read(k)
    THEN k \in s /\ k \in w
====