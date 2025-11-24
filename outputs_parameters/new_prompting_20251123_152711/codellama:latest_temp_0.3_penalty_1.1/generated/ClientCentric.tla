---- MODULE ClientCentric ----

(***************************************************************************)
(* TODO InitValue could be bottom (_|_)                                     *)
(* TLA+ specifications of Client Centric Isolation Specification by Crooks et al: https://dl.acm.org/doi/10.1145/3087801.3087802 *)
(***************************************************************************)

CONSTANT Keys == {k \in 0..n-1 |-> v: Values}
CONSTANT Values == {v \in 0..m-1 |-> v: Values}
CONSTANT InitValue == <<>>

LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
  
\* A database `State` is represented by keys with corresponding values
State == [k \in Keys |-> v: Values]

\* An `Operation` is a read or write of a key and value
Operation == [op: Read | Write, k \in Keys, v: Values]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* For simplicity we store start and commit in a lookup function
startLookup == [t \in Transactions |-> t.start]
commitLookup == [t \in Transactions |-> t.commit]

\* An execution e for a set of transactions T is a sequence of operations
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* We represent an `Execution` as a sequence of `Transaction`s with their corresponding parent state.
Executions(initialState, transactions) ==
  [e \in ExecutionElems |-> e.transaction = (t \in Transactions |-> t)]

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s]

\* readStatesForEmptyTransaction contains all previous states, to ensure that empty txns do not incorrectly invalidate the checked isolation level
readStatesForEmptyTransaction == {s \in States |-> TRUE}

\* The write set of T comprises the keys that T updates: WT = {k|w(k, v) ∈ ΣT }.
WriteSet(T) == [k \in Keys |-> w(k, v) \in Values]

\* For simplicity of exposition, we assume that a transaction only writes a key once.
WriteOnce(T) == [t \in Transactions |-> t.ops = (op \in T.ops |-> op.op = Write)]

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
completeFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op.k \in s /\ (op.op = Read => op.v \in s)] /\ WriteSet(T) <= s

\* A state `s` is valid for `T` in `e` if every operation in `T` can read from `s` and the write set of `T` is a subset of `s`
validFor(s, T) ==
  IF s = <<>>
  THEN TRUE
  ELSE [op \in T.ops |-> op
====