---- MODULE ClientCentric ----

(***************************************************************************)
(* A database `State` is represented by keys with corresponding values *)
(***************************************************************************)

CONSTANT Keys == {0, 1, ...}
CONSTANT Values == {0, 1, ...}
CONSTANT InitValue == 0

\* An `Operation` is a read or write of a key and value *)
TYPE Operation == [key: Keys, value: Values]

\* A `Transaction` is a total order of `Operation`s *)
TYPE Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* For simplicity we store start and commit in a lookup function *)
FUNCTION Start(t: Transaction) == t.start
FUNCTION Commit(t: Transaction) == t.commit

\* A `State` is a set of key-value pairs *)
TYPE State == [key: Keys |-> value: Values]

\* An execution e for a set of transactions T is a sequence of states, where each state corresponds to the parent state of the next transaction in T. *)
TYPE Execution == [parentState: State, transaction: Transaction, resultState: State]

\* We represent an `Execution` as a sequence of `Transaction`s with their corresponding parent state. *)
FUNCTION Executions(initialState: State, transactions: Seq(Transaction)) ==
  [e |-> ExecutionElem(parentState = initialState, transaction = t, resultState = ResultState(t))] : e \in transactions

\* A `ResultState` is the parent state of the next transaction in an execution. *)
FUNCTION ResultState(t: Transaction) ==
  IF t = <<>>
  THEN initialState
  ELSE [key |-> value] : key \in Keys, value \in Values

\* A `ReadStates` is a set of states that can be read from by an operation. *)
TYPE ReadStates == {s: State | s -T-> s'}

\* A `WriteSet` is the set of keys that are written to in a transaction. *)
TYPE WriteSet == {k: Keys | w(k, v) \in Σ}

\* A `CommitTest` is a predicate on transactions and executions that checks if an execution satisfies a given isolation level. *)
TYPE CommitTest == [t: Transaction, e: Execution] => BOOLEAN

\* A `IsolationLevel` is a predicate on transactions and executions that checks if an execution satisfies a given isolation level. *)
TYPE IsolationLevel == [t: Transaction, e: Execution] => BOOLEAN

\* A `SerializabilityCommitTest` is a commit test that checks if an execution is serializable. *)
FUNCTION CT_SER(t: Transaction, e: Execution) ==
  /\ Start(t) < Commit(e)
  /\ ResultState(t) -*-> ResultState(e)

\* A `SnapshotIsolationCommitTest` is a commit test that checks if an execution satisfies snapshot isolation. *)
FUNCTION CT_SSER(t: Transaction, e: Execution) ==
  /\ Start(t) < Commit(e)
  /\ ResultState(t) -*-> ResultState(e)

\* A `ReadCommittedCommitTest` is a commit test that checks if an execution satisfies read committed isolation. *)
FUNCTION CT_RC(t: Transaction, e: Execution) ==
  /\ Start(t) < Commit(e)
  /\ ResultState(t) -*-> ResultState(e)

\* A `ReadUncommittedCommitTest` is a commit test that checks if an execution satisfies read uncommitted isolation. *)
FUNCTION CT_RU(t: Transaction, e: Execution) ==
  /\ Start(t) < Commit(e)
  /\ ResultState(t) -*-> ResultState(e)

\* A `Serializability` is a predicate on transactions and executions that checks if an execution satisfies serializability. *)
FUNCTION Serializability(transactions: Seq(Transaction)) ==
  \/ ExecutionElem(parentState = initialState, transaction = t, resultState = ResultState(t)) : e \in Executions(initialState, transactions) /\ CT_SER(t, e)

\* A `SnapshotIsolation` is a predicate on transactions and executions that checks if an execution satisfies snapshot isolation. *)
FUNCTION SnapshotIsolation(transactions: Seq(Transaction)) ==
  \/ ExecutionElem(parentState = initialState, transaction = t, resultState = ResultState(t)) : e \in Executions(initialState, transactions) /\ CT_SSER(t, e)

\* A `ReadCommitted` is a predicate on transactions and executions that checks if an execution satisfies read committed isolation. *)
FUNCTION ReadCommitted(transactions: Seq(Transaction)) ==
  \/ ExecutionElem(parentState = initialState, transaction = t, resultState = ResultState(t)) : e \in Executions(initialState, transactions) /\ CT_RC(t, e)

\* A `ReadUncommitted` is a predicate on transactions and executions that checks if an execution satisfies read uncommitted isolation. *)
FUNCTION ReadUncommitted(transactions: Seq(Transaction)) ==
  \/ ExecutionElem(parentState = initialState, transaction = t, resultState = ResultState(t)) : e \in Executions(initialState, transactions) /\ CT_RU(t, e)

\* A `IsolationLevel` is a predicate on transactions and executions that checks if an execution satisfies a given isolation level. *)
FUNCTION IsolationLevel(level: IsolationLevel, transactions: Seq(Transaction)) ==
  \/ ExecutionElem(parentState = initialState, transaction = t, resultState = ResultState(t)) : e \in Executions(initialState, transactions) /\ level(t, e)

\* A `SerializabilityDebug` is a predicate on transactions and executions that checks if an execution satisfies serializability. *)
FUNCTION SerializabilityDebug(initialState: State, transactions: Seq(Transaction)) ==
  \/ ExecutionElem(parentState = initialState, transaction = t, resultState = ResultState(t)) : e \in Executions(initialState, transactions) /\ CT_SER(t, e)

\* A `SnapshotIsolationDebug` is a predicate on transactions and executions that checks if an execution satisfies snapshot isolation. *)
FUNCTION SnapshotIsolationDebug(initialState: State, transactions: Seq(Transaction)) ==
  \/ ExecutionElem(parentState = initialState, transaction = t, resultState = ResultState(t)) : e \in Executions(initialState, transactions) /\ CT_SSER(t, e)

\* A `ReadCommittedDebug` is a predicate on transactions and executions that checks if an execution satisfies read committed isolation. *)
FUNCTION ReadCommittedDebug(initialState: State, transactions: Seq(Transaction)) ==
  \/ ExecutionElem(parentState = initialState, transaction = t, resultState = ResultState(t)) : e \in Executions(initialState, transactions) /\ CT_RC(t, e)

\* A `ReadUncommittedDebug` is a predicate on transactions and executions that checks if an execution satisfies read uncommitted isolation. *)
FUNCTION ReadUncommittedDebug(initialState: State, transactions: Seq(Transaction)) ==
  \/ ExecutionElem(parentState = initialState, transaction = t, resultState = ResultState(t)) : e \in Executions(initialState, transactions) /\ CT_RU(t, e)

\* A `IsolationLevelDebug` is a predicate on transactions and executions that checks if an execution satisfies a given isolation level. *)
FUNCTION IsolationLevelDebug(level: IsolationLevel, initialState: State, transactions: Seq(Transaction)) ==
  \/ ExecutionElem(parentState = initialState, transaction = t, resultState = ResultState(t)) : e \in Executions(initialState, transactions) /\ level(t, e)

\* A `PrintT` is a function that prints an execution. *)
FUNCTION PrintT(execution: Execution) ==
  <<"try execution:",execution>>

\* A `SerializabilityCommitTest` is a commit test that checks if an execution is serializable. *)
FUNCTION SerializabilityCommitTest(initialState: State, transactions: Seq(Transaction)) ==
  \/ ExecutionElem(parentState = initialState, transaction = t, resultState = ResultState(t)) : e \in Executions(initialState, transactions) /\ CT_SER(t, e)

\* A `SnapshotIsolationCommitTest` is a commit test that checks if an execution satisfies snapshot isolation. *)
FUNCTION SnapshotIsolationCommitTest(initialState: State, transactions: Seq(Transaction)) ==
  \/ ExecutionElem(parentState = initialState, transaction = t, resultState = ResultState(t)) : e \in Executions(initialState, transactions) /\ CT_SSER(t, e)

\* A `ReadCommittedCommitTest` is a commit test that checks if an execution satisfies read committed isolation. *)
FUNCTION ReadCommittedCommitTest(initialState: State, transactions: Seq(Transaction)) ==
  \/ ExecutionElem(parentState = initialState, transaction = t, resultState = ResultState(t)) : e \in Executions(initialState, transactions) /\ CT_RC(t, e)

\* A `ReadUncommittedCommitTest` is a commit test that checks if an execution satisfies read uncommitted isolation. *)
FUNCTION ReadUncommittedCommitTest(initialState: State, transactions: Seq(Transaction)) ==
  \/ ExecutionElem(parentState = initialState, transaction = t, resultState = ResultState(t)) : e \in Executions(initialState, transactions) /\ CT_RU(t, e)

\* A `IsolationLevelCommitTest` is a commit test that checks if an execution satisfies a given isolation level. *)
FUNCTION IsolationLevelCommitTest(level: IsolationLevel, initialState: State, transactions: Seq(Transaction)) ==
  \/ ExecutionElem(parentState = initialState, transaction = t, resultState = ResultState(t)) : e \in Executions(initialState, transactions) /\ level(t, e)
====