---- MODULE ClientCentric ----
EXTENDS FiniteSets, Naturals, Sequences

CONSTANTS
  InitValue == _|_
  Keys == {...}
  Values == {...}

ASSUME
  \* InitValue \in Values
  \* PrintT(State)

\* The definition of State
State == [k \in Keys |-> Value]

\* An operation is a read or write of a key and value
Operation == [op: {"read", "write"}, key: Keys, value: Values]

\* Helpers representing Reads and Writes
IsRead(op) == op.op = "read"
IsWrite(op) == op.op = "write"

\* A transaction is a total order of operations
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* Represent an execution as a sequence of transactions with their corresponding parent state
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* The parent state is the last state in the execution
CT_PARENT(s, T) == [k, v] \in s /\ [k, v] \notin T.parentState

\* Definition 1
CT_DEF(s, T) == [(k, v) \in s /\ (k, v) \notin T.resultState] => k \in W_T /\ w(k, v) \in \Sigma_T => (k, v) \in s

\* Definition 5
CT_SER(T, e) == EXISTS execution \in e: \A t \in T: CT_DEF(t.parentState, t) /\ CT_PARENT(t.parentState, t) = e.parentState

\* Serializability commit test
CT_SER_COMMIT(initialState, transactions) ==
  \* if no executions satisfy commit test, print all executions
  (~\E execution \in executions(initialState, transactions): \A transaction \in transactions: CT_SER(transaction, execution))
  => \A execution \in executions(initialState, transactions): PrintT(<<"Execution not Serializable:",execution>>)
  \* fall back to normal check
  \/ \E execution \in executions(initialState, transactions): \A transaction \in transactions: CT<｜begin▁of▁sentence｜>

\* Snapshot Isolation
CT_SSER(timestamps) == \A T \in transactions: T.start < timestamps.t /\ T.commit \geq timestamps.t

\* Read Committed
CT_RC(timestamps) == \A T \in transactions: T.start < timestamps.t /\ T.commit \geq timestamps.t

\* Read Uncommitted
CT_RU(timestamps) == TRUE

\* Check types in derived specification
CT_CHECK_TYPES == \A T \in transactions: \A op \in T.ops: op.key \in Keys /\ op.value \in Values

\* Helper: checks if specific execution satisfies given commit test
CT_SER_EXEC(commitTest, transactions, execution) == commitTest(transactions, execution)

\* tests there exists an execution for transactions, that satisfies the isolation level given by commitTest
CT_SER_LEVEL(transactions, commitTest) == EXISTS execution \in executions(initialState, transactions): CT_SER_EXEC(commitTest, transactions, execution)

=============================================================================
====