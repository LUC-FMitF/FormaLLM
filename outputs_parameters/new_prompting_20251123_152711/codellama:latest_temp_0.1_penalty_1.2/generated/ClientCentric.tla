---- MODULE ClientCentric ----

CONSTANTS Keys = <<k1, k2, ...>>
CONSTANTS Values = <<v1, v2, ...>>
CONSTANTS InitValue = <<init_value>>
\* The initial state of the system is a map from keys to their corresponding values.
INITIAL STATE == [k \in Keys |-> InitValue]

CONSTANTS Transactions = <<t1, t2, ...>>
\* An execution is a sequence of transactions.
INITIAL STATE == [ops: Seq(Transaction), start: TimeStamp]
============================= MODULE Execution ============================
CONSTANTS ReadStates = <<s1, s2, ...>>
\* A set of states in which a transaction can read its value.
INITIAL STATE == [readStates: Set(State)]
============================= MODULE Helpers ============================
CONSTANTS InitialState = <<k \in Keys |-> InitValue>>
\* The initial state of the system is a map from keys to their corresponding values.
INITIAL STATE == [initialState: State]
============================= MODULE Executions ============================
CONSTANTS Transactions = <<t1, t2, ...>>
\* A set of transactions.
INITIAL STATE == [transactions: Set(Transaction)]
============================= MODULE Isolation ============================
CONSTANTS CommitTest = <<commit_test>>
\* A commit test is a function that takes a transaction and an execution as input, and returns whether the transaction can be committed in the given execution.
INITIAL STATE == [commitTest: (Transaction \X Execution) -> Bool]
============================= MODULE Serializability ============================
CONSTANTS Transactions = <<t1, t2, ...>>
\* A set of transactions.
INITIAL STATE == [transactions: Set(Transaction)]
============================= MODULE SnapshotIsolation ============================
CONSTANTS Transactions = <<t1, t2, ...>>
\* A set of transactions.
INITIAL STATE == [transactions: Set(Transaction)]
============================= MODULE ReadCommitted ============================
CONSTANTS Transactions = <<t1, t2, ...>>
\* A set of transactions.
INITIAL STATE == [transactions: Set(Transaction)]
============================= MODULE ReadUncommitted ============================