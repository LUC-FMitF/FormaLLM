---- MODULE ClientCentric ----

CONSTANTS Keys = <<k1, k2, ...>>
CONSTANTS Values = <<v1, v2, ...>>
CONSTANTS InitValue = <<init_value>>
\* The initial state of the system is a map from keys to their corresponding values.
INITIAL STATE == [k \in Keys |-> InitValue]

CONSTANTS Transactions = <<t1, t2, ...>>
\* A transaction is a sequence of operations. Each operation consists of a key and a value.
LOCAL Operations(transaction) == [op \in 0..Len(transactions)-1 |-> (Keys[op], Values[op])]
\* The parent state of the execution is the last state in the execution, which corresponds to the final state of the system after applying all transactions.
LOCAL ParentState(execution) == [k \in Keys |-> InitValue]
\* A transaction can be applied to a given state by iterating over its operations and updating the parent state accordingly.
LOCAL ApplyTransaction(state, transaction) ==
  IF transaction = <<>>
  THEN state
  ELSE DOMAIN state -*-> ParentState(execution)
CONSTANTS CommitTest = <<commit_test>>
\* A commit test is a function that takes as input a transaction and an execution, and returns true if the transaction can be committed in the given execution.
LOCAL SatisfyIsolationLevel(transactions, commitTest) ==
  IF transactions = <<>>
  THEN TRUE
  ELSE \/ (EXECUTION execution IN Executions(InitialState, Transactions)) : CT_SER(transaction, execution) => SatisfyIsolationLevel(Transactions - {transaction}, CommitTest)
====