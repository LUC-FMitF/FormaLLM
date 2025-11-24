---- MODULE ClientCentric ----

(*****************************************************************************)
(* Define State Machine for Isolation Specification                          *)
(*****************************************************************************)

LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences

\* Helper: checks if specific execution satisfies given commit test
Helper(initialState, transactions, commitTest) ==
  IF commitTest = CT_SERIALIZABILITY
  THEN \/ \E execution \in Execution(initialState, transactions) : CT_SERIALIZABILITY(execution)
  ELSE
    IF commitTest = CT_READ_COMMITTED
    THEN \/ \E execution \in Execution(initialState, transactions) : CT_READ_COMMITTED(execution)
    ELSE
      IF commitTest = CT_READ_UNCOMMITTED
      THEN \/ \E execution \in Execution(initialState, transactions) : CT_READ_UNCOMMITTED(execution)
      ELSE FALSE

\* Initial state of the system
INITIAL_STATE == <<>>

\* Set of all possible transactions
TRANSACTIONS == {
  [
    id   |-> i,
    ops |-> Seq(
      [
        key |-> k,
        type |->
          IF type = WRITE
          THEN WRITE
          ELSE READ
      ] : op : ops
    )
  ] : transaction : transactions
}

\* Function to calculate next state given a transaction
CalculateNextState(state, transaction) ==
  LET
    ops = transaction.ops
    RECURSIVE
    ApplyOp(s, op) ==
      IF op.type = WRITE
      THEN [key |-> op.key, value |-> op.value] \* set value for key
      ELSE [key |-> op.key, value |-> s[op.key].value] \* read value for key
  IN
    [key |-> value] : key : DOMAIN state \* merge with previous state
      /\ op.type = WRITE
      /\ ApplyOp(state, op)
      /\ ~(op.key \in ops \* previous operation is a write on same key)
      /\ ~(op.key \in DOMAIN state \* previous operation is a read on same key)

\* Function to generate all possible permutations of a set of transactions
Execution(initialState, transactions) ==
  IF transactions = {}
  THEN [[parentState: initialState, transaction: <<>>, resultState: initialState]]
  ELSE UNION {
    [parentState: initialState, transaction: transaction, resultState: CalculateNextState(initialState, transaction)] : transaction : transactions
  }

\* Function to check if a given execution satisfies a given commit test
CT_SERIALIZABILITY(execution) ==
  IF execution.transaction = <<>>
  THEN TRUE
  ELSE
    LET
      ops = execution.transaction.ops
      RECURSIVE
      WriteSet(op) ==
        IF op.type = WRITE
        THEN [key |-> op.key]
        ELSE []
      ReadSet(op) ==
        IF op.type = READ
        THEN [key |-> op.key]
        ELSE []
      WriteReadConflict(op) ==
        IF op.type = WRITE
        THEN ReadSet(op) \* read set for write
        ELSE []
    IN
      IF ReadSet(execution.transaction.ops) \* check read set for transaction
      THEN
        LET
          RECURSIVE
          WriteReadConflict(_, _, _)
          WriteReadConflict(s1, s2, i) ==
            IF i = 0
            THEN WriteReadConflict(s1, s2, i + 1)
            ELSE WriteReadConflict(s1[i-1], s2, i + 1) \* check write read conflict
        IN
          WriteReadConflict(execution.transaction.ops, execution.transaction.ops, 0) \* check write read conflict
      ELSE FALSE

CT_READ_COMMITTED(execution) ==
  IF execution.transaction = <<>>
  THEN TRUE
  ELSE
    LET
      ops = execution.transaction.ops
      RECURSIVE
      ReadSet(op) ==
        IF op.type = READ
        THEN [key |-> op.key]
        ELSE []
    IN
      IF ReadSet(execution.transaction.ops) \* check read set for transaction
      THEN
        LET
          RECURSIVE
          ReadSet(_, _, _)
          ReadSet(s1, s2, i) ==
            IF i = 0
            THEN ReadSet(s1, s2, i + 1)
            ELSE ReadSet(s1[i-1], s2, i + 1) \* check read set
        IN
          ReadSet(execution.transaction.ops, execution.transaction.ops, 0) \* check read set
      ELSE FALSE

CT_READ_UNCOMMITTED(execution) ==
  IF execution.transaction = <<>>
  THEN TRUE
  ELSE
    LET
      ops = execution.transaction.ops
      RECURSIVE
      ReadSet(op) ==
        IF op.type = READ
        THEN [key |-> op.key]
        ELSE []
    IN
      IF ReadSet(execution.transaction.ops) \* check read set for transaction
      THEN
        LET
          RECURSIVE
          ReadSet(_, _, _)
          ReadSet(s1, s2, i) ==
            IF i = 0
            THEN ReadSet(s1, s2, i + 1)
            ELSE ReadSet(s1[i-1], s2, i + 1) \* check read set
        IN
          ReadSet(execution.transaction.ops, execution.transaction.ops, 0) \* check read set
      ELSE FALSE

\* Print all possible executions for a given transaction
PrintExecution(execution) ==
  Print(<<"Executions for transaction:", execution.transaction>>)

\* Print all possible executions for a given set of transactions
PrintExecutions(transactions) ==
  Print(<<"Executions for transactions:", transactions>>)
  /\ [execution |-> Execution(INITIAL_STATE, transactions)] : execution : Execution(INITIAL_STATE, transactions)

\* Helper: checks if specific execution satisfies given commit test
PrintCommitTest(initialState, transactions, commitTest) ==
  Print(<<"Commit Test:", commitTest>>)
  /\ [execution |-> Execution(initialState, transactions)] : execution : Execution(initialState, transactions)
  /\ Print(<<"Executions:", PrintExecution(execution)>>)

\* Function to check if a given execution satisfies a given commit test
CommitTest(initialState, transactions, commitTest) ==
  IF commitTest = CT_SERIALIZABILITY
  THEN \/ \E execution \in Execution(initialState, transactions) : CT_SERIALIZABILITY(execution)
  ELSE
    IF commitTest = CT_READ_COMMITTED
    THEN \/ \E execution \in Execution(initialState, transactions) : CT_READ_COMMITTED(execution)
    ELSE
      IF commitTest = CT_READ_UNCOMMITTED
      THEN \/ \E execution \in Execution(initialState, transactions) : CT_READ_UNCOMMITTED(execution)
      ELSE FALSE

\* Function to check if a given execution satisfies a given isolation level
SatisfyIsolationLevel(transactions, isolationLevel) ==
  CommitTest(INITIAL_STATE, transactions, isolationLevel)

\* Function to check if a given execution satisfies a given isolation level
SatisfyIsolationLevel(initialState, transactions, isolationLevel) ==
  CommitTest(initialState, transactions, isolationLevel)

\* Function to check if a given set of transactions satisfies a given isolation level
SatisfyIsolationLevel(transactions, isolationLevel) ==
  CommitTest(INITIAL_STATE, transactions, isolationLevel)

\* Function to check if a given set of transactions satisfies a given isolation level
SatisfyIsolationLevel(initialState, transactions, isolationLevel) ==
  CommitTest(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given commit test
CommitDebug(initialState, transactions, commitTest) ==
  Print(<<"Commit Test:", commitTest>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, commitTest)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation level
IsolationDebug(initialState, transactions, isolationLevel) ==
  Print(<<"Isolation Level:", isolationLevel>>)
  /\ Print(<<"Executions:", PrintExecutions(transactions)>>)
  /\ SatisfyIsolationLevel(initialState, transactions, isolationLevel)

\* Debug function to check if a given execution satisfies a given isolation
====