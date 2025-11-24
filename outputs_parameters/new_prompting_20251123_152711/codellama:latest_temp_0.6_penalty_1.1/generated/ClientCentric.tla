---- MODULE ClientCentric ----

CONSTANT Keys
CONSTANT Values
CONSTANT InitValue
VARIABLE State == <<>>
VARIABLE Seq == []
INVARIANTS
\* The parent state is the last state in the execution
Definition1(parentState, transaction) ==
  IF transaction = []
  THEN TRUE
  ELSE [k \in Keys |-> InitValue] \* makes it level-1 therefore pass it in
  /\ store ExecutionElem(parentState, transaction)
  /\ calculateNextState(transaction)
  /\ recoverExecutionElements
  /\ checkCommitTest(commitTest, execution)
SerializabilityDebug(initialState, transactions) ==
  IF noExecutionsSatisfyCommitTest(initialState, transactions)
  THEN PrintT(<<"try execution:",execution>>)
  ELSE \A execution \in executions(initialState, transactions): PrintT(<<"Execution not Serializable:",execution>>)
ReadCommittedDebug(initialState, transactions) ==
  IF noExecutionsSatisfyCommitTest(initialState, transactions)
  THEN PrintT(<<"try execution:",execution>>)
  ELSE \A execution \in executions(initialState, transactions): PrintT(<<"Execution not Serializable:",execution>>)
ReadUncommittedDebug(initialState, transactions) ==
  IF noExecutionsSatisfyCommitTest(initialState, transactions)
  THEN PrintT(<<"try execution:",execution>>)
  ELSE \A execution \in executions(initialState, transactions): PrintT(<<"Execution not Serializable:",execution>>)
\* Helper: checks if specific execution satisfies given commit test
checkCommitTest(commitTest, execution) ==
  IF noExecutionsSatisfyCommitTest(initialState, transactions)
  THEN \A transaction \in transactions: CT_SER(transaction, execution)
  ELSE TRUE
\* Fall back to normal check
noExecutionsSatisfyCommitTest(initialState, transactions) ==
  IF noExecutionsExist(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
checkExecutionForCommitTest(execution, commitTest) ==
  IF execution = []
  THEN TRUE
  ELSE [k \in Keys |-> InitValue] \* makes it level-1 therefore pass it in
  /\ store ExecutionElem(parentState, transaction)
  /\ calculateNextState(transaction)
  /\ recoverExecutionElements
  /\ checkCommitTest(commitTest, execution)
\* Helper: checks if any executions satisfy given commit test
noExecutionsExist(initialState, transactions) ==
  IF noExecutionsExistInAllPossiblePermutations(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistInAllPossiblePermutations(initialState, transactions) ==
  IF noExecutionsExistInAllPossiblePermutationsHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistInAllPossiblePermutationsHelper(initialState, transactions) ==
  IF noExecutionsExistInAllPossiblePermutationsHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistInAllPossiblePermutationsHelperHelper(initialState, transactions) ==
  IF noExecutionsExistInAllPossiblePermutationsHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistInAllPossiblePermutationsHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistInAllPossiblePermutationsHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistInAllPossiblePermutationsHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistInAllPossiblePermutationsHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistInAllPossiblePermutationsHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistInAllPossiblePermutationsHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistInAllPossiblePermutationsHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistInAllPossiblePermutationsHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistInAllPossiblePermutationsHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistInAllPossiblePermutationsHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistInAllPossiblePermutationsHelperHelper(initialState, transactions) ==
  IF noExecutionsExistInAllPossiblePermutationsHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistInAllPossiblePermutationsHelper(initialState, transactions) ==
  IF noExecutionsExistInAllPossiblePermutationsHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistInAllPossiblePermutations(initialState, transactions) ==
  IF noExecutionsExistInAllPossiblePermutations(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Fall back to normal check
noExecutionsExist(initialState, transactions) ==
  IF noExecutionsExistHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
\* Helper: checks if any executions satisfy given commit test in all possible permutations of transactions
noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions) ==
  IF noExecutionsExistHelperHelperHelperHelperHelperHelper(initialState, transactions)
  THEN TRUE
  ELSE /\ checkExecutionForCommitTest(execution, commitTest)
====