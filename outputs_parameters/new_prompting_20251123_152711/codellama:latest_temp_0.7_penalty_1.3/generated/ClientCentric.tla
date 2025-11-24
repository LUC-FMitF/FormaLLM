---- MODULE ClientCentric ----
----------------------------- ------------
CONSTANTS Keys = <<"k1", "k2">>
INITIALIZE INITVALUES {InitValue |-> 0} \* initial value for all keys is zero *\/
LOCAL Instance FiniteSets
LOCAL Instance Naturals

\*\* The parent state of a transaction is the last state in the execution that generated it. \*\/
FUNCTION ParentState(e: ExecutionElem) : State = e.parentState

\*\* A read operation can only be performed on states before or equal to the current time stamp.\*\*
CONSTRAINT ReadStates <= {s | s -T-> _}: (t \in TimeStamp, s: ParentState(e)) => t <= s.time}

\*\* The write set of a transaction is the keys that are written by this transaction.\*\*
FUNCTION WriteSet(transaction) : Set = {k | w(k, v)}

\*\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s`. \*\/
CONSTRAINT CompleteFor <= (t: Transaction) -> e: ExecutionElem : s -*-> ParentState(e): {s | t.ops = ReadStates}

\*\* By convention, write operations have read states too.\*\*
FUNCTION AllReadStatesInWriteSet => w(k, v) -to-> r(k,v)  /\ k \in Keys: (t: Transaction): WriteSet(t).containsKey }

\*\* A transaction is serializable if it satisfies the commit test.\*\*
CONSTRAINT Serializability => CT_SER(transaction.ops, ExecutionElem)
LOCAL FUNCTION SatisfiesCommitTest(execution: ExecutionElem): BOOL = {TRUE} /\ FALSE }
FUNCTION TransactionsAreSerializable => \A t1: Transaction / T2:Transaction : (t1 <T-> 0 AND t2.start > t1.commit) -> ~SatisfiesCommitTest(ExecutionElem({transaction=t1, start = t1.start}, {transaction=t2}))
FUNCTION SerializabilityDebug => \A initialState: State / transactions: Set : (transactions -T-> 0 AND INITVALUES <= initValues): !TransactionsAreSerializable(initialState, transactions) /\ PrintT("Execution not serializable", ExecutionElem({transaction=t1}, {transaction=t2}))
LOCAL FUNCTION SerializabilityCheck => \A initialState: State / transactions: Set : (transactions -T-> 0 AND INITVALUES <= initValues): !TransactionsAreSerializable(initialState, transactions) /\ PrintT("Execution not serializable", ExecutionElem({transaction=t1}, {transaction=t2}))
FUNCTION ReadCommitted => \A initialState: State / transaction: Transaction : (INITVALUES <= InitValue ): SerializabilityCheck()/\PrintT(<<"try execution:">>,ExecutionElem({initialState = InitialState},{Transaction.ops=[r1]}, {ResultState=InitialState}))
FUNCTION ReadUncommitted => \A initialState: State / transaction: Transaction : (INITVALUES <= InitValue ): SerializabilityCheck()/\PrintT(<<"try execution:">>,ExecutionElem({initialState = InitialState},{Transaction.ops=[r1]}, {ResultState=InitialState}))
FUNCTION SnapshotIsolation => \A initialState: State / transaction: Transaction : (INITVALUES <= InitValue ): SerializabilityCheck()/\PrintT(<<"try execution:">>,ExecutionElem({initialState = InitialState},{Transaction.ops=[r1]}, {ResultState=InitialState}))
\*\* Helper function to check if a transaction is serializable.\*\*
LOCAL FUNCTION SatisfiesCommitTest(_: ExecutionElem): BOOL /\ TRUE }
====