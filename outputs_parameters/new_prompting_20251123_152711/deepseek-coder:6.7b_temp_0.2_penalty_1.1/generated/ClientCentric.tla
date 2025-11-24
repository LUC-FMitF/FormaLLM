---- MODULE ClientCentric -----------------------------------------
EXTENDS FiniteSets, Naturals, Sequences

CONSTANTS Values == {0, 1} \ UNION {2, ..., MAX_VALUE},
           Keys   == {0, 1} \ UNION {2, ..., MAX_KEY},
           InitValue == BOTTOM

TYPE State      == [k \in Keys |-> v \in Values]
     Operation  == [op: {"Read", "Write"}, key: Key, value: Value]
     Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp],
     ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* Helpers representing Reads and Writes
ReadOp(key)   == [op = "Read", key = key, value = s[key]]
WriteOp(key, value) == [op = "Write", key = key, value = value]

\* The set of all possible permutations of executions given a set of transactions
LOCAL Permutations(transactions) == 
  IF EmptySet(transactions)
  THEN {}
  ELSE {p \in Transaction |-> p} UNION {t \in transactions |-> t U p : p \in Permutations(transactions - {t})}

\* Given system state and single transaction, determines new state
LOCAL NextState(s: State, t: Transaction) == 
  IF EmptySet(t.ops)
  THEN s
  ELSE A[i \in ZIndices(t.ops) |-> (t.ops)[i].key = s[(t.ops)[i].key] : i = 0..Len(t.ops)-1]

\* Lists all possible permutations of executions given set of transactions
LOCAL Executions(transactions: Set(Transaction)) == 
  IF EmptySet(transactions)
  THEN {}
  ELSE {e \in Transaction |-> e} UNION {t \in transactions |-> t U e : e \in Executions(transactions - {t})}

\* Helper: checks if specific execution satisfies given commit test
LOCAL CT_SER(transaction, execution) == 
  LET s == initialState,
      ts == transaction.start
  IN ALL t \in execution |-> (s[t.key] = t.value AND t.commit <= ts) => s[t.key] = t.value

\* Definition 5 Given a set of transactions T and their read states,
a storage system satisfies an isolation level I iff ∃e:∀t ∈ T :CTI(t,e).
LOCAL satisfyIsolationLevel(transactions, CT_SER) == 
  EXISTS execution \in Executions(transactions) |-> ALL transaction \in transactions => CT_SER(transaction, execution)

\* Serializability commit test
LOCAL COMMITTED == [t1: Transaction, t2: Transaction] ==> 
  LET ts1 == t1.commit,
      ts2 == t2.commit
  IN (ts1 < ts2 => NextState(initialState, t1) <= NextState(NextState(initialState, t1), t2))

\* Read Committed
LOCAL READ_COMMITTED == [t: Transaction] ==> EXISTS execution \in Executions({t}) |-> ALL transaction \in {t} => CT_SER(transaction, execution)

\* Read Uncommitted
LOCAL READ_UNCOMMITTED == [t1: Transaction, t2: Transaction] ==> 
  LET ts1 == t1.start,
      ts2 == t2.start
  IN (ts1 < ts2 => NextState(initialState, t1) <= NextState(NextState(initialState, t1), t2))
====