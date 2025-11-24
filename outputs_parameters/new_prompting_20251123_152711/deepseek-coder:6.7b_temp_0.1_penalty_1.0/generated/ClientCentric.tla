---- MODULE ClientCentric ----
EXTENDS FiniteSets, Naturals, Sequences

CONSTANTS
  InitValue == _|_
  Keys == {...}
  Values == {...}

\* A database `State` is represented by keys with corresponding values
State == [k \in Keys |-> Value]

\* An `Operation` is a read or write of a key and value
Operation == [op: {"Read", "Write"}, key: Key, value: Value]

\* Helpers representing Reads and Writes
Read(key, value) == [op: "Read", key: key, value: value]
Write(key, value) == [op: "Write", key: key, value: value]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* ExecutionElem represents an execution of a transaction
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* Execution represents a sequence of `Transaction`s with their corresponding parent state
Execution == Seq(ExecutionElem)

\* The parent state is the last state in the execution
ParentState(execution) == LAST(execution).parentState

\* Definition of state transition
s -T-> s' == [(k,v) \in s /\ (k,v) \notin s' => k \in W_T /\ w(k,v) \in \sigma_T => (k,v) \in s]

\* The write set of T comprises the keys that T updates
WT(transaction) == {k |-> v \in transaction.ops /\ w(k,v) \in \sigma_T}

\* Denoting the set of keys in which s and s′ differ as ∆(s, s′), we express this as NO-CONF_T(s) == \Delta(s, ParentState(transaction)) \cap WT(transaction) = {}

\* t1 comes before t2 in wall clock/oracle time
t1 < t2 == t1.commit < t2.start

\* Given system state and single transaction (seq of operations), determines new state
NextState(state, transaction) ==
  IF transaction.ops = {}
  THEN state
  ELSE IF FIRST(transaction.ops).op = "Read"
  THEN state
  ELSE [k \in state /\ (k,v) \notin transaction.ops => v, k \in transaction.ops => v]

\* Lists all possible permutations of executions given set of transactions
Executions(initialState, transactions) ==
  IF transactions = {}
  THEN {ExecutionElem(initialState, {}, initialState)}
  ELSE UNION {ExecutionElem(initialState, transaction, NextState(initialState, transaction)) : transaction \in transactions}

\* Helper: checks if specific execution satisfies given commit test
CT_SER(transaction, execution) ==
  LET
    parentState == execution.parentState
    resultState == execution.resultState
  IN parentState.commit < transaction.start /\ transaction.commit < resultState.start

\* Definition 5 Given a set of transactions T and their read states, a storage system satisfies an isolation level I iff ∃e:∀t ∈ T :CTI(t,e)
satisfyIsolationLevel(transactions, CT_SER)

\* Check types in derived specification
/\ InitValue \in Values
/\ PrintT(State)

====