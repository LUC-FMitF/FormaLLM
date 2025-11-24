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

\* Represent an `Execution` as a sequence of `Transaction`s with their corresponding parent state.
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* The parent state is the last state in the execution
DEFINITIONS
  ParentState(s, T) == LAST(s \in T |-> s)

\* Definition 1: s −T−> s' ≡ [(k,v) ∈ s ∧ (k,v) ∉ s'] => k ∈ W_T /\ w(k,v) ∈ Σ_T => (k,v) ∈ s.
\* The write set of T comprises the keys that T updates: WT = {k|w(k, v) ∈ ΣT }.
DEFINITIONS
  WT(T) == {k \in Keys |-> EXISTS op \in T.ops : op.op = "Write" /\ op.key = k}

\* Denoting the set of keys in which s and s′ differ as ∆(s, s′), we express this as NO-CONF_T(s) ≡ ∆(s, sp) ∩ WT = {}
DEFINITIONS
  NOCONFLICT(s, s', T) == (s \ s') INTERSECT WT(T) = {}

\* Given system state and single transaction (seq of operations), determines new state
DEFINITIONS
  NextState(s, T) == IF EXISTS op \in T.ops : op.op = "Write" /\ op.key = k THEN [k \in Keys - {k} |-> op.value] ELSE s

\* Lists all possible permutations of executions given set of transactions
DEFINITIONS
  Permutations(transactions) == {seq \in Seq(transactions) |-> seq}

\* All possible permutations
DEFINITIONS
  AllPermutations == UNION {Permutations(transactions) : transactions \in Powerset(Transaction)}

\* Helper: checks if specific execution satisfies given commit test
DEFINITIONS
  CheckCommitTest(execution, commitTest) == EXISTS transaction \in execution : commitTest(transaction)

\* Definition 5 Given a set of transactions T and their read states, a storagesystem satisfies an isolation level I iff ∃e:∀t ∈ T :CTI(t,e).
DEFINITIONS
  SatisfyIsolationLevel(transactions, commitTest) == EXISTS execution \in AllPermutations : CheckCommitTest(execution, commitTest)

\* Serializability commit test
DEFINITIONS
  SerializabilityDebug(initialState, transactions) ==
    IF ~\E execution \in AllPermutations : CheckCommitTest(execution, CT_SER)
    THEN ALL execution \in AllPermutations : CheckCommitTest(execution, CT_SER)

\* Snapshot Isolation
DEFINITIONS
  SnapshotIsolation(transactions, timestamps) == ALL transaction \in transactions : timestamps(transaction) <= timestamps(ParentState(transaction, transactions))

\* Strict Serializability: ∀T ∈T:T <s T ⇒ s_T′ −*−> s_T.
DEFINITIONS
  StrictSerializability(transactions, timestamps) == ALL transaction \in transactions : timestamps(transaction) < timestamps(ParentState(transaction, transactions)) ==> NOCONFLICT(ParentState(transaction, transactions), NextState(ParentState(transaction, transactions), transaction), transaction)

\* Read Committed
DEFINITIONS
  ReadCommitted(transactions, timestamps) == ALL transaction \in transactions : timestamps(transaction) <= timestamps(ParentState(transaction, transactions))

\* Check types in derived specification
DEFINITIONS
  CheckTypes == TYPEOK(InitValue \in Values) /\ TYPEOK(PrintT(State))

=============================================================================
====