---- MODULE ClientCentric ----
------------------------------ MODEL STATE ----------------------------
CONSTANTS Keys = <<k1, k2>> : SET OF STRING; (* set of all keys *)
Values == {v1, v2} : SET OF INTEGER; (* values associated with each key*)
InitValue == 0: INTEGER; (* initial value for a new state*);
State = [k \in Keys |-> InitValue] * makes it level-1 therefore pass it in ;(* current system state *)
ExecutionElem == {parentState, transaction} : SET OF State × Transaction; (* an execution element is the parent state and corresponding transactions*)
Executions(initialState) = <<>>: Seq(Seq(Transaction)); (* empty sequence of sequences for initial state*);
SerializabilityDebug(state, transactions): BOOLEAN ;(* checks if a given set of transaction satisfies serializable isolation level *)
SnapshotIsolation == TRUE; (* snapshot isolation is enabled*)
ReadCommitted = FALSE:BOOLEAN; (* read committed mode disabled by default*);
PrintT : (State → STRING) -> BOOL ;(* print function for debugging purposes *).
============================= SPECIFICATIONS =============================
\*\/\/ Serializability commit test \\\\/ /\* checks if a given transaction satisfies serializable isolation level *)
CT_SER(transaction, execution):BOOLEAN; (* check that all operations in the transactions are executed before their corresponding operation*)
(* Definition 5 Given a set of transactions T and their read states,
a storagesystem satisfies an isolation level I iff \E e:∀t ∈ T :CTI(t,e). *)
\*\/\/ Read committed commit test \\\\/ /\* checks that all operations in the transaction are executed before its corresponding operation*)
CT_RCER(transaction):BOOLEAN; (* check read consistency for a given set of transactions and their executions *);
(* Definition 6 Given a set of transactions T, an isolation level I satisfies Read Committed Isolation iff \A t:T | CT_RCER(t). *)
\*\/\/ Snapshot commit test \\\\/ /\* checks that all operations in the transaction are executed before its corresponding operation*)
CT_SSER(transaction):BOOLEAN; (* check snapshot isolation for a given set of transactions and their executions *);
(* Definition 7 Given a set of transactions T, an isolation level I satisfies Snapshot Isolation iff \A t:T | CT_SER(t). *)
\*\/\/ Read uncommitted commit test \\\\/ /\* checks that all operations in the transaction are executed before its corresponding operation*)
CTI(transaction):BOOLEAN; (* check read consistency for a given set of transactions and their executions *);
(* Definition 8 Given a set of transactions T, an isolation level I satisfies Read Uncommitted Isolation iff \A t:T | CTI(t). *)
============================= INVARIANTS =============================
\*\/\/ Invariant for Executions invariant * ensures that all executions are valid and satisfy the given commit test*)
ExecutionsValid[e ∈ EXECUTIONS] : CT_SER(transaction, e) ; (* check if an element in sequence is a transaction *)
(* Definition 1: s -T-> s' ≡ [(k,v) \in s ∧ (k,v) \notin s'] => k ∈ W_T /\ w(k,v) ∈ Σ_T => (k,v) \in s. *);
(* Definition 2: For simplicity of exposition we assume that a transaction only writes a key once.*);
\*\/\/ Invariant for Read States invariant * ensures all read states are valid and satisfy the given commit test*)
ReadStatesValid[s_p, t] : CTI(t) ; (* check if an element in sequence is a state *)
(* Definition 3: s -*-> s' => (k \in Keys | k \notin WT). *);
\*\/\/ Invariant for Write Set invariant * ensures all write sets are valid and satisfy the given commit test*)
WriteSetValid[s_p, t] : CTI(t) ; (* check if an element in sequence is a state *)
(* Definition 4: s -*-> s' => (k \in Keys | k \notin WT). *);
\*\/\/ Invariant for Read Consistency invariant * ensures all read consistencies are valid and satisfy the given commit test*)
ReadConsistent[s_p, t] : CTI(t) ; (* check if an element in sequence is a state *)
(* Definition 5: s -*-> s' => (k \in Keys | k \notin WT). *);
\*\/\/ Invariant for Write Consistency invariant * ensures all write consistencies are valid and satisfy the given commit test*)
WriteConsistent[s_p, t] : CTI(t) ; (* check if an element in sequence is a state *)
(* Definition 6: s -*-> s' => (k \in Keys | k \notin WT). *);
\*\/\/ Invariant for Snapshot Isolation invariant * ensures all snapshot isolations are valid and satisfy the given commit test*)
SnapshotIsolationValid[s_p, t] : CTI(t) ; (* check if an element in sequence is a state *)
(* Definition 7: s -*-> s' => (k \in Keys | k \notin WT). *);
\*\/\/ Invariant for Read Committed invariant * ensures all read committed isolations are valid and satisfy the given commit test*)
ReadCommitedValid[s_p, t] : CTI(t) ; (* check if an element in sequence is a state *)
(* Definition 8: s -*-> s' => (k \in Keys | k \notin WT). *);
\*\/\/ Invariant for Read Uncommitted invariant * ensures all read uncommited isolations are valid and satisfy the given commit test*)
ReadUnCommitedValid[s_p, t] : CTI(t) ; (* check if an element in sequence is a state *)
============================= SPECIFICATIONS =============================
\*\/\/ Serializability Debug \\\\/ /\* checks that all executions are valid and satisfy the given commit test*)
SerializableDebug[initialState, transactions] : ∃e:∀t∈transactions:(CT_SER(transaction, e)) => PrintT("Execution not serializable",execution); (* fall back to normal check *) \/ (~E execution in Executions(initialState):A transaction in transactions: CT_SER(transaction, execution));
\*\/\* Read Committed Debug *\/ /\* checks that all operations are executed before their corresponding operation*)
ReadCommitedDebug[state] : ∀t∈transactions:(CTI(t)) => PrintT("Operation not read committed",execution); (* fall back to normal check *) \/ (~E execution in Executions(initialState):A transaction in transactions: CT_RCER(transaction));
\*\/\* Snapshot Debug *\/ /\* checks that all operations are executed before their corresponding operation*)
SnapshotDebug[state] : ∀t∈transactions:(CTI(t)) => PrintT("Operation not snapshot",execution); (* fall back to normal check *) \/ (~E execution in Executions(initialState):A transaction in transactions: CT_SSER(transaction));
\*\/\* Read Uncommitted Debug *\/ /\* checks that all operations are executed before their corresponding operation*)
ReadUnCommitedDebug[state] : ∀t∈transactions:(CTI(t)) => PrintT("Operation not read uncommitted",execution); (* fall back to normal check *) \/ (~E execution in Executions(initialState):A transaction in transactions: CT_RCER(transaction));
============================= INVARIANTS =============================
\*\/\* Invariant for Read Consistency invariant * ensures all read consistencies are valid and satisfy the given commit test*)
ReadConsistent[s, t] : ∀k∈Keys:CT_RCER(t) => (~E e in Executions(initialState):A transaction in transactions:(w(e)) = v); (* check if an element in sequence is a state *)
\*\/\* Invariant for Write Set invariant * ensures all write sets are valid and satisfy the given commit test*)
WriteSetValid[s, t] : ∀k∈Keys:CT_RCER(t) => (~E e in Executions(initialState):A transaction in transactions:(w(e)) = v); (* check if an element in sequence is a state *)
\*\/\* Invariant for Snapshot Isolation invariant * ensures all snapshot isolations are valid and satisfy the given commit test*)
SnapshotIsolationValid[s, t] : ∀k∈Keys:CT_RCER(t) => (~E e in Executions(initialState):A transaction in transactions:(w(e)) = v); (* check if an element in sequence is a state *)
\*\/\* Invariant for Read Committed invariant * ensures all read committed isolations are valid and satisfy the given commit test*)
ReadCommitedValid[s, t] : ∀k∈Keys:CT_RCER(t) => (~E e in Executions(initialState):A transaction in transactions:(w(e)) = v); (* check if an element in sequence is a state *)
\*\/\* Invariant for Read Uncommitted invariant * ensures all read uncommited isolations are valid and satisfy the given commit test*)
ReadUnCommitedValid[s, t] : ∀k∈Keys:CT_RCER(t) => (~E e in Executions(initialState):A transaction in transactions:(w(e)) = v); (* check if an element in sequence is a state *)
====