---- MODULE ClientCentric ----

(***************************************************************************)
(* Tim Soethout (tim.soethout@ing.com) et al, Automated Validation of State-Based *)
(* Client-Centric Isolation with TLA+: https://doi.org/10.1007/978-3-030-67220-1_4 *)
(***************************************************************************)

CONSTANT Keys
CONSTANT Values
CONSTANT InitValue  (* replace with bottom ( _) in final version *)

VARIABLE State == [k \in Keys |-> v: Values]
VARIABLE ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A database `State` is represented by keys with corresponding values
State == [k \in Keys |-> v: Values]

\* An `Operation` is a read or write of a key and value
Operation == Read(k) \/ Write(k,v)

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* For simplicity we store start and commit in a lookup function
startLookup[transaction] == transaction.start
commitLookup[transaction] == transaction.commit

\* Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* We represent an `Execution` as a sequence of `Transaction`s with their corresponding parent state.
Execution == {executionElem: ExecutionElem | (parentState, transaction) \in executionElem}

\* Note: This execution does therefore not contain the "final state" of the execution, since it is not a parent state of a transaction.
Execution == {executionElem: ExecutionElem | (parentState, transaction) \in executionElem}

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s`
complete(e, T) == {s \in States | \A t \in T : \A op \in s.ops : op = Read(k)}

\* readStatesForEmptyTransaction contains all previous states, to ensure that empty txns do not incorrectly invalidate the checked isolation level
readStatesForEmptyTransaction == {s \in States | (s,T) \notin complete(e, T)}

\* The write set of T comprises the keys that T updates: WT = {k|w(k, v) ∈ ΣT }.
WriteSet(T) == {k \in Keys | \EX t \in T : w(k,v) \in T.ops}

\* By convention, write operations have read states too: for a write operation in T , they include all states in Se up to and including T ’s parent state.
WriteSet(T) == {k \in Keys | \EX t \in T : w(k,v) \in T.ops}

\* Denoting the set of keys in which s and s′ differ as ∆(s, s′), we express this as NO-CONF_T (s) ≡ ∆(s, sp) ∩ WT = ∅
NOConflict(s, T) == WriteSet(T) \cap (s -*-> sp) = {}

\* Definition 1: s -T-> s' ≡ [(k,v) ∈ s ∧ (k,v) \notin s'] => k ∈ W_T /\ w(k,v) ∈ Σ_T => (k,v) ∈ s.
ReadStatesForEmptyTransaction == {s \in States | NOConflict(s, T)}

\* Definition 5 Given a set of transactions T and their read states,
A storagesystem satisfies an isolation level I iff ∃e:∀t ∈ T :CTI(t,e).
SatisfyIsolationLevel == \E e \in Executions: {transaction: Transaction | CT_SER(transaction, e)}

\* Helper: checks if specific execution satisfies given commit test
CommitTestHelper == {execution: Execution | commitLookup[transaction] \in T.commit}

\* Fall back to normal check
FallBack == CT_SER(transaction, execution)

\* PrintT(<<"try execution:",execution>>) =>
PrintT(e) ==
/\ Print("try execution:")
/\ Print(e)
/\ Print(".")

\* Serializability commit test
SerializabilityDebug == \A e \in Executions: CommitTestHelper[e] => SatisfyIsolationLevel[e] /\ PrintT(<<"Execution not Serializable:",e>>)

\* Read Committed
ReadCommitted == {state: State | (\A t \in T : w(k,v) \in T.ops)}

\* Read Uncommitted
ReadUncommitted == {state: State | (state -T-> state') /\ \EX t \in T : t.commit = state'.start}

(* Check types in derived specification *)
/\ InitValue \in Values
\/ PrintT(State)
/\ (* Fall back to normal check *)
FallBack
\* End of module declaration *)
====