---- MODULE ClientCentric ----
EXTENDS FiniteSets, Naturals, Sequences, ZSequences

CONSTANTS
  InitValue == _|_ (* InitValue could be bottom *)
  Keys == {...} (* Database keys *)
  Values == {...} (* Database values *)

TypeOK == \/ (k,v) \in State ==> k \in Keys /\ v \in Values

(* An operation is a read or write of a key and value *)
Operation == [op: {"read", "write"}, key: Keys, value: Values]

(* A transaction is a total order of operations *)
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

(* An execution element represents a state, a transaction, and the resulting state *)
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

(* A state is complete for a transaction in an execution if every operation in the transaction can read from the state *)
StateOK == \A op: Transaction.ops[\A i: 0..<ZLen(ops)].op[1] = op[1] /\ (op[0] = "read" => op[1] \in parentState)

(* The parent state is the last state in the execution *)
ParentState == [e: Seq(ExecutionElem)].e[0].resultState

(* The write set of T comprises the keys that T updates *)
WriteSet == [t: Transaction].{k: t.ops[\A i: 0..<ZLen(t.ops)].op[1] = k /\ t.ops[\A i: 0..<ZLen(t.ops)].op[0] = "write"}

(* A transaction comes before another in wall clock/oracle time if its commit timestamp is less than the other's *)
CT_WALL == [t1: Transaction, t2: Transaction].t1.commit < t2.commit

(* Given a set of transactions and their read states, a storage system satisfies an isolation level if there exists an execution that satisfies the commit test *)
satisfyIsolationLevel == \A transactions: Seq(Transaction), CT_COMMIT: State \times Transaction -> BOOLEAN.
  (\E execution: Seq(ExecutionElem): 
    \A transaction: transactions[i]: (transaction \in execution.transaction /\ CT_COMMIT(execution.parentState, transaction)) =>
    CT_COMMIT(execution.resultState, transaction))

(* Commit tests *)
CT_SER == [transaction: Transaction, execution: Seq(ExecutionElem)].
  (\A i: 0..<ZLen(execution) - 1.execution[i].transaction \in transaction /\ execution[i + 1].transaction \notin WriteSet) =>
  (\A i: 0..<ZLen(execution) - 1.execution[i].transaction \notin transaction /\ execution[i + 1].transaction \in WriteSet)

(* Snapshot Isolation *)
CT_SSER == [state: State, transaction: Transaction].state \in ReadStates(transaction)

(* Read Committed *)
CT_RC == [state: State, transaction: Transaction].state \in ReadStates(transaction)

(* Read Uncommitted *)
CT_RU == [state: State, transaction: Transaction].TRUE

(* Check types in derived specification *)
CheckTypes == TypeOK /\ CT_WALL /\ satisfyIsolationLevel(transactions, CT_SSER) /\ satisfyIsolationLevel(transactions, CT_RC) /\ satisfyIsolationLevel(transactions, CT_RU)

(* Printing states *)
PrintState == [s: State].s /\ \A k: Keys.s[k] \in Values

SPECIFICATION Spec == CheckTypes /\ PrintState

INVARIANTS TypeOK /\ StateOK /\ CT_WALL /\ satisfyIsolationLevel /\ CheckTypes /\ PrintState /\ \A k: Keys.InitValue \in Values
=============================================================================
====