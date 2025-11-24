---- MODULE ClientCentric ----
EXTENDS FiniteSets, Naturals, Sequences

(* Defines the state of the system, represented by keys with corresponding values *)
State == [Key => Value]

(* An operation is a read or write of a key and value *)
Operation == [Key => Value]

(* A transaction is a total order of operations *)
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

(* An execution element represents the state, transaction, and the resulting state *)
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

(* Defines the read states for a transaction *)
ReadStates == [Key => Value]

(* Defines the set of keys in which the state and the result state differ *)
Delta(s, s') == {k : Key | (k, v) \in s /\ (k, v) \notin s'}

(* Defines the write set of a transaction *)
WriteSet(s) == {k : Key | (k, v) \in s}

(* Defines the set of keys in which the state and the result state differ *)
Delta(s, s') == {k : Key | (k, v) \in s /\ (k, v) \notin s'}

(* Defines the commit test for serializability *)
CT_SER(transaction, execution) ==
  EXISTS execution : Execution :
    LET e == Recover(execution)
    LET t == transaction
    LET es == e.parentState
    LET et == e.transaction
    LET er == e.resultState
    LET ts == et.start
    LET tc == et.commit
    LET ds == Delta(es, er)
    LET wt == WriteSet(er)
    LET noConflict == ds \intersect wt = {}
    noConflict /\ (FORALL k : Key, v : Value, (k, v) \in ds : ts <= tc)

(* Defines the isolation level for a set of transactions *)
satisfyIsolationLevel(transactions, commitTest) ==
  EXISTS execution : Execution :
    ALL transaction : transactions :
      commitTest(transaction, execution)

(* Defines the serializability commit test *)
CT_SSER(timestamps) ==
  FORALL t1, t2 : Transaction, ts1, ts2 : TimeStamp :
    (t1, t2) \in timestamps ==> ts1 <= ts2

(* Defines the helper for checking serializability *)
SerializabilityDebug(initialState, transactions) ==
  (* if no executions satisfy commit test, print all executions *)
  (~EXISTS execution : Execution :
    ALL transaction : transactions :
      CT_SER(transaction, execution))
    ==>
  FORALL execution : Execution :
    PrintT(<<"Execution not Serializable:",execution>>)

(* Defines the helper for checking serializability *)
Serializability(initialState, transactions) ==
  (* if no executions satisfy commit test, print all executions *)
  (~EXISTS execution : Execution :
    ALL transaction : transactions :
      CT_SER(transaction, execution))
    ==>
  FORALL execution : Execution :
    PrintT(<<"Execution not Serializable:",execution>>)

(* The initial state of the system *)
CONSTANTS
  InitValue == TOP
  Keys == {k : Key}
  Values == {v : Value}

(* Defines the state of the system at the start *)
CONSTANTS
  initialState == [k \in Keys |-> InitValue]

(* Defines the helper for checking serializability *)
CheckTypes ==
  (* Check that the initial state is of type State *)
  TypeOK[initialState \in State]
  (* Check that the keys and values are of the correct types *)
  TypeOK[Keys \in FiniteSet]
  TypeOK[Values \in FiniteSet]
  (* Check that the initial value is of the correct type *)
  TypeOK[InitValue \in Values]

END MODULE ClientCentricIsolation
====

(* TLC Configuration *)
CONSTANTS
  TimeStamp == {t : Time | t >= 0}
  Execution == Seq(ExecutionElem)

SPECIFICATION
  (* The specification of the Client Centric Isolation Specification *)
  ClientCentricIsolation ==
    (* The system starts in the initial state *)
    InitState == <<>> /\
    (* Every transaction is a total order of operations *)
    FORALL t : Transaction : t.ops \in Seq(Operation)
    (* The system state changes based on the transactions *)
    NEXT (State -*-> NextState)

INVARIANTS
  (* The system state is a finite set of keys *)
  State -*-> State
  (* The system state is a finite set of keys *)
  NextState -*-> NextState
  (* The system state is a finite set of keys *)
  Execution -*-> Execution

(* Check types in derived specification *)
CheckTypes

(* Check serializability *)
Serializability(initialState, transactions)

(* Check snapshot isolation *)
satisfyIsolationLevel(transactions, CT_SSER(timestamps))

(* Check read committed *)
satisfyIsolationLevel(transactions, CT_READ_COMMITTED)

(* Check read uncommitted *)
satisfyIsolationLevel(transactions, CT<｜begin▁of▁sentence｜>READ_UNCOMMITTED)
====