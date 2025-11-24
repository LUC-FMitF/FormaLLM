---- MODULE ClientCentric ----
EXTENDS FiniteSets, Naturals, Sequences

CONSTANTS 
    InitValue == _|_ (* InitValue could be bottom (_|_) *)
    Keys == {...} (* A database `State` is represented by keys with corresponding values *)

TypeOK Read == [key: Key, value: Value] (* An `Operation` is a read or write of a key and value *)
TypeOK Write == [key: Key, value: Value]
TypeOK Transaction == [ops: Seq(Read \/ Write), start: TimeStamp, commit: TimeStamp] (* A `Transaction` is a total order of `Operation`s *)
TypeOK ExecutionElem == [parentState: State, transaction: Transaction, resultState: State] (* Helpers representing Reads and Writes *)

(* Defining a function to get the keys in which state s and s' differ *)
FUNCTION Delta(s, s') == DOMAIN(s) \ DOMAIN(s') U (DOMAIN(s) \ DOMAIN(s'))

(* Defining a function to get the write set of transaction T *)
FUNCTION WriteSet(T) == {key: Key |-> value: Value \in T.ops}

(* Defining a function to get all possible permutations of executions given set of transactions *)
FUNCTION Permutations(transactions) ==
  IF Cardinality(transactions) = 0
  THEN {}
  ELSE UNION {transaction |-> Permutations(transactions - transaction)}

(* Defining a function to get all possible permutations of executions given set of transactions *)
FUNCTION Executions(initialState, transactions) ==
  UNION {
    [parentState:= initialState, transaction:= transaction, resultState:= ResultState(initialState, transaction)]
    |-> Executions(ResultState(initialState, transaction), transactions - transaction)
  }

(* Defining a function to check if specific execution satisfies given commit test *)
FUNCTION CT_SER(transaction, execution) == Delta(execution.parentState, execution.resultState) \subseteq Delta(transaction.start, transaction.commit)

(* Defining a function to check if a set of transactions T and their read states satisfy a given isolation level *)
FUNCTION satisfyIsolationLevel(transactions, CT) == EXISTS e: Executions(InitialState, transactions) : \A transaction: transactions : CT(transaction, e)

(* Defining a function to calculate new state given system state and single transaction *)
FUNCTION ResultState(s, transaction) ==
  IF transaction.ops = EmptySequence
  THEN s
  ELSE ResultState(Apply(s, transaction.ops[0]), transaction.ops[1:])

(* Defining a function to apply operation to state *)
FUNCTION Apply(s, op) ==
  IF op \in Read
  THEN s
  ELSE s \ op

(* Serializability commit test *)
FUNCTION CT_SSER(timestamps) == EXISTS t1, t2: timestamps : t1.commit <= t2.start

SPECIFICATION Isolation ==
  (* Check types in derived specification *)
  EVENTUALLY (\A transaction: Transaction : EXISTS key: Key : transaction.ops \in Read ==> key \in Keys)
  /\ EVENTUALLY (\A transaction: Transaction : EXISTS key: Key : transaction.ops \in Write ==> key \in Keys)
  /\ EVENTUALLY (\A transaction: Transaction : EXISTS value: Value : transaction.ops \in Write ==> value \in Values)
  /\ InitValue \in Values
  /\ PrintT(State)
  (* Snapshot Isolation *)
  /\ satisfyIsolationLevel(transactions, \A transaction, execution: Executions(InitialState, transactions) : \A T: transactions : T.transaction <= execution.transaction)
  (* Strict Serializability *)
  /\ satisfyIsolationLevel(transactions, CT_SSER(timestamps))
  (* Read Committed *)
  /\ satisfyIsolationLevel(transactions, \A transaction, execution: Executions(InitialState, transactions) : \A T: transactions : T.transaction < execution.transaction)
  (* Read Uncommitted *)
  /\ satisfyIsolationLevel(transactions, \A transaction, execution: Executions(InitialState, transactions) : \A T: transactions : T.transaction <= execution.transaction)

INVARIANTS
  (* Initial state is a level 1 state *)
  INIT == InitialState.level = 1
  (* Every operation in a transaction can read from the state *)
  EVENTUALLY (\A transaction: Transaction : \A op: transaction.ops : op \in transaction.resultState)
  (* A state is complete for a transaction if every operation in the transaction can read from the state *)
  EVENTUALLY (\A transaction: Transaction : \A op: transaction.ops : op \in transaction.resultState)
  (* No transaction can read from future states *)
  EVENTUALLY (\A transaction: Transaction : \A futureState: Executions(InitialState, transactions) : \A op: transaction.ops : op \notin futureState.resultState)
  (* No transaction can write to future states *)
  EVENTUALLY (\A transaction: Transaction : \A futureState: Executions(InitialState, transactions) : \A op: transaction<｜begin▁of▁sentence｜> : op \notin futureState.resultState)
  (* No transaction can read from previous states *)
  EVENTUALLY (\A transaction: Transaction : \A previousState: Executions(InitialState, transactions) : \A op: transaction.ops : op \notin previousState.resultState)
  (* No transaction can write to previous states *)
  EVENTUALLY (\A transaction: Transaction : \A previousState: Executions(InitialState, transactions) : \A op: transaction<｜begin▁of▁sentence｜> : op \notin previousState.resultState)
  (* No transaction can read from initial state *)
  EVENTUALLY (\A transaction: Transaction : \A op: transaction.ops : op \notin InitialState)
  (* No transaction can write to initial state *)
  EVENTUALLY (\A transaction: Transaction : \A op: transaction<｜begin▁of▁sentence｜> : op \notin InitialState)

---- END OF MODULE Isolation ----
====