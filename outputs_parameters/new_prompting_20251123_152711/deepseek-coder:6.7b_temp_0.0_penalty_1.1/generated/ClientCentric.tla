---- MODULE ClientCentric ----
EXTENDS FiniteSets, Naturals, Sequences

CONSTANTS Keys = {...} (* The set of all keys *)

(* A database `State` is represented by keys with corresponding values *)
TypeOK State == [k \in Keys |-> Values]

(* An `Operation` is a read or write of a key and value *)
TypeOK Operation == [op: {"read", "write"}, k: Keys, v: Values]

(* Helpers representing Reads and Writes *)
Read(k) == [op: "read", k: k, v: State[k]]
Write(k, v) == [op: "write", k: k, v: v]

(* A `Transaction` is a total order of `Operation`s *)
TypeOK Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

(* Helper to get the state at a certain timestamp *)
GetStateAtTime(state, time) == 
  IFEXISTS t \in Domain(state.commit) /\ state.commit[t] = time THEN state.ops[state.commit[t]] ELSE state

(* ExecutionElem represents an execution of a transaction in a certain state *)
TypeOK ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

(* The set of all executions for a given set of transactions *)
Executions(initialState, transactions) == 
  IF Cardinality(transactions) = 0 THEN {} ELSE 
    {[
      parentState: initialState, 
      transaction: Head(transactions), 
      resultState: GetStateAtTime(Head(transactions).ops, Head(transactions).commit)
    ] \in Executions(GetStateAtTime(initialState, Head(transactions).start), Tail(transactions))}

(* Check if a transaction can read from a state *)
CanReadFrom(state, k) == EXISTS i \in Domain(state) /\ state[i] = k

(* Check if a specific execution satisfies the serializability commit test *)
CT_SER(transaction, execution) == 
  LET eState == GetStateAtTime(execution.parentState, transaction.start) IN
    EXISTS i \in Domain(eState) /\ CanReadFrom(GetStateAtTime(execution.resultState, transaction.commit), i)

(* Check if a specific execution satisfies the strict serializability commit test *)
CT_SSER(transaction, execution) == CT_SER(transaction, execution)

(* The set of all executions for a given set of transactions that satisfy the serializability commit test *)
SerializableExecutions(initialState, transactions) == 
  {execution \in Executions(initialState, transactions) |-> CT_SER(transaction, execution)}

(* Check if there exists an execution for `transactions`, that satisfies the isolation level given by `commitTest` *)
SatisfyIsolationLevel(transactions, commitTest) == 
  EXISTS execution \in SerializableExecutions(initialState, transactions) :-> commitTest(transaction, execution)

(* Check types in derived specification *)
TypeOK State /\ TypeOK Operation /\ TypeOK Transaction /\ TypeOK ExecutionElem
/\ InitValue \in Values
/\ PrintT(State)
====