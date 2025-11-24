---- MODULE ClientCentric ----
EXTENDS FiniteSets, Naturals, Sequences

(* Definitions *)
TYPE State == [Key : Value] (* A database `State` is represented by keys with corresponding values *)
TYPE Operation == {op: {"READ", "WRITE"}, key: Key, value: Value} (* An `Operation` is a read or write of a key and value *)
TYPE Transaction == {ops: Seq(Operation), start: TimeStamp, commit: TimeStamp} (* A `Transaction` is a total order of `Operation`s *)
TYPE ExecutionElem == {parentState: State, transaction: Transaction, resultState: State} (* An execution element includes the parent state and resulting state after executing a transaction *)

(* Helpers representing Reads and Writes *)
FUNCTION w(k : Key, v : Value) == <>(k -> v)([x : Key |-> x != k] U [Key -> Value]) (* Write operation (k,v) *)
FUNCTION r(k : Key, v : Value) == {(key, value) : State | key = k AND value = v} (* Read operation from state (k,v) *)

(* Transaction helpers *)
FUNCTION InitValue == <>[Key -> Value] (* Initial state of the database *)
FUNCTION Keys == DOMAIN(InitValue) (* All possible keys in the system *)
FUNCTION Values == RANGE(InitValue) (* All possible values in the system *)

(* Check types in derived specification *)
CONSTANTS InitValue /\ PrintT(State)

(* The set of all permutations of a sequence of transactions *)
FUNCTION Permutations(transactions : Seq(Transaction)) == {seq: Seq(Transaction) | ZLen(seq) = ZLen(transactions)} [i : ZIndices(transactions) -> seq[i]]

(* An execution is a sequence of transactions with their corresponding parent state. *)
FUNCTION Execution(initialState : State, transactions : Seq(Transaction)) == {elem: ExecutionElem | elem.parentState = initialState AND elem.transaction \in transactions} [nextState : State -> EXTEND elem.resultState WITH nextState]

(* Check if a transaction can be executed in a state *)
FUNCTION CanExecute(state : State, transaction : Transaction) == ALL {op : Operation | op \in transaction.ops AND r(op.key, op.value) SUBSET state}

(* Check if an execution satisfies the serializability commit test *)
FUNCTION CT_SER(transaction : Transaction, execution : Execution) == 
    EXISTS {otherTransaction : Transaction | otherTransaction \in execution AND transaction != otherTransaction 
            AND transaction.start < otherTransaction.commit}
====