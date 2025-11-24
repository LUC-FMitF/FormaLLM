---- MODULE ClientCentric ----
EXTENDS FiniteSets, Naturals, Sequences

(* Definitions *)
CONSTANTS InitValue = _|_ (* TODO: Specify an initial value for the database state *)

TYPE State == [k \in Keys |-> Values] (* A state is represented by keys with corresponding values *)
TYPE Operation == [op: {"Read", "Write"}, key: Keys, value: Values] (* An operation is a read or write of a key and value *)
TYPE Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp] 
(* A transaction is a total order of operations *)
TYPE ExecutionElem == [parentState: State, transaction: Transaction, resultState: State] (* Represents an execution as a sequence of transactions with their corresponding parent state. *)

(* Helpers representing Reads and Writes *)
FUNCTION Read(state: State, key: Key) == 
  IF EXISTS "k \in Keys |-> Values"[k](state) AND (key = k) 
  THEN [k][state] 
  ELSE InitValue 
  ENDIF 
ENDFUNCTION 

FUNCTION Write(state: State, key: Key, value: Value) == 
  IF EXISTS "k \in Keys |-> Values"[k](state) AND (key = k) 
  THEN [k][value] 
  ELSE state 
  ENDIF 
ENDFUNCTION 

(* Transaction helpers *)
FUNCTION GetStart(transaction: Transaction) == transaction.start 
FUNCTION GetCommit(transaction: Transaction) == transaction.commit 
FUNCTION GetOps(transaction: Transaction) == transaction.ops 

(* ExecutionElem helpers *)
FUNCTION GetParentState(elem: ExecutionElem) == elem.parentState 
FUNCTION GetTransaction(elem: ExecutionElem) == elem.transaction 
FUNCTION GetResultState(elem: ExecutionElem) == elem.resultState 

(* Apply a transaction to a state *)
OPERATION ApplyTransaction(state, txn) == 
  IF EXISTS ops \in Seq(Operation)(GetOps(txn)) /\ op \in Seq(Operation) |-> (op \in Op ~\/ Key(op) = Key(state) AND Value(op) = Value(state)) 
    (* Check if the transaction is valid *)
  THEN state 
  ELSE [k \in Keys |-> IF op.key = k THEN op.value ELSE Value(state[k]) ENDIF] 
  ENDIF 
ENDOFOPERATION 

(* Calculate next state given a transaction and the previous state *)
OPERATION NextState(prevState, txn) == 
  IF GetStart(txn) > TimeStamp AND prevState \in State THEN ApplyTransaction(prevState, txn) ELSE InitValue ENDIF 
ENDOFOPERATION 

(* Check if a state is complete for a transaction *)
FUNCTION IsComplete(state: State, txn: Transaction) == 
   EXISTS op \in Seq(Operation)(GetOps(txn)) /\ Read(state, Key(op)) = Value(op) 
ENDFUNCTION 

(* Check if a transaction can read from a state *)
FUNCTION CanRead(state: State, txn: Transaction) == 
   EXISTS op \in Seq(Operation)(GetOps(txn)) /\ Read(state, Key(op)) = Value(op) 
ENDFUNCTION 

(* Check if a transaction can write to a state *)
FUNCTION CanWrite(state: State, txn: Transaction) == 
   EXISTS op \in Seq(Operation)(GetOps(txn)) /\ Key(op) = Key(state) AND Value(op) = Value(state) 
ENDFUNCTION 

(* Check if a transaction commits *)
FUNCTION IsCommit(state: State, txn: Transaction) == 
   GetCommit(txn) > TimeStamp AND CanRead(state, txn) AND CanWrite(state, txn) 
ENDFUNCTION
====