---- MODULE ClientCentric -----------------------------------------------
EXTENDS FiniteSets, Naturals, Sequences
=============================================================================
CONSTANTS InitValue = _|_ (* TODO: Define initial value *)
             Keys \subseteq Nat (* Set of keys in the database. Assumed to be finite and non-empty for simplicity's sake*)
LOCAL INSTANCE Operations == [key : Key, opType : {"Read", "Write"}, value : Values] 
(* An operation is a read or write on a key with an optional value *)
LOCAL INSTANCE Transaction = [ops: Seq(Operations), start: TimeStamp, commit: TimeStamp] (* A transaction is total order of operations*)
LOCAL FUNCTION ReadsAndWrites == \X{op : Operations | op.key NOTIN DOMAIN X => (op.value=InitValue)} 
(* Helper representing reads and writes *)
LOCAL INSTANCE ExecutionElem = [parentState: State, transaction: Transaction, resultState: State] (* An execution element is a state transition with the corresponding parent state*)
LOCAL FUNCTION Parent == \X{e : Execution | e.transaction=Y} => X 
(* The parent of an execution *)
LOCAL INSTANCE States = [key : Key, value : Values] (* A State represents database states by keys with values *)
LOCAL OPERATOR "==>" == \X{s1:States[Key], s2:States[Key]} => ([(k,v) & ((k,v) NOTIN X AND w(k, v) IN WriteSet)] IMPLIES (k,v) IN Y )
(* The transition operator *)
LOCAL FUNCTION CT_SER == \E{e : Execution | e.transaction=X} => Parent[e] = PreState 
(* Serializability commit test*)
=============================================================================
OPERATIONS (* Operations on states and transactions *)
\* ... (operations to define how operations affect a state, etc.) *\\
...
====