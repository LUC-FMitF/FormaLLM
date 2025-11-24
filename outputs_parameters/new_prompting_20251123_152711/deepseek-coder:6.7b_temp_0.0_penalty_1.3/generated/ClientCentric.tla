---- MODULE ClientCentric -----------------------------------------------
EXTENDS FiniteSets, Naturals, Sequences
---------------------------------------------------------------------- MODULE END

\* Definitions of types and operations on states.
TypeOK State == [k \in Keys |-> Value] /\ InitValue \in Values;
TypeOK Operation == {read: Key, write: (Key * Value)};
TypeOK Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp];
TypeOK ExecutionElem == [parentState: State, transaction: Transaction, resultState: State];
\* The set of all possible states.
CONSTANTS States = {s \in PowerSetUniv |-> s} /\ InitValue \in Values;

(* Helper functions for operations *)
FUNCTION ReadStates(op, state) == IF op=read THEN {state} ELSE {} END;
FUNCTION WriteStates(op, state) == ~ReadStates(op, state);
OPERATIONS OpToState = [r \in Operation |-> (s: State |-> 
  IF r.label = read THEN s[r.key]=r.value ELSE {k \in Domain(state) - {r.key} |-> state[k]} U {r.key -> r.value}}];
OPERATIONS NextState == [s: State, t: Transaction |-> 
  IF s IN WriteStates(t.ops[0], States) THEN {} ELSE OpToState[t.ops[1]](s)] ];
\* Helper function to check if a state is complete for a transaction *)
FUNCTION IsCompleteForTransaction == [state: State, txn: Transaction |-> 
  EXISTS i \in Indices(txn.ops) /\ OpToState[txn.ops[i]](state) = {} ];
OPERATIONS ExecutionElems == 
  IF transactions={} THEN {<parentState=InitValue, transaction=<>, resultState=InitValue>} ELSE 
    [e: Seq(ExecutionElem), txn \in Domain(transactions) |-> 
      <| parentState = e[LAST].resultState IF LastIndex(e)!={} ELSE InitValue FI, transaction = transactions[txn], resultState = 
      NextState[IF LASTINDEX(e)!=0 THEN e[LastIndex(e)-1].parentState ELSE InitValue FI, txn]>]; 
\* Commit test for serializability *)
FUNCTION CT_SER == [transaction: Transaction, executionElem : ExecutionElems |-> 
  ~EXISTS i \in Indices(execution) /\ IsCompleteForTransaction[execution[i].parentState, transaction]]; 
(* Check types in derived specification. Note that this is a partial function because TLA+ does not support the concept of total functions *)
FUNCTION SatisfyIsolationLevel == [transactions: Seq(Transaction), commitTest : Transaction -> BOOLEAN |-> 
  ~EXISTS execution \in Executions[initialState, transactions] /\ ~commitTest(execution)]; 
(* Isolation levels. Note that these are partial functions because TLA+ does not support the concept of total functions *)
FUNCTION CT_SSER == [timestamps: Seq((Transaction * TimeStamp)) |-> 
  ~EXISTS i, j \in Indices(transactions) /\ transactions[i].start < timestamps[j]]; 
(* Check if the system state and a single transaction determine new states *)
FUNCTION Executions == [initialState: State, transactions : Seq(Transaction)] == 
  {e |-> e \in PowersetUniv /\ LastIndex(e) IN Indices(transactions)};  
(* Check if the system state and a single transaction determine new states *)
FUNCTION NextStates == [state: State, txn : Transaction] == 
  {s |-> s \in PowersetUniv /\ IsCompleteForTransaction[s,txn]} ;
====