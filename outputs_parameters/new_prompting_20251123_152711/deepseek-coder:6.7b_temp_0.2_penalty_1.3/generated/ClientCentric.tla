---- MODULE ClientCentric ----
EXTENDS FiniteSets, Naturals, Sequences

(**********************************************************************************************************)
(* TLA+ specifications of Client Centric Isolation Specification by Crooks et al: https://dl.acm.org/doi/10<｜begin▁of▁sentence｜>3087801.3087802 *)
(* TLA+ specifications by Tim Soethout (tim.soethout@ing.com) et al: Automated Validation of State-Based Client-Centric Isolation with TLA+: https://doi.org/10<｜begin▁of▁sentence｜>67220-1_4 *)
(***********************************************************************************************************)
CONSTANTS 
    Keys = {...} (* Set of all keys in the database *),
    Values = {...} (* Set of all possible values that a key can have *).
    
TypeOK InitValue \in Values,
      Operation == [key: Key, value: Value], 
      Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp] EXTENDS SEQ(Operation),
      ExecutionElem == [parentState: State, transaction: Transaction, resultState: State].
      
(* Definitions *)
\* A database `State` is represented by keys with corresponding values *)(*) 
State == {Key : Value} EXTENDS FUNSET(Keys, Values), (* Initial state of the system *)
    InitValue \== [k \in Keys |-> InitValue] EXTEND FUNSET(Keys, Values) TO State.
    
(* Helpers representing Reads and Writes *)(*) 
Read == {key : value} IN DOMAIN /\ VALUE = value, (* Reading a key returns the corresponding value *)
    Write[k](v) ==  [k \in Keys |-> v] EXTEND FUNSET(Keys, Values) TO State.(* Writing to a key updates its value *) 
    
(* A `Transaction` is a total order of `Operation`s *)(*)  
\* Operations are ordered by their timestamps in the transaction *)(*)
Order == [t : Transaction |-> SeqOrd(DOMAIN t, OPERATION.ord)]. (* Ordering function for transactions *) 
    
(* An execution e for a set of transactions T is represented as sequence of `Transaction`s with their corresponding parent state *)(*)  
Executions == [ops : Transaction |-> ExecutionElem], (* Sequence of executions *)
    ParentState[e](t) ==  EXECUTIONS.prev(e).resultState,(* The parent state is the last state in the execution for a transaction t *) 
    
\* Definition: s -T-> s' means that all keys and values not present in s', but present in s (i.e., they were written by T), must have been updated at some point before or during T *)(*)  
Isolation == \A(t : Transaction) /\ DOMAIN t SUBSET KEYS => STATE = ParentState[EXECUTIONS.prev(Order[\E ops:Transaction |-> Order[ops] < Order[t]]).resultState](t), (* Isolation definition *)
    
(* Check if a specific execution satisfies the given commit test *)(*)  
CommitTest == BOOLEAN, 
    CT_SER(transaction : Transaction) ==  STATE = transaction.commit => EXECUTIONS[Order[\E ops:Transaction |-> Order[ops] < Order[transaction]]].resultState](transaction), (* Serializability commit test *)  
    
(* Check types in derived specification *)(*) 
CheckTypes == \A(t : Transaction) /\ DOMAIN t SUBSET KEYS => STATE = transaction.commit =>  TYPEOK EXECUTIONS[Order[\E ops:Transaction |-> Order[ops] < Order[transaction]]].resultState](transaction), (* Check types in derived specification *) 
    
(* Isolation Levels *)(*)  
IsolLevel == {ReadCommitted, ReadUncommitted}, (* Enum for isolation levels *)   
\* Strict Serializability: For any transaction T and its read states s_T , no other transactions can commit after T until all preceding transactions have committed.  *)(*)    
SSER[transactions : Transaction] == \A(t1, t2 : transactions) /\ Order[t1] < Order[t2] => ParentState[EXECUTIONS[\E ops:Transaction |-> Order[ops] <= Order[t1]]].resultState](t2), (* Strict Serializability *)
    ReadCommitted == \A(transaction : transactions) /\ DOMAIN transaction SUBSET KEYS =>  STATE = ParentState[EXECUTIONS[\E ops:Transaction |-> Order[ops] <= Order[transaction]]].resultState](transaction), (* Read Committed isolation level *)
    ReadUncommitted == \A(t : transactions) /\ DOMAIN t SUBSET KEYS => STATE = EXECUTIONS.prev(\E ops:Transaction |-> Order[ops] < Order[t]).resultState](t), (* Read Uncommitted isolation level *)
    
(* Check if a set of transactions satisfy an isolation level *)(*)  
satisfyIsolationLevel == \A(transactions : Transaction, commitTest : CommitTest) /\ EXIST t1:Transaction /\ Order[t1] = MINIMUM{Order[\E ops:Transaction |-> Order[ops]]}(DOMAIN transactions SUBSET DOMAIN ORDER} => (commitTest)(t1), (* Check if a set of transactions satisfy an isolation level *)
    
(* Helper function to print execution *)(*)  
PrintT == PROCEDURE(STRING) : STRING -> BOOLEAN, 
    PrintT[s](execution) ==  EXIST t:Transaction /\ Order[\E ops:Transaction |-> Order[ops] < Order[t]] = MINIMUM{Order}[\E ops:Transaction |-> Order[ops]]}(DOMAIN transactions SUBSET DOMAIN ORDER => s \in {<<"try execution:">>,execution}), (* Print the execution *)
    
(* SerializabilityDebug checks if no executions satisfy commit test or all of them do *)(*)  
SerializabilityDebug == PROCEDURE(BOOLEAN) : State x Transaction -> BOOLEAN, 
    SerializabilityDebug[initialState](transactions) ==  (~\E execution:Executions /\ CT_SER(execution)) => (\A transaction:(DOMAIN transactions SUBSET DOMAIN ORDER) =>  PrintT("Execution not Serializable",transaction)), (* If no executions satisfy commit test, print all of them *)
    \/ EXIST t1 : Transaction /\ Order[t1] = MINIMUM{Order[\E ops:Transaction |-> Order[ops]]}(DOMAIN transactions SUBSET DOMAIN ORDER) => CT_SER(initialState)(transactions), (* If all of them do, check if any execution satisfies commit test *)
    
(* Check types in derived specification *)(*)  
CheckTypes == \A t : Transaction /\ DOMAIN t SUBSET KEYS =>  STATE = EXECUTIONS[\E ops:Transaction |-> Order[ops] < Order[t]].resultState](t), (* Check if the state of a transaction is valid *) 
    
(* All possible permutations *)(*)  
Permutation == {...}, (* Set of all possible permutations for executions given set of transactions *)   
\* Lists all possible permutations of executions given set of transactions. For now, inline `satisfyIsolationLevel` instead of `satisfyIsolationLevel(transactions, CT_SSER(timestamps)) because partial functions are not supported/hard *)(*)  
    
(* Recover ExecutionElems from accumulator *) 
Recovery == PROCEDURE() : BOOLEAN -> EXECUTIONS.TYPEOK, (* Helper to recover the execution elements from an accumulated state *)   
\* Given system state and single transaction (seq of operations), determines new state *)(*)  
NextState[state: State](transaction) == [k \in Keys |->  IFEXISTS ops : Operation /\ DOMAIN(ops) = Order[\E t':Transaction |-> Order[t'] < Order[transaction]] => VALUE ELSE InitValue] EXTEND FUNSET(Keys, Values) TO State], (* Given system state and single transaction (seq of operations), determines new state *)  
    
(* Check if a specific execution satisfies given commit test *)(*) 
CommitTest == PROCEDURE() : BOOLEAN -> EXECUTIONS.TYPEOK, (* Helper to check the conditions for serializability and strictness *)   
\* Definition: Given set of transactions T and their read states s_T , a storagesystem satisfies an isolation level I iff ∃e : ∀t ∈ T : CTI(t, e) *)(*)  
satisfyIsolationLevel == PROCEDURE() : BOOLEAN -> EXECUTIONS.TYPEOK (* Check the conditions for serializability and strictness *)   
    
(* PrintT checks if a specific execution satisfies given commit test *) 
PrintT[s](execution) ==  EXIST t:Transaction /\ Order[\E ops:Transaction |-> Order[ops] < Order[t]] = MINIMUM{Order}[\E ops:Transaction |-> Order[ops]]}(DOMAIN transactions SUBSET DOMAIN ORDER => s \in {<<"try execution:">>,execution}), (* Print the execution *)  
    
(* Check if a set of transactions satisfy an isolation level *)(*) 
satisfyIsolationLevel == PROCEDURE() : BOOLEAN -> EXECUTIONS.TYPEOK (* Check if all executions for given transaction are valid under specified commit test *)   
END Database
====