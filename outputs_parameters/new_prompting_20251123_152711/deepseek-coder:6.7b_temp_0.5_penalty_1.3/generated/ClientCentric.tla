---- MODULE ClientCentric ----
EXTENDS FiniteSets / Naturals / Sequences  -- Import necessary modules for sets, natural numbers & sequences.
---------------------------------------- Module Definition Starts Here ------------------------------------------------------------------------------------------
CONSTANTS InitValue = _|_ ; (* Initial value of any key *)
VARIABLES Keys \subseteq Powerset(Nat) -> Nat;(* Set containing all possible keys in the database state*) 
          Values == {0,1} /\ ~InitValue;\* All values that can be stored. InitVal is not included to avoid confusion with uninitialized/unknown states *)
OPERATIONS Read = \state: State -> Key; (* Operation of reading a key from the state*) 
            Write = 2-ARY Operator(State,Key) /\ ~InitValue;\* Writing value for specific keys in database. InitVal is not included to avoid confusion with uninitialized/unknown states *)  
OPERATIONS Transaction = [ops: Seq (Read \state -> Value , Write state Key)] ; (* A transaction can be a sequence of Read and write operations*) 
            Execution == SEQ(Transaction, State);(* An execution is represented as an ordered set or list of transactions *)  
OPERATIONS Writes = {<k:Key;v :Value> \in Write} /\ ~InitValue;\* Set containing all written keys and values. InitVal not included*) 
            Reads = ~Writes ; (* All possible reads, ie., those that are no writes *)  
OPERATIONS CT_SER = (Transaction * Execution) -> BOOLEAN;(* Serializability commit test for a single transaction in an execution. Returns boolean value*) 
            SatisfyIsolationLevel = 2-ARY Operator(SET Transaction, OPERATOR COMPOSE EXP3(Execution)); (* Checks if all transactions satisfy isolation level *)  
OPERATIONS CT_SSN = (Transaction * Execution) -> BOOLEAN;(* Snapshot Isolation commit test*) 
            CT_RCMD = 2-ARY Operator(SET Transaction, OPERATOR COMPOSE EXP3(Execution)); (* Read Committed isolation level *)  
OPERATIONS CT_RCUD = (Transaction * Execution) -<｜begin▁of▁sentence｜> State;(*Read Uncommitted commit test*) 
            PrintT == \s: String -> BOOLEAN ; -- Function to print debugging information about the state of a system. It accepts string input and returns boolean value *)  
---------------------------------------- Module Definition End Here ------------------------------------------------------------------------------------------
====