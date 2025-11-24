---- MODULE ClientCentric ----
EXTENDS FiniteSets, Naturals, Sequences ----------------- Extend basic TLA+ modules.
---------------------------------- Module for database isolation related operations and checks.
INSTANCE ReadsWrites : {<>} -> Values x ({Key}, Value) -> BOOLEAN
READ "\* Helper representing Reads and Writes" \* READ,WRITE Operation helper definition.
BEGIN --------------------------------------- Begin of module definitions.
CONSTANT InitValue == _|_ /\ "TODO: Define Initialization value for database state.";
VARIABLE State == [Key] -> Value /\ "\* A `State` is represented by keys with corresponding values";
OPERATION Read(k) ==  -- Definition of READ operation.
    k \in Domain[State] >< (~ReadsWrites[\emptyset, <k-VALUES State[k], VALUE>]) /\ FALSE;
OPERATION Write(op: {Key}, val : Value) == -- Definition of WRITE operation.
    <<x>>SUBSET DOMAIN op -> ^State U {[(k \in op)-> <k,val>} <~ State ;
VARIABLE Transaction == [ops: Seq({<>}), start: TimeStamp, commit: TimeStamp] /\ "Transaction is a total order of `Operation`s";
OPERATION AddOp(op) ==  -- Definition to add operation in transaction.
    IFF (Cardinality[DOMAIN Transaction] = 0)\/(PREDECESSOR[LAST DOMAIN State, commit]) THEN [ops: AppendSeq([], op), start := LAST DOMAIN State + 1 ,commit: Cardinality(op) + start];
VARIABLE ExecutionElem == [parentState: State, transaction: Transaction] /\ "Execution element is a sequence of `Transaction`s with their corresponding parent state";  -- Definition for execution.
OPERATION NextState() ==  -> ^State;  -- Function to calculate next state given system state and single transaction (seq of operations).
FUNCTION Executions(init: State, transactions : Seq({<>})) == [e \in {<parentState = init ,transaction = t>} /\ Cardinality[DOMAIN e.Transaction] > 0 ]-> ^Transactions;  -- Lists all possible permutations of executions given set of transactions
OPERATION CT_SER(t: Transaction, execution : ExecutionElem) == (LAST DOMAIN State = t.start /\ Domain[State] \subseteq Range[(Execution[-1].transaction).ops])/\ ((Cardinality[(Transaction.\<->Op)]=0)\/(\EXISTS ops' IN Seq(((^Transactions - Transaction) .op)): Cardinality[Domain(o.KeyIntersect Domain(State))] > 0 ));  -- checks if specific execution satisfies given commit test
OPERATION CT_SSN() == \A transactions : ^Transaction /\ (CTI(\emptyset, ExecutionElem[-1])/\((^Transactions - Transaction) .op => Cardinality[Domain(o.KeyIntersect Domain(State))] > 0 ));  -- Strict Serializability: checks if all previous states for the operations in T are no later than sp
OPERATION CT_RCM() == \A transactions : ^Transaction /\ (CTI(\emptyset, ExecutionElem[-1])/\((^Transactions - Transaction) .op => Cardinality[Domain(o.KeyIntersect Domain(State))] > 0 ));  -- Read Committed
OPERATION CT_RUN() == \A transactions : ^Transaction /\ (CTI(\emptyset, ExecutionElem[-1])/\((^Transactions - Transaction) .op => Cardinality[Domain(o<｜begin▁of▁sentence｜>.KeyIntersect Domain(State))] > 0 ));  -- Read Uncommitted
END ---------------------------------------------------------------------------------------- End of module definitions.
====