---- MODULE ClientCentric ----
EXTENDS FiniteSets, Naturals, Sequences

CONSTANTS Values = {...}  (* The set of all possible values *)
CONSTANTS Keys = {...}    (* The set of all keys in the database *)

\* A key-value pair is an Operation.
Operation == <k: Key, v: Value>

\* A Transaction is a total order of Operations.
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

(* The parent state of the next transaction *)
NextParentState == [k ∈ Keys |-> (GREATEST t ∈ TL[transaction].ops : Index(t.k) + 1)]

\* Definition 1: s -T-> s' means that for all keys k and values v in state s, if (k,v) is not in s', then k is a key written by transaction T and w(k,v) is a write operation.
w(k,v)-to->r(k,v)  (* By convention, write operations have read states too *)

\* Check if a specific execution satisfies the given commit test *)
CT_SER == [execution: Execution] -> EXISTS e ∈ execution : e.transaction.commit = transaction.start

(* Given system state and single transaction (seq of operations), determines new state *)
NextState(state, operation) == IF Index(operation.k) < Cardinality(Keys) THEN [k \in Keys |-> (IF k = operation.k THEN operation.v ELSE state[k])] FI

(* Lists all possible permutations of executions given set of transactions *)
executions(initialState, transactions) == {[e ∈ ExecutionElem : e.parentState = initialState /\ EXISTS t ∈ transactions : e.transaction = t]}

(* All possible permutations *)
Permutations == POWERSET(transactions)

\* Check types in derived specification *)
CheckTypes == \A transaction ∈ transactions: DOMAIN(transaction.ops) SUBSET Naturals /\ RANGE(transaction.ops) SUBSET Values

(* Read Committed *)
CT_RC == EXISTS execution ∈ executions : CT_SER(transactions, execution)

(* Read Uncommitted *)
CT_RU == \A transaction ∈ transactions: EXISTS state ∈ states : Index(transaction.ops[0].k) <= Index(state.k)

(* Snapshot Isolation *)
CT_SI == EXISTS e1,e2 ∈ executions : (Index(e1.transaction.ops[0].k) < Index(e2.transaction.ops[0].k)) => CT_SER(transactions, e1) /\ CT_SER(transactions, e2)

(* Strict Serializability *)
CT_SSER == EXISTS execution ∈ executions : \A transaction ∈ transactions: Index(transaction.ops[0].k) <= Index(execution.parentState.k) => CT_SER(transactions, execution)
====