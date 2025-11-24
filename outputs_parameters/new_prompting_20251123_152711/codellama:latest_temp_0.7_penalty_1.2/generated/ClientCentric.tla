---- MODULE ClientCentric ----

(* TODO InitValue could be bottom (_|_) *)
\* TLA+ specifications of Client Centric Isolation Specification by Crooks et al: https://dl.acm.org/doi/10.1145/3087801.3087802 *)
\* TLA+ specifications by Tim Soethout (tim.soethout@ing.com) et al: Automated Validation of State-Based Client-Centric Isolation with TLA+: https://doi.org/10.1007/978-3-030-67220-1_4 *)
------------------------------------ SETS ---------------------------------------
\* A database `State` is represented by keys with corresponding values *)
SET State == {k \in Keys |-> InitValue} (* makes it level-1 therefore pass it in *)
(* An `Operation` is a read or write of a key and value *)
SET Operation == [read: BOOLEAN, k: Key, v: Value]
\* A transaction is a total order of operations *)
SET Transaction == {ops: Seq(Operation), start: TimeStamp} (* for simplicity we store start and commit in a lookup function *)
(* ExecutionElem is the parent state of the next transaction *)
SET ExecutionElem == [parentState: State, transaction: Transaction]
\* A `Execution` as a sequence of transactions with their corresponding parent state. Note: This execution does therefore not contain the "final state" of the execution, since it is not a parent state of a transaction.*)
SET Execution == {ops \in Seq(Transaction)} (* We represent an execution as a sequence of transactions with their corresponding parent state*)
\* A `ReadStates` are from which states can the operation read its value *)
FUN ReadStates (transaction: Transaction): State <- [s |-> transaction.parentState] * \* restrict the valid read states for the operations in T to be no later than sp *\/
(* We define s as the parent state of T (denoted as `sp`,T ); to the *)
(* transaction that generated `s` as `Ts`; and to the set of keys in which*)
(* `s` and `s'` differ as `\Delta(s,s')` *)
FUN \Delta (state: State, nextState: State): Keys == {k |-> InitValue} <- [k |-> state] *\* By convention, write operations have read states too: for a write operation in T , they include all states in Se up to and including `T`'s parent state.*\/
(* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s`.*)
(* Note that this definition includes also the empty transaction, which has no *)
(* operations. We therefore add an additional constraint on the type of `W_T`, *)
(* i.e., we require it to be a subset of `Keys`. *)
FUN ReadStatesForEmptyTransaction (state: State): Keys <- [k |-> InitValue] *\* read states for empty transaction contains all previous states, to ensure that empty txns do not incorrectly invalidate the checked isolation level.*\/
(* The write set of `T` comprises the keys that `T` updates: W_T = {k|w(k, v) \in Σ_T}. *)
(* For simplicity of exposition, we assume that a transaction only writes a key once. *)
\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s`.*)
(* Note that this definition includes also the empty transaction, which has no *)
(* operations. We therefore add an additional constraint on the type of `W_T`, *)
(* i.e., we require it to be a subset of `Keys`. *)
FUN ReadStatesForEmptyTransaction (state: State): Keys <- [k |-> InitValue] *\* read states for empty transaction contains all previous states, to ensure that empty txns do not incorrectly invalidate the checked isolation level.*\/
(* Denoting the set of keys in which `s` and `s'` differ as `\Delta(s, s')` , we express this as NO-CONF_T (s) ≡ \Delta(s, sp) ∩ W_T = ∅ *)
\* A transaction comes before another if it has a smaller commit timestamp. We define the wall clock/oracle time for two transactions t1 and t2 as: *)
(* `t1` comes before `t2` in wall clock/oracle time*)
FUN Before (transaction1, transaction2): BOOLEAN <- \* given system state and single transaction (seq of operations), determines new state *\/\* lists all possible permutations of executions given set of transactions *)
(* All possible permutations *)
Permutation(transactions: SET Transaction) == {execution |-> [transaction \in transactions] |-> Seq([])} /\ [\A transaction \in transactions: execution.parentState = State(transaction)] *\/\* helper checks if specific execution satisfies given commit test *)
FUN CheckCommitTest (commitTest, executions: SET ExecutionElem): BOOLEAN <- [transaction |-> execution \in executions] |-> CT_SER(transaction, execution) \/ \A transaction \in transactions: CT_SER(transaction, execution) *\/\* fall back to normal check *)
FUN CheckCommitTest (commitTest, executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions] |-> CT_SER(transaction, execution) \/ \A transaction \in transactions: CT_SER(transaction, execution) *\/\* PrintT(<<"try execution:", execution>>) => *)
FUN CheckCommitTest (commitTest, executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions] |-> CT_SER(transaction, execution) \/ \A transaction \in transactions: CT_SER(transaction, execution) *\/\* print all executions that satisfy the commit test *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction \in transactions: CT_SER(transaction, execution)] *\/\* print all executions that satisfy the commit test *)
FUN CheckCommitTest (commitTest, executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions] |-> PrintExecutions(executions) *\/
(* Serializability Debugging*)
\* Given a set of transactions `T` and their read states, a storagesystem satisfies an isolation level `I` iff ∃e:∀t \in T :CTI(t,e). *)
FUN SatisfyIsolationLevel (transactions: SET Transaction, isolationLevel): BOOLEAN <- [transaction |-> executions \in Executions] |-> CheckCommitTest(isolationLevel, executions) *\/
(* Serializability commit test*)
\* Given a transaction `T` and its read states, `e`, it satisfies the serializable isolation level iff ∀t' \in T : (CTI(t', e) => CTI(t, e)) *)
FUN CT_SER (transaction: Transaction, executionElem): BOOLEAN <- [execution |-> transaction'] |-> Before(transaction, transaction') *\/\* If `e` has a commit test and the new state satisfies this test, then it is serializable. *)
FUN SatisfyIsolationLevel (transactions: SET Transaction, isolationLevel): BOOLEAN <- [execution |-> executionElem \in Executions] |-> CT_SER(transaction, executionElem) *\/
(* Serializability Debugging*)
\* Given a set of transactions `T` and their read states, a storagesystem satisfies an isolation level `I` iff ∃e:∀t \in T :CTI(t,e). *)
FUN SatisfyIsolationLevel (transactions: SET Transaction, isolationLevel): BOOLEAN <- [execution |-> executionElem \in Executions] |-> CheckCommitTest(isolationLevel, executions) *\/
(* Serializability commit test*)
\* Given a transaction `T` and its read states, `e`, it satisfies the serializable isolation level iff ∀t' \in T : (CTI(t', e) => CTI(t, e)) *)
FUN CT_SER (transaction: Transaction, executionElem): BOOLEAN <- [execution |-> transaction'] |-> Before(transaction, transaction') *\/\* If `e` has a commit test and the new state satisfies this test, then it is serializable. *)
FUN SatisfyIsolationLevel (transactions: SET Transaction, isolationLevel): BOOLEAN <- [execution |-> executionElem \in Executions] |-> CT_SER(transaction, executionElem) *\/
(* Read Committed*)
\* A transaction is read committed iff it reads its own writes. *)
FUN RC (transactions: SET Transaction): BOOLEAN <- [transaction |-> operation \in operations] |-> Before(operation, transaction) /\ [\A operation' \in transactions.: CT_SER(operation', executionElem)] *\/\* Read Uncommitted*)
FUN RU (transactions: SET Transaction): BOOLEAN <- [transaction |-> operation \in operations] |-> Before(operation, transaction) /\ [\A operation' \in transactions.: CT_SER(operation', executionElem)] *\/
(* Helper functions *)
\* Given a set of `T` and their read states, it returns all possible permutations. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- [transaction |-> transaction'] |-> {executionElem |-> execution \in Executions} /\ [\A execution' \in transactions.: CT_SER(transaction', execution')] *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* Given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it returns all possible executions of that transaction. *)
FUN Executions (transactions: SET Transaction): SET ExecutionElem <- {executionElem |-> [transaction' |-> operations' \in Operations] |-> Seq([])} /\ [\A operation' \in transactions.: CT_SER(operation', execution')]. *\/\* given a set of `T` and their read states, it returns all possible permutations. *)
FUN PrintExecutions (executions: SET ExecutionElem): BOOLEAN <- [execution |-> transaction \in transactions.] |-> PrintT(<<"try execution:", execution>>) /\ [\A transaction' \in transactions.: CT_SER(transaction', execution')] *\/
\* Given a state `s` and a new operation, it returns the updated state. *)
FUN State (state: State, newOperation): SET State <- [k |-> InitValue]. /\\[\A k \in Keys.] *\/\* given an initial state and a transaction, it
====