---- MODULE ClientCentric ----

(******************************************************************************)
(* TLA+ specifications by Tim Soethout (tim.soethout@ing.com) et al:           *)
(* Automated Validation of State-Based Client-Centric Isolation with TLA+:       *)
(* https://doi.org/10<｜begin▁of▁sentence｜>030672201_4                                              *)
(******************************************************************************)

EXTENDS FiniteSets, Naturals, Sequences

CONSTANTS InitValue = _|_ (* TODO InitValue could be bottom (_|_) *)

(* A database `State` is represented by keys with corresponding values *)
(* An `Operation` is a read or write of a key and value *)
(* Helpers representing Reads and Writes *)
(* A `Transaction` is a total order of `Operation`s *)
TYPE Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]
FOR ALL t IN Transaction : Cardinality(t.ops) > 0

(* We represent an `Execution` as a sequence of `Transaction`s with their corresponding parent state *)
TYPE ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

(* Definition 1: s -T-> s' => ((k,v) IN s AND (k,v) NOT IN s') => 
   k IN W_T /\ w(k,v) IN Σ_T => (k,v) IN s *)
(* We refer to s as the parent state of T (denoted as sp,T ); to the transaction that generated s as Ts; 
   and to the set of keys in which s and s′ differ as ∆(s,s′) *)
(* w(k,v)-to->r(k,v) *)
(* By convention, write operations have read states too: for a write operation in T , they include all states in Se up to and including T ’s parent state. *)
(* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` *)
(* readStatesForEmptyTransaction contains all previous states, to ensure that empty txns do not incorrectly invalidate the checked isolation level *)
(* The write set of T comprises the keys that T updates: WT = {k|w(k, v) IN ΣT }. For simplicity of exposition, we assume that a transaction only writes a key once. *)
(* Denoting the set of keys in which s and s′ differ as ∆(s, s′), we express this as NO-CONF_T (s) = DIFF(s, sp) INTERSECT WT = {} *)
(* t1 comes before t2 in wall clock/oracle time *)
(* Given system state and single transaction (seq of operations), determines new state *)
(* Lists all possible permutations of executions given set of transactions *)
(* All possible permutations *)
CONSTANTS initialState == [k \in Keys |-> InitValue] (* makes it level-1 therefore pass it in *)
VARIABLE executionElems == {<<>>}
VARIABLE nextState == {}
OPERATIONS
  storeExecutionElem(elem),
  calculateNextState(),
  recoverExecutionElems()
HELPERS
  checksIfSpecificExecutionSatisfiesGivenCommitTest(transaction, execution) : BOOLEAN
(* Definition 5 Given a set of transactions T and their read states, a storagesystem satisfies an isolation level I iff EXISTS e:FORALL t IN T :checksIfSpecificExecutionSatisfiesGivenCommitTest(t,e). *)
OPERATION PrintT(<<"try execution:",execution>>) IF ~checksIfSpecificExecutionSatisfiesGivenCommitTest(transaction, execution) THEN PRINT(<<"Execution not Serializable:",execution>>)
(* Snapshot Isolation *)
(* Strict Serializability: FORALL T IN Transactions : T <s T => s_T′ -*-> s_T. *)
(* For now inline satisfyIsolationLevel instead of satisfyIsolationLevel(transactions, checksIfSpecificExecutionSatisfiesGivenCommitTest) because partial functions are not supported/hard *)
(* Read Committed *)
(* Read Uncommitted *)
(* Check types in derived specification *)
/\ InitValue \in Values
/\ PrintT(State)
===============================================================================
====