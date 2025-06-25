---- MODULE ClientCentricIsolation ----
(***************************************************************************)
(* TLA+ specifications of Client Centric Isolation Specification by Crooks et al: https://dl.acm.org/doi/10.1145/3087801.3087802 *)
(* TLA+ specifications by Tim Soethout (tim.soethout@ing.com) et al: Automated Validation of State-Based Client-Centric Isolation with TLA+: https://doi.org/10.1007/978-3-030-67220-1_4 *)
(***************************************************************************)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Keys, Values, InitValue, TimeStamps
ASSUME InitValue \in Values

VARIABLES State, Transactions

(***************************************************************************)
(* A database `State` is represented by keys with corresponding values *)
(***************************************************************************)
State == [Keys -> Values]

(***************************************************************************)
(* An `Operation` is a read or write of a key and value *)
(***************************************************************************)
Operation == [type: {"read", "write"}, key: Keys, value: Values]

(***************************************************************************)
(* A `Transaction` is a total order of `Operation`s *)
(***************************************************************************)
Transaction == [ops: Seq(Operation), start: TimeStamps, commit: TimeStamps]

(***************************************************************************)
(* We represent an `Execution` as a sequence of `Transaction`s with their corresponding parent state. *)
(***************************************************************************)
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]
Execution == Seq(ExecutionElem)

(***************************************************************************)
(* Given system state and single transaction (seq of operations), determines new state *)
(***************************************************************************)
ApplyTransaction(state, transaction) ==
  LET ops == transaction.ops
  IN [state EXCEPT ![op.key] = op.value
      | op \in Range(ops) /\ op.type = "write"]

(***************************************************************************)
(* Lists all possible permutations of executions given set of transactions *)
(***************************************************************************)
Executions(transactions) ==
  LET perms == Permutations(transactions)
  IN [Seq(ApplyTransaction(Accumulate(state, ts), ts)): ts \in perms]

(***************************************************************************)
(* Helper: checks if specific execution satisfies given commit test *)
(***************************************************************************)
SatisfiesCommitTest(execution, commitTest) ==
  \A transaction \in Range(execution): commitTest(transaction, execution)

(***************************************************************************)
(* Tests there exists an execution for `transactions`, that satisfies the isolation level given by `commitTest` *)
(***************************************************************************)
SatisfiesIsolationLevel(transactions, commitTest) ==
  \E execution \in Executions(transactions): SatisfiesCommitTest(execution, commitTest)

(***************************************************************************)
(* Serializability commit test *)
(***************************************************************************)
CT_SER(transaction, execution) ==
  \A other \in Range(execution):
    other /= transaction =>
      \/ other.commit < transaction.start
      \/ transaction.commit < other.start

(***************************************************************************)
(* Snapshot Isolation *)
(***************************************************************************)
CT_SI(transaction, execution) ==
  \A other \in Range(execution):
    other /= transaction =>
      \/ other.commit <= transaction.start
      \/ transaction.commit <= other.start
      \/ transaction.ops \cap other.ops = {}

(***************************************************************************)
(* Strict Serializability: ∀T ∈T:T <s T => s_T′ -*-> s_T. *)
(***************************************************************************)
CT_SSER(transaction, execution) ==
  \A other \in Range(execution):
    other /= transaction =>
      \/ other.commit < transaction.start
      \/ (transaction.commit < other.start /\ transaction.ops \cap other.ops = {})

(***************************************************************************)
(* Read Committed *)
(***************************************************************************)
CT_RC(transaction, execution) ==
  \A other \in Range(execution):
    other /= transaction =>
      \/ other.commit <= transaction.start
      \/ transaction.ops \cap other.ops = {}

(***************************************************************************)
(* Read Uncommitted *)
(***************************************************************************)
CT_RU(transaction, execution) ==
  \A other \in Range(execution):
    other /= transaction =>
      transaction.ops \cap other.ops = {}

(***************************************************************************)
(* Check types in derived specification *)
(***************************************************************************)
TypeOK ==
  /\ State \in [Keys -> Values]
  /\ Transactions \in Seq(Transaction)

(***************************************************************************)
(* Initialize state with Init and transition with Next *)
(***************************************************************************)
Init ==
  /\ State = [k \in Keys |-> InitValue]
  /\ Transactions = <<>>

Next ==
  \E t \in Transactions:
    /\ State' = ApplyTransaction(State, t)
    /\ UNCHANGED Transactions

(***************************************************************************)
(* The specification *)
(***************************************************************************)
Spec ==
  Init /\ [][Next]_<<State, Transactions>>

(***************************************************************************)
(* Theorems *)
(***************************************************************************)
THEOREM Spec => []TypeOK
=============================================================================