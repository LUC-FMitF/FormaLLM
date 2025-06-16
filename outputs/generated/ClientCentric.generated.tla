--------------------------- MODULE ClientCentricIsolation ---------------------------
(**************************************************************************)
(* TLA+ specifications of Client Centric Isolation Specification by Crooks et al: *)
(* https://dl.acm.org/doi/10.1145/3087801.3087802                             *)
(* TLA+ specifications by Tim Soethout (tim.soethout@ing.com) et al:        *)
(* Automated Validation of State-Based Client-Centric Isolation with TLA+:  *)
(* https://doi.org/10.1007/978-3-030-67220-1_4                               *)
(**************************************************************************)

EXTENDS Sequences, FiniteSets, TLC

CONSTANTS Keys, Values, InitValue, TimeStamp, Operation
ASSUME InitValue \in Values

VARIABLES State, Transaction, ExecutionElem, Execution

(**************************************************************************)
(* A database `State` is represented by keys with corresponding values    *)
(**************************************************************************)
State == [Keys -> Values]

(**************************************************************************)
(* An `Operation` is a read or write of a key and value                    *)
(**************************************************************************)
Operation == [type: {"read", "write"}, key: Keys, value: Values]

(**************************************************************************)
(* A `Transaction` is a total order of `Operation`s                        *)
(**************************************************************************)
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

(**************************************************************************)
(* We represent an `Execution` as a sequence of `Transaction`s with their  *)
(* corresponding parent state.                                             *)
(**************************************************************************)
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]
Execution == Seq(ExecutionElem)

(**************************************************************************)
(* Given system state and single transaction (seq of operations),          *)
(* determines new state                                                    *)
(**************************************************************************)
ApplyTransaction(state, transaction) ==
  LET ops == transaction.ops
  IN [k \in Keys |-> IF \E op \in Range(ops) : op.type = "write" /\ op.key = k
                    THEN op.value
                    ELSE state[k]]

(**************************************************************************)
(* Lists all possible permutations of executions given set of transactions *)
(**************************************************************************)
Permutations(transactions) ==
  LET transactionSeq == Seq(transactions)
  IN Permutations(transactionSeq)

(**************************************************************************)
(* Helper: checks if specific execution satisfies given commit test        *)
(**************************************************************************)
SatisfiesCommitTest(execution, commitTest) ==
  \A transaction \in Range(execution) : commitTest(transaction, execution)

(**************************************************************************)
(* Tests there exists an execution for `transactions`, that satisfies the  *)
(* isolation level given by `commitTest`                                   *)
(**************************************************************************)
SatisfiesIsolationLevel(transactions, commitTest) ==
  \E execution \in Permutations(transactions) :
    SatisfiesCommitTest(execution, commitTest)

(**************************************************************************)
(* Serializability commit test                                             *)
(**************************************************************************)
CT_SER(transaction, execution) ==
  \A otherTransaction \in Range(execution) :
    \/ transaction.start < otherTransaction.start
    \/ /\ transaction.start = otherTransaction.start
       /\ transaction.commit <= otherTransaction.commit

(**************************************************************************)
(* Snapshot Isolation                                                      *)
(**************************************************************************)
CT_SI(transaction, execution) ==
  \A otherTransaction \in Range(execution) :
    \/ transaction.start < otherTransaction.start
    \/ /\ transaction.start = otherTransaction.start
       /\ transaction.commit <= otherTransaction.commit
    \/ /\ transaction.start > otherTransaction.start
       /\ transaction.commit > otherTransaction.commit

(**************************************************************************)
(* Strict Serializability: ∀T ∈T:T <s T => s_T′ -*-> s_T.                  *)
(**************************************************************************)
CT_SSER(transaction, execution) ==
  \A otherTransaction \in Range(execution) :
    transaction.start < otherTransaction.start => transaction.commit <= otherTransaction.start

(**************************************************************************)
(* Read Committed                                                          *)
(**************************************************************************)
CT_RC(transaction, execution) ==
  \A otherTransaction \in Range(execution) :
    transaction.start < otherTransaction.start => transaction.commit <= otherTransaction.start

(**************************************************************************)
(* Read Uncommitted                                                        *)
(**************************************************************************)
CT_RU(transaction, execution) ==
  \A otherTransaction \in Range(execution) :
    transaction.start < otherTransaction.start => transaction.commit <= otherTransaction.start

(**************************************************************************)
(* Check types in derived specification                                    *)
(**************************************************************************)
TypeInvariant ==
  /\ State \in [Keys -> Values]
  /\ Transaction \in [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]
  /\ ExecutionElem \in [parentState: State, transaction: Transaction, resultState: State]
  /\ Execution \in Seq(ExecutionElem)

(**************************************************************************)
(* Initialize state with InitValue and transition with Next.               *)
(**************************************************************************)
Init == State = [k \in Keys |-> InitValue]
Next == \E transaction \in Transaction : State' = ApplyTransaction(State, transaction)

(**************************************************************************)
(* Initialize state with Init and transition with Next.                    *)
(**************************************************************************)
Spec == Init /\ [][Next]_State

(**************************************************************************)
(* Theorem to check the type invariant                                     *)
(**************************************************************************)
THEOREM Spec => []TypeInvariant
=============================================================================