--------------------------- MODULE ClientCentricIsolation ---------------------------
(***************************************************************************)
(* TLA+ specifications of Client Centric Isolation Specification by Crooks et al: https://dl.acm.org/doi/10.1145/3087801.3087802 *)
(* TLA+ specifications by Tim Soethout (tim.soethout@ing.com) et al: Automated Validation of State-Based Client-Centric Isolation with TLA+: https://doi.org/10.1007/978-3-030-67220-1_4 *)
(***************************************************************************)

EXTENDS Sequences, FiniteSets, Naturals

CONSTANTS Keys, Values, InitValue, TimeStamps
ASSUME InitValue \in Values

VARIABLES State, Transactions, TimeStamp

(* A database `State` is represented by keys with corresponding values *)
State == [Keys -> Values]

(* An `Operation` is a read or write of a key and value *)
Operation == [type: {"read", "write"}, key: Keys, value: Values]

(* A `Transaction` is a total order of `Operation`s *)
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

(* We represent an `Execution` as a sequence of `Transaction`s with their corresponding parent state. *)
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]
Execution == Seq(ExecutionElem)

(* Initialization *)
Init == 
  /\ State = [k \in Keys |-> InitValue]
  /\ Transactions = <<>>
  /\ TimeStamp = 0

(* Transition *)
Next ==
  /\ \E t \in Transaction: 
    /\ TimeStamp' = TimeStamp + 1
    /\ Transactions' = Append(Transactions, t)
    /\ State' = [State EXCEPT ![t.ops.key] = t.ops.value]
  /\ UNCHANGED <<TimeStamp>>

(* The specification *)
Spec == Init /\ [][Next]_<<State, Transactions, TimeStamp>>

=============================================================================