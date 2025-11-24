---- MODULE ClientCentric ----
EXTENDS FiniteSets, Naturals, Sequences

---- CONSTANTS ----
(* Constants used in the module *)
CONSTANTS InitValue = _|_ (* The initial value of a state *)

---- VARIABLES ----
(* Variables used in the module *)
VARIABLES 
  Keys, Values, TimeStamp, Operation, Transaction, State, Execution

---- INVARIANTS ----
(* Invariants for the module *)
INVARIANTS
  TypeOK[State, {Keys, Values, TimeStamp, Operation, Transaction, Execution}]

---- FUNCTIONS ----
(* Functions defined in the module *)
FUNCTIONS
  IsSerializable /\ InitValue \in Values
    \* if no executions satisfy commit test, print all executions
  /\ (~\E execution \in executions(initialState, transactions): 
      \A transaction \in transactions: CT_SER(transaction, execution)) 
    => \A execution \in executions(initialState, transactions): PrintT(<<"Execution not Serializable:",execution>>)
    \* fall back to normal check
  /\ (~\E execution \in executions(initialState, transactions): 
      \A transaction \in transactions: CT_SER(transaction, execution))
    => \E execution \in executions(initialState, transactions): PrintT(<<"Execution not Serializable:",execution>>)

---- SPECIFICATION ----
(* Specification for the module *)
SPECIFICATION Isolation == IsSerializable(initialState, transactions)

---- END OF MODULE ----
====