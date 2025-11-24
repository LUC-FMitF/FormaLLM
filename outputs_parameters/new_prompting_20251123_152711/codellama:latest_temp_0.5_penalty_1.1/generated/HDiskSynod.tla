---- MODULE HDiskSynod ----

(**************************************************************************)
(* Modification History                                                     *)
(* Last modified Sat Jan 26 15:52:41 CET 2019 by tthai                      *)
(* Created Sat Jan 26 15:23:57 CET 2019 by tthai                             *)
(**************************************************************************)

CONSTANTS   Input,          \* The set of all inputs.
            Output,         \* The set of all outputs.
            State           \* The state of the banking system.
VARIABLES   bk,             \* The banking system.
            inp,            \* The current input.
            out,            \* The current output.
            bal             \* The balance of the bank account.
----------------------------------------------------------------------------
NoInput ==    \* Choose something to represent the absence of an input.
    CHOOSE i : i \notin Input

InputSet ==    \* The set of all inputs.
    [i \in Input |-> TRUE]

OutputSet ==   \* The set of all outputs.
    [o \in Output |-> TRUE]

StateSet ==    \* The state of the banking system.
    [s \in State |-> TRUE]

BkInit == \* The initial state of the banking system.
    /\ bk = <<>>                     \* The banking system is initially empty.
    /\ inp = NoInput                 \* There is no input to the banking system.
    /\ out = OutputSet               \* All outputs are initially available.
    /\ bal = 0                       \* The balance of the bank account is initially zero.
    
TypeInvariant ==    \* The type invariant.
    /\ bk \in StateSet
    /\ inp \in InputSet
    /\ out \in OutputSet
    /\ bal \in Nat

TxLifecycle ==
    /\ \A s \in State : (bk = <<>> \/ bk[s] = NoInput) => (out = [o \in Output |-> TRUE])  \* All outputs are initially available.
    /\ \A s \in State : (bk = <<>> \/ bk[s] = NoInput) => (bal = 0)                          \* The balance of the bank account is initially zero.
    
BkLemma(s1, s2) ==    \* A lemma for the transition function.
    /\ s1 \in State
    /\ s2 \in State
    /\ s1[bk] = s2[bk]
    => (IF bk[s1] = NoInput THEN out[s1] = out[s2] ELSE TRUE)
    /\ (IF bk[s1] = NoInput THEN bal[s1] = bal[s2] ELSE TRUE)
    
BkTrans(s1, s2) ==    \* The transition function.
    /\ s1 \in State
    /\ s2 \in State
    /\ (IF bk[s1] = NoInput THEN out[s1] = out[s2] ELSE TRUE)
    /\ (IF bk[s1] = NoInput THEN bal[s1] = bal[s2] ELSE TRUE)
    => s2 \in State
    
Spec == \* Initialize state with BkInit and transition with BkTrans.
    BkInit /\ [](TypeInvariant /\ TxLemma(_, _) /\ TxLifecycle)
=============================================================================
====