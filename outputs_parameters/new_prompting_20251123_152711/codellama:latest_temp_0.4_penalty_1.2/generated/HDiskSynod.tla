---- MODULE HDiskSynod ----

(**********************************************************************)
(* Modification History                                               *)
(**********************************************************************)
(Last modified Sat Jan 26 15:52:41 CET 2019 by tthai)                (* Created Sat Jan 26 15:23:57 CET 2019 by tthai)                       *)
(**********************************************************************)
(* Bank module for the banking system.                               *)
(**********************************************************************)
CONSTANTS   Input,      \* The set of all inputs to the bank.
            Output,     \* The set of all outputs from the bank.
            Balance    \* The set of all balances in the bank.
VARIABLES   bk,         \* The state of the bank.
            inp,        \* Input variable for the next transaction.
            out         \* Output variable for the current transaction.
-----------------------------------------------------------------------------
NoInput ==    \* Choose something to represent the absence of an input.
    CHOOSE i : i \notin Input

BalanceInit ==   \* The initial balance is 0.
    ∀ bk: Balance |-> NoVal,
       inp: Inp -> {NoInput}

InpNext ==      \* Next input function for the bank.
    [inp' \in Input : (bk.bal = 0) => (inp' = NotAnInput)]
    ∧ [out' \in Output : (bk.bal > 0) => (out' = bk.out)]
    ∧ [bk'.bal == bk.bal + inp - out]
    ∧ [bk'.out == out']

InpInv ==       \* Input invariant for the bank.
    /\ bk.inp = NotAnInput => (bk.bal = 0)
    /\ bk.out = NoVal => (bk.bal > 0)
    ∧ [bk'.bal == bk.bal + inp - out]
    ∧ [bk'.out == out']
    ∧ [inp' \in Input : (bk.bal = 0) => (inp' = NotAnInput)]
    ∧ [out' \in Output : (bk.bal > 0) => (out' = bk.out)]

OutNext ==      \* Next output function for the bank.
    [out' \in Output]

OutInv ==       \* Output invariant for the bank.
    ∧ [bk'.bal == bk.bal + inp - out']
    ∧ [out'' \in Output : (bk.bal > 0) => (out'' = bk.out)]

Spec ==         \* The specification of the bank module.
    InpInv /\ OutInv
-----------------------------------------------------------------------------
THEOREM Spec => [](BalanceInit /\ INVARIANTS[InpNext, OutNext])
=============================================================================
====