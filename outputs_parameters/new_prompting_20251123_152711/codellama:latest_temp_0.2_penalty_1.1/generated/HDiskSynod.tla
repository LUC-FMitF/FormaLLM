---- MODULE HDiskSynod ----

(**************************************************************************)
(* Modification History                                                    *)
(**************************************************************************)
(**************************************************************************)
(* Created Sat Jan 26 15:23:57 CET 2019 by tthai                          *)
(**************************************************************************)
(* Last modified Sat Jan 26 15:52:41 CET 2019 by tthai                    *)
(**************************************************************************)

CONSTANTS   Input,      \* The set of all inputs.
            Balance,    \* The set of all balances.
            NotAnInput \* A special value to represent the absence of an input.
VARIABLES   bk,         \* The bank account.
            inp,        \* The current input.
            bal         \* The current balance.
----------------------------------------------------------------------------
NoVal ==    \* Choose something to represent the absence of a value.
    CHOOSE v : v \notin Balance

Inputs ==    \* The set of all inputs.
    [Input -> {NotAnInput}]

Balances ==  \* The set of all balances.
    [Balance -> {NoVal}]

Init == \* The initial predicate.
    /\ bk = <<>>                   \* The bank account is initially empty.
    /\ inp = NotAnInput            \* The current input is initially the absence of an input.
    /\ bal = NoVal                 \* The current balance is initially the absence of a balance.
    
TypeInvariant ==    \* The type invariant.
    /\ bk \in BankAccount
    /\ inp \in Inputs
    /\ bal \in Balances
    
InputLaw ==
    /\ (bk.bal = 0) ≡ (bk.inp = NotAnInput)   \* The law of inputs.

Next == \* The next-state relation.
    \/ \E bk' \in BankAccount : Open(bk, inp, bal) => Init /\ [][Next]_<<bk', inp, bal>>
    \/ \E bk' \in BankAccount : Deposit(bk, inp, bal) => Init /\ [][Next]_<<bk', inp, bal>>
    \/ \E bk' \in BankAccount : Withdraw(bk, inp, bal) => Init /\ [][Next]_<<bk', inp, bal>>
    \/ \E bk' \in BankAccount : Close(bk, inp, bal) => Init /\ [][Next]_<<bk', inp, bal>>
        
Spec == \* Initialize state with Init and transition with Next.
    Init /\ [][Next]_<<bk, inp, bal>>
-----------------------------------------------------------------------------
THEOREM Spec => [](TypeInvariant /\ InputLaw)
=============================================================================
====