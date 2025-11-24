---- MODULE HDiskSynod ----

(***************************************************************************)
(* Modification History                                                     *)
(* Last modified Sat Jan 26 15:52:41 CET 2019 by tthai                    *)
(* Created Sat Jan 26 15:23:57 CET 2019 by tthai                           *)
(***************************************************************************)

CONSTANTS   Input,     \* The set of all inputs.
            Balance,   \* The set of all balances.
            NotAnInput,    \* A special value to represent an invalid input.
            INITIAL_BALANCE,  \* The initial balance for a new account.
            MIN_BALANCE,      \* The minimum allowed balance.
            MAX_BALANCE       \* The maximum allowed balance.
VARIABLES   bk,        \* A bank account with input and balance.
            inp,        \* The current input for the account.
            bal         \* The current balance of the account.
----------------------------------------------------------------------------
(* Input properties *)
Input ==    \* The set of all inputs.
    [i \in INPUT |-> i \in {Deposit(a), Withdraw(a)}]

Balance ==  \* The set of all balances.
    [b \in BALANCE |-> b \in {MIN_BALANCE, MAX_BALANCE}]

NotAnInput ==    \* A special value to represent an invalid input.
    CHOOSE a : a \notin Input

INITIAL_BALANCE ==  \* The initial balance for a new account.
    0

MIN_BALANCE ==  \* The minimum allowed balance.
    0

MAX_BALANCE ==  \* The maximum allowed balance.
    1000

(* Bank account properties *)
bk ==    \* A bank account with input and balance.
    [inp |-> NotAnInput, bal |-> INITIAL_BALANCE]

(* Input operations *)
Deposit(a) ==  \* Deposit amount a into the account.
    /\ a > 0
    /\ inp' = Deposit(a)
    /\ bal' = bal + a

Withdraw(a) ==  \* Withdraw amount a from the account.
    /\ a > 0
    /\ inp' = Withdraw(a)
    /\ bal' = bal - a

(* Bank account operations *)
Balance() ==  \* The current balance of the account.
    bal

InputOp() ==    \* The current input for the account.
    inp

Next == \* The next-state relation.
    \/ \E i \in INPUT : Deposit(i)
    \/ \E i \in INPUT : Withdraw(i)
        
Spec == \* Initialize state with Init and transition with Next.
    Init /\ [][Next]_<<bk, inp, bal>>
=============================================================================
====