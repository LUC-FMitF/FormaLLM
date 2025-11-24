---- MODULE HDiskSynod ----

(**************************************************************************)
(* Modification History                                                      *)
(* Last modified Sat Jan 26 15:52:41 CET 2019 by tthai                        *)
(* Created Sat Jan 26 15:23:57 CET 2019 by tthai                              *)
(**************************************************************************)

CONSTANTS
    Inp,       \* The set of all inputs.
    Act,       \* The set of all actions.
    S,         \* The set of all states.
    B,         \* The set of all bank accounts.
    Bal        \* The set of all balances.
VARIABLES
    bk,        \* The current bank.
    bk'        \* The next bank.
    inp,       \* The current input.
    inp'       \* The next input.
    act,       \* The current action.
    act'       \* The next action.
    s,         \* The current state.
    s'         \* The next state.
    b,         \* The current balance.
    b'         \* The next balance.
    SPEC,      \* The specification.
    INV,       \* The invariants.
    ASSUME,    \* The initial assumption.
    ASSUME'    \* The next assumption.
    PROVE,     \* The initial proof.
    PROVE'     \* The next proof.

INIT ==
    /\ bk = <<>>
    /\ inp = NotAnInput
    /\ act = NoAction
    /\ s = <<>>
    /\ b = <<>>
    /\ SPEC = FALSE
    /\ INV = FALSE
    /\ ASSUME = TRUE
    /\ ASSUME' = TRUE
    /\ PROVE = FALSE
    /\ PROVE' = FALSE

Next ==
    /\ (bk' = bk) \/ (inp' = inp) \/ (act' = act) \/ (s' = s) \/ (b' = b)
    /\ (SPEC' = SPEC) \/ (INV' = INV) \/ (ASSUME' = ASSUME) \/ (PROVE' = PROVE)

Transfer ==
    /\ bk' = <<>>
    /\ inp' = NotAnInput
    /\ act' = Transfer
    /\ s' = <<>>
    /\ b' = <<>>
    /\ SPEC' = FALSE
    /\ INV' = FALSE
    /\ ASSUME' = FALSE
    /\ PROVE' = FALSE
    /\ (SPEC = FALSE) \/ (INV = FALSE) \/ (ASSUME = TRUE) \/ (PROVE = FALSE)

Withdraw ==
    /\ bk' = <<>>
    /\ inp' = NotAnInput
    /\ act' = Withdraw
    /\ s' = <<>>
    /\ b' = <<>>
    /\ SPEC' = FALSE
    /\ INV' = FALSE
    /\ ASSUME' = FALSE
    /\ PROVE' = FALSE
    /\ (SPEC = FALSE) \/ (INV = FALSE) \/ (ASSUME = TRUE) \/ (PROVE = FALSE)

Deposit ==
    /\ bk' = <<>>
    /\ inp' = NotAnInput
    /\ act' = Deposit
    /\ s' = <<>>
    /\ b' = <<>>
    /\ SPEC' = FALSE
    /\ INV' = FALSE
    /\ ASSUME' = FALSE
    /\ PROVE' = FALSE
    /\ (SPEC = FALSE) \/ (INV = FALSE) \/ (ASSUME = TRUE) \/ (PROVE = FALSE)

NoAction ==
    /\ bk' = bk
    /\ inp' = inp
    /\ act' = NoAction
    /\ s' = s
    /\ b' = b
    /\ SPEC' = FALSE
    /\ INV' = FALSE
    /\ ASSUME' = FALSE
    /\ PROVE' = FALSE
    /\ (SPEC = FALSE) \/ (INV = FALSE) \/ (ASSUME = TRUE) \/ (PROVE = FALSE)

Transfer' ==
    /\ bk' = <<>>
    /\ inp' = NotAnInput
    /\ act' = Transfer
    /\ s' = <<>>
    /\ b' = <<>>
    /\ SPEC' = FALSE
    /\ INV' = FALSE
    /\ ASSUME' = FALSE
    /\ PROVE' = FALSE
    /\ (SPEC = FALSE) \/ (INV = FALSE) \/ (ASSUME = TRUE) \/ (PROVE = FALSE)

Withdraw' ==
    /\ bk' = <<>>
    /\ inp' = NotAnInput
    /\ act' = Withdraw
    /\ s' = <<>>
    /\ b' = <<>>
    /\ SPEC' = FALSE
    /\ INV' = FALSE
    /\ ASSUME' = FALSE
    /\ PROVE' = FALSE
    /\ (SPEC = FALSE) \/ (INV = FALSE) \/ (ASSUME = TRUE) \/ (PROVE = FALSE)

Deposit' ==
    /\ bk' = <<>>
    /\ inp' = NotAnInput
    /\ act' = Deposit
    /\ s' = <<>>
    /\ b' = <<>>
    /\ SPEC' = FALSE
    /\ INV' = FALSE
    /\ ASSUME' = FALSE
    /\ PROVE' = FALSE
    /\ (SPEC = FALSE) \/ (INV = FALSE) \/ (ASSUME = TRUE) \/ (PROVE = FALSE)

NoAction' ==
    /\ bk' = bk
    /\ inp' = inp
    /\ act' = NoAction
    /\ s' = s
    /\ b' = b
    /\ SPEC' = FALSE
    /\ INV' = FALSE
    /\ ASSUME' = FALSE
    /\ PROVE' = FALSE
    /\ (SPEC = FALSE) \/ (INV = FALSE) \/ (ASSUME = TRUE) \/ (PROVE = FALSE)

Spec ==
    /\ bk = <<>>
    /\ inp = NotAnInput
    /\ act = NoAction
    /\ s = <<>>
    /\ b = <<>>
    /\ SPEC = TRUE
    /\ INV = FALSE
    /\ ASSUME = TRUE
    /\ PROVE = FALSE

Inv ==
    /\ bk = <<>>
    /\ inp = NotAnInput
    /\ act = NoAction
    /\ s = <<>>
    /\ b = <<>>
    /\ SPEC = FALSE
    /\ INV = TRUE
    /\ ASSUME = FALSE
    /\ PROVE = FALSE

Assume ==
    /\ bk = <<>>
    /\ inp = NotAnInput
    /\ act = NoAction
    /\ s = <<>>
    /\ b = <<>>
    /\ SPEC = FALSE
    /\ INV = FALSE
    /\ ASSUME = TRUE
    /\ PROVE = FALSE

Prove ==
    /\ bk = <<>>
    /\ inp = NotAnInput
    /\ act = NoAction
    /\ s = <<>>
    /\ b = <<>>
    /\ SPEC = FALSE
    /\ INV = FALSE
    /\ ASSUME = FALSE
    /\ PROVE = TRUE

------------------------------------------------------------------------------
====