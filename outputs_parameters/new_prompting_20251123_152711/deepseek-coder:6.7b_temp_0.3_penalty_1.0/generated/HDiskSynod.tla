---- MODULE BankAccount  ----
(*******************************************************************************)
(* Modification History
(* Last modified Sat Jan 26 15:52:41 CET 2019 by tthai
(* Created Sat Jan 26 15:23:57 CET 2019 by tthai
(* /\ (bk.bal = 0) ≡ (bk.inp = NotAnInput)*)
(*******************************************************************************)

EXTENDS ZSequences

CONSTANTS  NotAnInput,
            Deposit,
            Withdraw,
            Transfer,
            Balance,
            Input

VARIABLES  bk == <<>>

(* The set of all bank accounts *)
BankAccounts == {bk}

(* The set of all possible inputs *)
Inputs == {NotAnInput, Deposit, Withdraw, Transfer, Balance}

(* The set of all possible operations *)
Operations == {Deposit, Withdraw, Transfer}

(* The set of all possible invariants *)
Invariants == {Balance, Input}

(* The initial state *)
Init == bk.bal = 0 /\ bk.inp = NotAnInput

(* The next-state relation *)
Next ==
  /\  bk.bal' = IF bk.op = Deposit THEN bk.bal + bk.amt ELSE bk.bal
  /\  bk.bal' = IF bk.op = Withdraw THEN bk.bal - bk.amt ELSE bk.bal'
  /\  bk.bal' = IF bk.op = Transfer THEN bk.bal - bk.amt ELSE bk.bal'
  /\  bk.inp' = IF bk.op = Balance THEN bk.inp ELSE bk.op
  /\  bk.op' = IF bk.inp = NotAnInput THEN bk.op ELSE bk.inp
  /\  bk.amt' = IF bk.inp = NotAnInput THEN bk.amt ELSE bk.bal

(* The specification *)
Spec == Init /\ []Next

(* The invariants *)
InvBalance == [](bk.bal >= 0)
InvInput == [](bk.inp IN Inputs)

(* TLC configuration *)
TLC_CONFIG ==
  CONSTANTS NotAnInput = 0, Deposit = 1, Withdraw = 2, Transfer = 3, Balance = 4, Input = 5,
  SPECIFICATION Spec,
  INVARIANTS InvBalance, InvInput
=============================================================================
====