---- MODULE BankAccount  ----
(***************************************************************************)
(* Modification History
   Last modified Sat Jan 26 15:52:41 CET 2019 by tthai
   Created Sat Jan 26 15:23:57 CET 2019 by tthai
   \/ (bk.bal = 0) ≡ (bk.inp = NotAnInput)*)
(***************************************************************************)

CONSTANTS   NotAnInput,      \* Represents the absence of an input.
            Deposit,         \* Represents a deposit operation.
            Withdrawal       \* Represents a withdrawal operation.

VARIABLES   bk.bal,          \* The balance of the bank account.
            bk.inp          \* The input operation.

ASSUME  \* Assume the initial state.
    Init == bk.bal = 0 /\ bk.inp = NotAnInput

NEXT  \* Define the next-state relation.
    Next == [bk.bal' = IF bk.inp = Deposit THEN bk.bal + 1 ELSE bk.bal - 1,
             bk.inp' = IF bk.inp = Deposit THEN Withdrawal ELSE NotAnInput]

SPECIFICATION Spec == Init /\ [](bk.bal > 0) <==> (bk.inp = Deposit)

INVARIANTS Inv == [bk.bal >= 0]

TLC_CONFIG ==
  CONSTANTS
    NotAnInput = 0,
    Deposit = 1,
    Withdrawal = 2,
  INITIAL_STATES
    Init == <<bk.bal, bk.inp>>
====