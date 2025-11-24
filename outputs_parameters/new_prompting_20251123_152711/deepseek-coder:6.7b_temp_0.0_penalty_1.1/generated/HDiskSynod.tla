---- MODULE HDiskSynod ----

(***************************************************************************)
(* Modification History                                                     *)
(* Last modified Sat Jan 26 15:52:41 CET 2019 by tthai                      *)
(* Created Sat Jan 26 15:23:57 CET 2019 by tthai                          *)
(***************************************************************************)

CONSTANTS   NotAnInput,     \* Represents the absence of an input.
            InitialBalance  \* The initial balance in a bank account.

VARIABLES   bk               \* A bank account with balance and input.

----------------------------------------------------------------------------
Init == /\ (bk.bal = InitialBalance) /\ (bk.inp = NotAnInput)

Next == [bk]_v . bal' = IF v > 0 THEN bk.bal + v ELSE bk.bal - (-v)
     /\ [bk]_v . inp' = IF v > 0 THEN "Deposit" ELSE "Withdrawal"
     /\ (bk.bal ≠ 0) ≡ (bk.inp ≠ NotAnInput)

Spec == Init /\ [][Next]_<<bk>>

TLC Configuration:
CONSTANTS InitialBalance = 100, NotAnInput = "No Input"
SPECIFICATION Spec
INVARIANTS (bk.bal ≠ 0) ≡ (bk.inp ≠ NotAnInput)
=============================================================================
====