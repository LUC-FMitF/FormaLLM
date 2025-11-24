---- MODULE HDiskSynod ----

(***************************************************************************)
(* Modification History
   Last modified Sat Jan 26 15:52:41 CET 2019 by tthai
   Created Sat Jan 26 15:23:57 CET 2019 by tthai
*)
(* /\ (bk.bal = 0) <==> (bk.inp = NotAnInput) *)
(***************************************************************************)

CONSTANTS   NotAnInput       (* No input to the system *)
VARIABLES   bk               (* Bank account state *)

Next  \/ [](bk.bal = 0 /\ bk.inp = NotAnInput)    (* Initialization and transition relation *)
     \/  EXT (bk.bal > 0  /\ bk.inp = d) ==> -1   (* Deposit *)
     \/  EXT (bk.bal >= 0 /\ bk.inp = w) == 1      (* Withdrawal, balance must be non-negative *)

(* TLC Configuration: *)
CONSTANTS  d = 1, w = -1    (* Deposit and withdrawal operations *)
SPECIFICATION [](bk.bal >= 0 /\ bk.inp = NotAnInput)
INVARIANT   BankAccountInv == bk.bal >= 0       (* Non-negative balance invariant *)
====


This module represents a simple bank account model where deposits (d = 1) and withdrawals (w = -1) are the only operations allowed. The initial state is defined as having zero balance and no input, which means that at any point in time, the system should be in this state unless it has been modified by one of the two transition rules.

The TLC configuration section sets up constants for the deposit (d = 1) and withdrawal (w = -1) operations, specifies a specification for the model, which is that the balance must always be non-negative and that there should be no input at any point in time, and defines an invariant BankAccountInv stating that the balance of the bank account must never be negative.
====