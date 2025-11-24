---- MODULE HDiskSynod ----

(***************************************************************************)
(* Modification History                                                     *)
(***************************************************************************)

(* Last modified Sat Jan 26 15:52:41 CET 2019 by tthai *)
(* Created Sat Jan 26 15:23:57 CET 2019 by tthai *)

(*
***************************************************************************)
(* The BankAccount module.                                                *)
(*                                                                         *)
(* The module defines a bank account with a balance and an input.          *)
(* The balance can be set to any value, but the input must be a valid     *)
(* input.                                                                 *)
(***************************************************************************)

CONSTANTS
  Balance,  \* The balance of the account.
  Input,    \* The input of the account.
  NotAnInput, \* A value that represents an invalid input.
  ValidInput, \* A value that represents a valid input.
  ValidOutput, \* A value that represents a valid output.
  Output,  \* The output of the account.
VARIABLES
  bk,  \* The bank account.
  inp, \* The input to the account.
  out, \* The output of the account.

Init ==
  /\ bk.bal = 0
  /\ bk.inp = NotAnInput
  /\ bk.out = ValidOutput

Next ==
  \/ \E bk.bal' = bk.bal
  \/ \E bk.inp' = bk.inp
  \/ \E bk.out' = bk.out

Spec ==
  Init /\ [][Next]_<<bk.bal, bk.inp, bk.out>>

TypeInvariant ==
  /\ bk.bal \in Balance
  /\ bk.inp \in Input
  /\ bk.out \in Output

TLCConfig ==
  CONSTANTS
    Balance == {0, 1, 2, 3, 4, 5, 6, 7, 8, 9},
    Input == {NotAnInput, ValidInput},
    Output == {ValidOutput},
  VARIABLES
    bk.bal,
    bk.inp,
    bk.out

=============================================================================
====