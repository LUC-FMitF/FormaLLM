---- MODULE BankAccount ----
(***************************************************************************)
(* A simple model of a bank account. The account has a balance, which is   *)
(* initially 0. The account can receive inputs, which are either deposits  *)
(* or withdrawals. A deposit increases the balance by the amount of the    *)
(* deposit, and a withdrawal decreases the balance by the amount of the    *)
(* withdrawal. If the balance is 0, then the account is not expecting any  *)
(* inputs.                                                                 *)
(***************************************************************************)

EXTENDS Integers, Sequences

CONSTANTS NotAnInput

VARIABLES bk

vars == << bk >>

(***************************************************************************)
(* The initial state of the bank account.                                  *)
(***************************************************************************)
Init ==
    /\ bk.bal = 0
    /\ bk.inp = NotAnInput

(***************************************************************************)
(* The next state relation.                                                *)
(***************************************************************************)
Next ==
    \/ /\ bk.inp \in Nat
       /\ bk.bal' = bk.bal + bk.inp
       /\ bk.inp' = NotAnInput
    \/ /\ bk.inp \in -Nat
       /\ bk.bal' = bk.bal + bk.inp
       /\ bk.inp' = NotAnInput

(***************************************************************************)
(* The specification.                                                      *)
(***************************************************************************)
Spec ==
    Init /\ [][Next]_vars

(***************************************************************************)
(* If the balance is 0, then the account is not expecting any inputs.      *)
(***************************************************************************)
NoInputWhenZero ==
    (bk.bal = 0) <=> (bk.inp = NotAnInput)

=============================================================================