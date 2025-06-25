---- MODULE BankAccount ----
(***************************************************************************)
(* A simple model of a bank account. The account has a balance, which is   *)
(* initially 0. The account can receive inputs, which are either deposits  *)
(* or withdrawals. Each input has an associated amount. The balance of the *)
(* account after processing an input is the previous balance plus the      *)
(* amount of the input if the input is a deposit, or the previous balance  *)
(* minus the amount of the input if the input is a withdrawal. If the      *)
(* balance of the account is 0, then the last input to the account must    *)
(* have been a withdrawal.                                                 *)
(***************************************************************************)

EXTENDS Integers, Sequences

CONSTANTS NotAnInput

VARIABLES bk

vars == << bk >>

(***************************************************************************)
(* The type of an input to the account.                                    *)
(***************************************************************************)
InputType == { "deposit", "withdrawal" }

(***************************************************************************)
(* The type of an input to the account.                                    *)
(***************************************************************************)
Input == [ type: InputType, amount: Nat ]

(***************************************************************************)
(* The type of the bank account.                                           *)
(***************************************************************************)
BankAccount == [ bal: Int, inp: Input \cup {NotAnInput} ]

(***************************************************************************)
(* The initial state of the bank account.                                  *)
(***************************************************************************)
Init == bk = [ bal |-> 0, inp |-> NotAnInput ]

(***************************************************************************)
(* The next state relation.                                                *)
(***************************************************************************)
Next ==
  /\ bk' \in BankAccount
  /\ IF bk'.inp.type = "deposit"
       THEN bk'.bal = bk.bal + bk'.inp.amount
       ELSE bk'.bal = bk.bal - bk'.inp.amount
  /\ (bk'.bal = 0) <=> (bk'.inp = NotAnInput)

(***************************************************************************)
(* The specification.                                                      *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars
=============================================================================