---- MODULE Bank ----
(***************************************************************************)
(* This module models a simple bank account with a balance. The balance    *)
(* can be increased by depositing money and decreased by withdrawing money.*)
(* The balance cannot go below 0. If a withdrawal would result in a        *)
(* negative balance, the withdrawal is not performed.                      *)
(***************************************************************************)

EXTENDS Integers, Sequences, TLC

CONSTANTS NotAnInput

VARIABLES bk

(***************************************************************************)
(* The initial state of the bank account. The balance is 0 and there is no *)
(* pending input.                                                          *)
(***************************************************************************)
Init ==
    /\ bk.bal = 0
    /\ bk.inp = NotAnInput

(***************************************************************************)
(* The type invariant ensures that the balance is a natural number and the *)
(* input is either a natural number or the special value NotAnInput.       *)
(***************************************************************************)
TypeInvariant ==
    /\ bk.bal \in Nat
    /\ bk.inp \in Nat \cup {NotAnInput}

(***************************************************************************)
(* Deposit money into the bank account. The amount to deposit is given by  *)
(* the input. After the deposit, the input is reset to NotAnInput.         *)
(***************************************************************************)
Deposit ==
    /\ bk.inp \in Nat
    /\ bk.bal' = bk.bal + bk.inp
    /\ bk.inp' = NotAnInput

(***************************************************************************)
(* Withdraw money from the bank account. The amount to withdraw is given   *)
(* by the input. If the withdrawal would result in a negative balance, the *)
(* withdrawal is not performed. After the withdrawal, the input is reset   *)
(* to NotAnInput.                                                          *)
(***************************************************************************)
Withdraw ==
    /\ bk.inp \in Nat
    /\ IF bk.bal >= bk.inp
         THEN bk.bal' = bk.bal - bk.inp
         ELSE bk.bal' = bk.bal
    /\ bk.inp' = NotAnInput

(***************************************************************************)
(* The next-state relation.                                                *)
(***************************************************************************)
Next ==
    \/ Deposit
    \/ Withdraw

(***************************************************************************)
(* The specification.                                                      *)
(***************************************************************************)
Spec ==
    Init /\ [][Next]_bk

(***************************************************************************)
(* The balance is 0 if and only if the input is NotAnInput.                *)
(***************************************************************************)
BalanceZeroIffInputNotAnInput ==
    (bk.bal = 0) <=> (bk.inp = NotAnInput)

=============================================================================