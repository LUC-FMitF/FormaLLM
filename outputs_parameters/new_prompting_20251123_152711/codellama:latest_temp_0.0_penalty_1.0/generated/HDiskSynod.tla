---- MODULE HDiskSynod ----

(***************************************************************************)
(* Modification History                                                     *)
(***************************************************************************)

(* Last modified Sat Jan 26 15:52:41 CET 2019 by tthai *)
(* Created Sat Jan 26 15:23:57 CET 2019 by tthai *)

CONSTANTS
  Inp,  \* The set of all inputs.
  Bal,  \* The set of all balances.
  NotAnInput,  \* A special value to represent an invalid input.
  NoBalance  \* A special value to represent an invalid balance.

VARIABLES
  bk,  \* The bank account.
  inp,  \* The input.
  bal  \* The balance.

----------------------------------------------------------------------------

Init ==
  /\ bk.bal = 0
  /\ bk.inp = NotAnInput

Next ==
  \/ \E inp \in Inp :
    (
      /\ inp = Deposit(d)
      /\ bal' = bk.bal + d
      /\ bk' = bk WITH [bal := bal']
    )
  \/ \E inp \in Inp :
    (
      /\ inp = Withdraw(w)
      /\ bal' = bk.bal - w
      /\ bk' = bk WITH [bal := bal']
    )
  \/ \E inp \in Inp :
    (
      /\ inp = Balance
      /\ bal' = bk.bal
      /\ bk' = bk WITH [bal := bal']
    )

Spec == Init /\ [][Next]_<<bk, inp, bal>>

=============================================================================
====