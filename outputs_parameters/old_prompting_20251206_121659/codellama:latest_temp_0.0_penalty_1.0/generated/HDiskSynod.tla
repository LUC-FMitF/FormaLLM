---- MODULE HDiskSynod ----

(***************************************************************************)
(* Modification History                                                     *)
(***************************************************************************)

CONSTANTS
  NotAnInput == 0

VARIABLES
  bal, inp

Init ==
  /\ bal = 0
  /\ inp = NotAnInput

Next ==
  /\ bal' =
    IF inp = Deposit THEN bal + 10
    ELSE IF inp = Withdraw THEN bal - 10
    ELSE bal
  /\ inp' = NotAnInput

Spec == Init /\ [][Next]_<<bal, inp>>

THEOREM Spec => [](bal >= 0 /\ inp \in {Deposit, Withdraw})
=============================================================================
====