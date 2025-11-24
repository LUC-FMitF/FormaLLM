---- MODULE HDiskSynod ----

(***************************************************************************)
(* Modification History
   Last modified Sat Jan 26 15:52:41 CET 2019 by tthai
   Created Sat Jan 26 15:23:57 CET 2019 by tthai
   \/ (bk.bal = 0) ≡ (bk.inp = NotAnInput)*)
(***************************************************************************)

CONSTANTS   Bank, Inp, NotAnInput
VARIABLES   bk

Bank == [bk.bal ∈ Nat, bk.inp ∈ Inp]

Init == bk.bal = 0 /\ bk.inp = NotAnInput

Next ==
  \/ bk.inp = NotAnInput /\ bk.bal' = bk.bal
  \/ bk.inp /= NotAnInput /\ bk.bal' = bk.bal + bk.inp

Spec == Init /\ [][Next]_<<bk.bal>>

INVARIANTS
  InvBalance == bk.bal >= 0
  InvInput == bk.inp ∈ {NotAnInput, Inp1, Inp2, ..., InpN}

TLC CONFIGURATION
  CONSTANTS
    Bank = 1..1000
    Inp = {NotAnInput, Inp1, Inp2, ..., InpN}
  SPECIFICATION Spec
  INVARIANTS InvBalance, InvInput
=============================================================================
====