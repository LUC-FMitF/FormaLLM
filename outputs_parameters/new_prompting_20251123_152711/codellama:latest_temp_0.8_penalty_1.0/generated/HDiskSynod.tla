---- MODULE HDiskSynod ----

(**************************************************************************)
(* Modification History                                                   *)
(**************************************************************************)
(* Last modified Sat Jan 26 15:52:41 CET 2019 by tthai                     *)
(**************************************************************************)
(**************************************************************************)
(* Created Sat Jan 26 15:23:57 CET 2019 by tthai                           *)
(**************************************************************************)

CONSTANTS   Input,           \* The set of all inputs.
            Bal,             \* The set of all balances.
            NotAnInput       \* A special input that is not an input.
VARIABLES   bk,              \* The bank's state.
            inp,             \* The input variable.
            bal              \* The balance variable.
----------------------------------------------------------------------------
Input == 1..5
Bal == 0..10

Next ==
    /\ \E inp \in Input :
        \A inp' \in Input :
            inp' = inp + 1
    /\ \E bal \in Bal :
        \A bal' \in Bal :
            bal' = bal + 1

Spec == \* Initialize state with Init and transition with Next.
    Init /\ [][Next]_<<bk, inp, bal>>

=============================================================================
====