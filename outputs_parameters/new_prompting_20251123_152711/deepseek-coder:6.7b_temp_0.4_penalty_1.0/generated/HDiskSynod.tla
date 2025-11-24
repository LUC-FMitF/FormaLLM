---- MODULE HDiskSynod ----

(***************************************************************************)
(* Modification History
(* Last modified Sat Jan 26 15:52:41 CET 2019 by tthai
(* Created Sat Jan 26 15:23:57 CET 2019 by tthai
(* 
(* \ (bk.bal ≡ 0) ≡ (bk.inp ≡ NotAnInput)*)
(***************************************************************************)

CONSTANTS   NotAnInput,
            Input1,
            Input2

VARIABLES   bk.bal,
            bk.inp

Init ==
    /\ bk.bal = 0
    /\ bk.inp = NotAnInput

Next ==
    /\ (bk.inp = Input1) -> 
        (bk.bal' = bk.bal + 1) 
        /\ bk.inp' = NotAnInput
    /\ (bk.inp = Input2) -> 
        (bk.bal' = bk.bal - 1) 
        /\ bk.inp' = NotAnInput
    /\ (bk.inp = NotAnInput) -> 
        bk.bal' = bk.bal
        /\ bk.inp' = bk.inp

Spec == Init /\ [][Next]_<<bk.bal,bk.inp>>

TLC_CONFIG
CONSTANTS NotAnInput = 0,
           Input1 = 1,
           Input2 = 2

INVARIANTS
bk_bal_invariant == (bk.bal >= 0)

====