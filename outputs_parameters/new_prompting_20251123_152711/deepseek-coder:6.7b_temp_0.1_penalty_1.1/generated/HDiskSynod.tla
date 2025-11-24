---- MODULE HDiskSynod ----

(**************************************************************************)
(* Modification History                                                   *)
(* Last modified Sat Jan 26 15:52:41 CET 2019 by tthai                    *)
(* Created Sat Jan 26 15:23:57 CET 2019 by tthai                         *)
(**************************************************************************)

CONSTANTS   NotAnInput,     \* Represents an input that is not a valid one.
            Input           \* The set of all possible inputs.
VARIABLES   bk              \* A bank account with balance and input.

----------------------------------------------------------------------------
Init ==    \* Initial state predicate.
    /\ bk.bal = 0
    /\ bk.inp = NotAnInput
    
Next ==    \* Next-state relation.
    /\ (bk'.bal = IF bk.inp = Deposit THEN bk.bal + Amount ELSE bk.bal)
    /\ (bk'.inp = IF bk.inp = NotAnInput THEN bk.inp ELSE NotAnInput)
    
Spec ==    \* Initialize state with Init and transition with Next.
    Init /\ []Next_<<bk>>

(* TLC Configuration *)
CONSTANTS Amount = 10, Deposit = TRUE
SPECIFICATION Spec
INVARIANTS "(bk.bal >= 0) /\ (bk.inp = NotAnInput)"
=============================================================================
====