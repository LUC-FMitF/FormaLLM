---- MODULE HDiskSynod ----

(**************************************************************************)
(* Modification History                                                   *)
(* Last modified Sat Jan 26 15:52:41 CET 2019 by tthai                    *)
(* Created Sat Jan 26 15:23:57 CET 2019 by tthai                         *)
(**************************************************************************)

CONSTANTS   NotAnInput,     \* Represents the absence of an input.
            Zero           \* The number zero.

VARIABLES   bk              \* A bank account with balance and input.

----------------------------------------------------------------------------
Init ==    \* Initial state predicate.
    /\ (bk.bal = Zero)      \* The initial balance of the bank account is 0.
    /\ (bk.inp = NotAnInput) \* There is no input at the start.

Next ==    \* Next-state relation.
    /\ (bk'.bal = IF bk.inp = Deposit THEN bk.bal + bk.val ELSE bk.bal - bk.val)  \* If there is a deposit input, add the value to the balance; if there is a withdrawal input, subtract the value from the balance.
    /\ (bk'.inp = IF bk.inp = Deposit THEN Withdraw ELSE NotAnInput)               \* If there was a deposit input, change it to a withdrawal input; if there was no input or a withdrawal input, keep it as is.
    /\ (bk'.val = IF bk.inp = Deposit THEN bk.val ELSE Zero)                       \* The value of the input remains unchanged unless there is a deposit or withdrawal input.

Spec ==   \* Initialize state with Init and transition with Next.
    Init /\ []Next_<<bk>>

INVARIANTS TypeOK, "(bk.bal = Zero) ≡ (bk.inp = NotAnInput)"
=============================================================================
====
TLC Configuration:
CONSTANTS Deposit = 1, Withdraw = -1, Zero = 0
SPECIFICATION Spec
INVARIANTS TypeOK
====