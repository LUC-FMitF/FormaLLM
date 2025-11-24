---- MODULE HDiskSynod ----

(**************************************************************************)
(* Modification History                                                    *)
(**************************************************************************)
/\ (bk.bal = 0) \equiv (bk.inp = NotAnInput)
=============================================================================


CONSTANTS   bal, inp    \* The balance and input of the bank account.
VARIABLES   bk        \* The state of the bank account.
=============================================================================
Init ==  /\ bk = (bal = 0) /\ inp = NotAnInput     \* Initial predicate.
=============================================================================
Next ==    \/ \E bal' : (bk = bal')                             \* Transition relation.
           [] bal' = bal + inp - fee(inp) ∧ 0 <= inp ∧ inp < inf   \* Add a valid input to the balance and subtract the fee from it.
           [] bal' = bal                                         \* Otherwise, keep the current balance.
=============================================================================
Spec == Init /\ [][Next]_<<bk>>      \* Specification: Initial predicate followed by transition relation.
=============================================================================
THEOREM Spec => (bal = 0) ==> (inp = NotAnInput)   \* Type invariant: If the balance is zero, then the input must be NotAnInput.
=============================================================================
\* The bank account has a fee for each valid input.                     *)
fee(i) == IF i < 0 THEN -1 ELSE 0 ENDIF   \* Fee for negative inputs is -1, otherwise it's zero.
=============================================================================
TLC CONFIGURATION BEGIN
CONSTANTS bal = {0} inp = NotAnInput
SPECIFICATION Spec
INVARIANT (bal = 0) ==> (inp = NotAnInput)
GENERATED_INITIAL_STATE bk.bal = 0 /\ bk.inp = NotAnInput
TLC CONFIGURATION END
====