---- MODULE HDiskSynod ----

(***************************************************************************)
(* Modification History                                                     *)
(***************************************************************************)

CONSTANTS   Input,    \* The set of all inputs.
            Balance,  \* The set of all balances.
            NotAnInput,  \* A special value to represent an invalid input.
            NoBalance,  \* A special value to represent an invalid balance.
VARIABLES   bk,       \* The bank account.
            inp,       \* The current input.
            bal        \* The current balance.
----------------------------------------------------------------------------
Init == \* The initial predicate.
    /\ bk = [inp |-> NotAnInput, bal |-> NoBalance]
    /\ inp = Input
    /\ bal = 0
    
Next == \* The next-state relation.
    \/ \E inp' \in Input : (inp' = inp /\ bal = bal)
    \/ \E inp' \in Input : (inp' != inp /\ bal = bal + 1)
    \/ \E inp' \in Input : (inp' != inp /\ bal = bal - 1)
    
Spec == \* Initialize state with Init and transition with Next.
    Init /\ [][Next]_<<bk, inp, bal>>
=============================================================================
====