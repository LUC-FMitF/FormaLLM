---- MODULE HDiskSynod ----

(***************************************************************************)
(* Modification History                                                     *)
(***************************************************************************)

CONSTANTS   Input,    \* The set of all inputs.
            Balance  \* The set of all balances.
VARIABLES   bk,      \* A bank account with balance and input.
            inp      \* The current input.
----------------------------------------------------------------------------
NoInput ==    \* Choose something to represent the absence of an input.
    CHOOSE i : i \notin Input

Balance ==    \* The set of all balances.
    [b \in Nat |-> b >= 0]

BankAccount == \* A bank account with balance and input.
    [bk \in Balance, inp \in Input]

Init == \* The initial predicate.
    /\ bk = [Balance]
    /\ inp = NoInput
    
Next == \* The next-state relation.
    \/ \E i \in Input : (inp = i /\ bk' = bk + 1)
    \/ \E i \in Input : (inp = i /\ bk' = bk - 1)
    \/ \E i \in Input : (inp = i /\ bk' = bk * 2)
    \/ \E i \in Input : (inp = i /\ bk' = bk / 2)
    \/ \E i \in Input : (inp = i /\ bk' = bk + 10)
    \/ \E i \in Input : (inp = i /\ bk' = bk - 10)
    
Spec == \* Initialize state with Init and transition with Next.
    Init /\ [][Next]_<<bk, inp>>
=============================================================================
====