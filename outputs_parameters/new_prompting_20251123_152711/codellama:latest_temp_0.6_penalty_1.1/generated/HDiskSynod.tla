---- MODULE HDiskSynod ----

(***************************************************************************)
(* Modification History                                                     *)
(***************************************************************************)

CONSTANTS   Input,    \* The set of all inputs.
            Balance  \* The set of all balances.
VARIABLES   bank,    \* A data store mapping accounts to balances.
            inp      \* The input for the current transaction.
----------------------------------------------------------------------------
Init == \* The initial predicate.
    /\ bank = [a \in Account |-> bk \in Balance]  \* A data store mapping accounts to balances.
    /\ inp = NotAnInput   \* The input for the current transaction.
    
TypeInvariant ==    \* The type invariant.
    /\ bank \in [Account -> Balance]
    /\ inp \in Input
    
Transfer(a1, a2, v) ==    \* Transfer v from account a1 to account a2.
    /\ a1 \in Account
    /\ a2 \in Account
    /\ v \in Val
    /\ bank[a1] >= v
    /\ bank' = [bk |-> IF bk.acc = a1 THEN bk.bal - v ELSE bk.bal ENDIF]
    /\ bank'' = [bk |-> IF bk.acc = a2 THEN bk.bal + v ELSE bk.bal ENDIF]
    /\ UNCHANGED <<inp, bank>>
    
Check(a1, a2) == \* Check if account a1 has sufficient funds to transfer to account a2.
    /\ a1 \in Account
    /\ a2 \in Account
    /\ inp = Transfer(a1, a2, 10)
    /\ bank' = [bk |-> IF bk.acc = a1 THEN bk.bal - 10 ELSE bk.bal ENDIF]
    /\ bank'' = [bk |-> IF bk.acc = a2 THEN bk.bal + 10 ELSE bk.bal ENDIF]
    
Spec == \* The specification.
    Init /\ [][Next]_<<bank, inp>>
    
Invariant == \* The invariant.
    TypeInvariant /\ bank' \in [Account -> Balance]
    /\ inp' = Transfer(a1, a2, v) => Check(a1, a2)
    
Next == \* The next-state relation.
    \/ \E a1 \in Account : \E a2 \in Account : \E v \in Val : Transfer(a1, a2, v)
    \/ \E inp : Check(a1, a2)
----------------------------------------------------------------------------
THEOREM Spec => Invariant
=============================================================================
====