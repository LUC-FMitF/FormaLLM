---- MODULE HDiskSynod ----
EXTENDS TLC

CONSTANTS Deposit, Withdrawal = 1

VARIABLES bk.bal, bk.inp

TypeOK == bk.bal IN Nat /\ bk.inp = NotAnInput

Init == bk.bal = 0 /\ bk.inp = NotAnInput

Next == (bk'.bal = bk.bal + d /\ bk'.inp = NotAnInput) 
        \/ (bk'.bal = bk.bal - d /\ bk'.inp = NotAnInput)
        \/ (bk'.bal = bk.bal /\ bk'.inp = bk.inp)

Spec == Init /\ []Next_<<bk>>

TLC Configuration:
CONSTANTS Deposit, Withdrawal = 1
SPECIFICATION Spec
INVARIANTS TypeOK
====