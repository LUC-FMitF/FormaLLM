---- MODULE HDiskSynod ----

(***************************************************************************)
(* Modification History                                                     *)
(***************************************************************************)

CONSTANTS   Input,  \* The set of all inputs.
            Output, \* The set of all outputs.
            Balance,    \* The set of all balances.
VARIABLES   bk,     \* A bank account with balance and input/output.
            inp,     \* The current input.
            out      \* The current output.
----------------------------------------------------------------------------
NoInput ==    \* Choose something to represent the absence of an input.
    CHOOSE i : i \notin Input

BankAccount == \* The set of all bank accounts.
    [Balance -> Nat, inp -> Input, out -> Output]

Init == \* The initial predicate.
    /\ bk = [bal := 0, inp := NoInput, out := NoOutput]
    
TypeInvariant ==    \* The type invariant.
    /\ bk \in BankAccount
    /\ inp \in Input
    /\ out \in Output
    
InputTransfer ==
    /\ bk.bal > 0
    /\ inp = Transfer(bk.bal)
    /\ bk' = [bal := bk.bal - inp, inp := NoInput]
    /\ out = NotAnOutput
    /\ UNCHANGED <<bk.out>>
    
OutputTransfer ==
    /\ bk.bal > 0
    /\ inp = NotAnInput
    /\ out = Transfer(bk.bal)
    /\ bk' = [bal := bk.bal - out, inp := NoInput]
    /\ UNCHANGED <<bk.inp>>
    
NoOutput == \* Choose something to represent the absence of an output.
    CHOOSE o : o \notin Output

TypeOK ==    \* Type invariants.
    /\ bk.bal >= 0
    /\ bk.inp \in Input
    /\ bk.out \in Output
    
TxLifecycle ==
    /\ \A bk' \in BankAccount : (bk'.bal = bk.bal) => (bk'.inp = NoInput /\ bk'.out = NoOutput)
    /\ \A i \in Input : (i = Transfer(bk.bal)) => (bk'.bal > 0)
    /\ \A o \in Output : (o = Transfer(bk.bal)) => (bk'.bal > 0)
    
Next == \* The next-state relation.
    \/ \E bk' \in BankAccount : InputTransfer
    \/ \E bk' \in BankAccount : OutputTransfer
    \/ \E i \in Input : (i = NotAnInput) => (bk'.bal = bk.bal /\ bk'.inp = NoInput /\ bk'.out = NoOutput)
    \/ \E o \in Output : (o = NotAnOutput) => (bk'.bal = bk.bal /\ bk'.inp = NoInput /\ bk'.out = NoOutput)
        
Spec == \* Initialize state with Init and transition with Next.
    Init /\ [][Next]_<<bk, inp, out>>
=============================================================================
====