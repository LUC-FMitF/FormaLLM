---- MODULE HDiskSynod ----

(******************************************************************************)
(* Modification History                                                       *)
(* Last modified Sat Jan 26 15:52:41 CET 2019 by tthai                         *)
(* Created Sat Jan 26 15:23:57 CET 2019 by tthai                              *)
(******************************************************************************)
CONSTANTS   NotAnInput,     \* Represents the absence of an input.
            Input           \* The set of all possible inputs to a bank account operation.
VARIABLES   bk              \* A bank account with balance and pending input.
---------------------------------------------------------------------------------
Init ==                     \* Initial state predicate for BankAccount module. 
    /\ (bk.bal = 0)         \* The initial balance of the bank account is zero.
       /\ (bk.inp = NotAnInput)\* There's no pending input at initialization time.
    
Next ==                     \* Next-state relation for BankAccount module. 
    \(/ bk.bal > 0 ->        \* If the balance is positive, we can only decrease it by an amount equal to a valid input value:
         EXISTS x : Input /\ (bk'.bal = bk.bal + x) /\ (bk'.inp = NotAnInput)) 
       OTHERWISE             \* If the balance is zero, we can only increase it by an amount equal to a valid input value:
         EXISTS y : Input /\ (bk'.bal = bk.bal - y) /\ (bk'.inp = NotAnInput)) 
    
Spec ==                     \* Specification for BankAccount module, initialized with Init and transitioned by Next.
    Init /\ [](Next)\_<<bk>>   (* The specification is valid if the initial state satisfies Init and all reachable states satisfy Next *)
===============================================================================
(* TLC Configuration                                                        *)
CONSTANTS  Input = {-1, 50} \* Possible input values: -1 (deposit) or 50.
SPECIFICATION Spec
INVARIANTS "bk.bal >= 0"    (* The balance of a bank account cannot be negative *)
====