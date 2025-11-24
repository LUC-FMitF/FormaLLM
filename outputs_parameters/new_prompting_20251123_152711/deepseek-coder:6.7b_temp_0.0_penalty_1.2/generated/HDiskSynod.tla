---- MODULE HDiskSynod ----

(******************************************************************************)
(* Modification History                                                       *)
(* Last modified Sat Jan 26 15:52:41 CET 2019 by tthai                        *)
(* Created Sat Jan 26 15:23:57 CET 2019 by tthai                             *)
(******************************************************************************)
CONSTANTS   NotAnInput,     \* Represents the absence of an input.
            Input           \* The set of all possible inputs to a bank account operation.
VARIABLES   bk              \* A single instance of BankAccount state variable.
---------------------------------------------------------------------------------
Init ==                     \* Initial predicate for BankAccount module.
    /\ (bk.bal = 0)         \* Initially, the balance is 0.
       [...]                 \* Other invariants...
    ==> ((bk.inp = NotAnInput))   (* If other conditions are met, then no input has been made *)
        /\ (bk.bal = 0)         \* Initially, the balance is 0.
           [...]                 \* Other invariants...
    ==> TRUE                   (* Otherwise, we're in a valid state *)

Next ==                      \* Next-state relation for BankAccount module.
    /\ (bk.inp = NotAnInput)   \* If no input has been made yet:
        [...]                 \* Other operations...
    ==> TRUE                   (* Otherwise, we're in a valid state *)

Spec ==                      \* Specification for BankAccount module.
    Init /\ [][Next]_<<bk>>   \* Start from the initial state and transition according to Next relation.
---------------------------------------------------------------------------------
THEOREM Spec => [](Init)     (* Theorem: If our specification is true, then it must start in a valid state *)
=================================================================================
====                            \* TLC configuration for BankAccount module *)
CONSTANTS Input = {...}       \* Define all possible inputs to the bank account operation.
SPECIFICATION Spec             \* Use our specification as input into TLC.
INVARIANTS Init, Next         \* Include invariants in output of TLC for verification *)
=================================================================================