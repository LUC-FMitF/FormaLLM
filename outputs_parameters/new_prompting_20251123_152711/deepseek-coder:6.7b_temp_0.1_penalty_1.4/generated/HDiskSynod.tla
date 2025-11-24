---- MODULE HDiskSynod -----
------------------------------- MODULE ACCOUNTBALANCE ENDS----------------------------------
(*******************************************************************************************)
(* Modification History                                                                   *)
(* Last modified Sat Jan 26 15:52:41 CET 2019 by tthai                                     *)
(* Created Sun Feb 3 17:28:57 IST 2019 by tthai                                           *)
(*******************************************************************************************)
CONSTANTS Balance, Inputs \* The set of all possible balances and inputs.
VARIABLES bk = <<bal := NotAnInput>> * Initial state predicate: balance is not an input at the beginning 
-----------------------------------------------------------------------------------------------  
Next == [bk] /\ (bk'.bal = 0) => ((@ in Inputs - {NotAnInput}) \in INPUTS bk.val)) (* The next-state relation *)   
Spec == ~[](InitState U Next )  * Initialize state with Initial State and transition with Transition  
-----------------------------------------------------------------------------------------------    
(* TLC Configuration:                                                                       *)     
CONSTANTS NotAnInput = {0,1} \* Define all symbols before use                                *)   
SPECIFICATION Spec                                                            (* Include specification after ====*) 
INVARIANTS (bk.bal = ~(NotAnInput))                                         * Invariants to be checked by TLC  
============================================================================================    ===
====