---- MODULE TwoPhase ----
EXTENDS Alternate

CONSTANTS RM = {r1, r2, r3} \* Refinement mappings for Producer and Consumer actions
INVARIANT TPTypeOK == Init \in RM /\ Act \in RM
SPECIFICATION TPSpec == (ProducerHandshake /\ ConsumerHandshake) /\ Inv

(* ------------------------------ *)
(* Definitions for Producer and Consumer actions *)
(* ------------------------------ *)
PROCEDURE ProducerHandshake(x, XInit, XAct) == 
    ([] x = r1 -> A_0[XAct] /\ [] x = r2 -> A_1[XAct])

PROCEDURE ConsumerHandshake(x, XInit, XAct) == 
    ([] x = r1 -<｜begin▁of▁sentence｜> S /\ [] x = r3 -<> XAct) \/ 
    ([] x = r2 <-> A_0[XAct] \/ [] x = r3 -< S \/ [] x = r1 -> A_1[XAct])
    
(* ------------------------------ *)
(* Invariant for the two phase handshake protocol *)
(* ------------------------------ *)
INVARIANT Inv(x, XInit, XAct) == 
    ([] x = r1 -<> S /\ [] x = r2 <-> A_0[XAct] \/ [] x = r3 -<> XAct) \/ 
    ([] x = r1 -< S /\ [] x = r2 -<> A_0[XAct] \/ [] x = r3 <-> XAct)
    
(* ------------------------------ *)
(* Specification for the two phase handshake protocol *)
(* ------------------------------ *)
SPECIFICATION TPSpec(x, XInit, XAct) == 
    ([] x = r1 -<> S /\ [] x = r2 <-> A_0[XAct] \/ [] x = r3 -<> XAct) \/ 
    ([] x = r1 -< S /\ [] x = r2 -<> A_0[XAct] \/ [] x = r3 <-> XAct)
    
=============================================================================
====