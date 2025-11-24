---- MODULE TwoPhase ----
(*Generated at Sat Oct 31 03:15:55 PDT 2009*)
This module specifies the two-phase handshake, which is a simple but     *)
very important hardware protocol by which a Producer process and a       *)
Consumer process alternately perform actions, with the Producer going    *)
first. The system is pictured as follows:                               *)
(*`*)                                                                   *)
------------           p           ----------------------------------
|            |  ---------------------> |             |   .               *)
| Producer  |                           Consumer   |                      *)
|           |<------------------------ -      |      '                 *)
-------------          c         -------------------------------------------------
(*)
In the spec, we represent the Producer and Consumer actions as A_0 and A_1. We then show that this specification implements the Alternate               *)
specification under a suitable refinement mapping (substitution for the  v).                                                             *)
(*Inv is the invariant needed for proof*)                                                                                                      *)
(**/)(*We prove that Spec implementation implies the one obtained by substituting state function vBar for variable v. Here,vBar is defined as follows:                                         .*/)
(/
The following statement imports definition of A(!D), which equals to D with (subtituted for v and parameters substitution*) Alternate module  (*A!/(Alt)(*->TLA+*) *) ,such that every operator D in "Alternate" is defined by replacing variable 'v' from this module,by the corresponding definition of 'vBar',with respect to the other variables x and XInit as well.
(*The following theorem provides a standard proof for specification implementations under refinement mappings*) (*(safety part)*)(*->TLA+*) *)  .In realistic examples ,the non temporal leaf proofs would be more structured than one line each (substeps <2>2).  
/)
==== TLC Configuration ====
CONSTANTS RM = {r1, r2, r3} (* Refinement Mapping set defined in the problem *) 
SPECIFICATION Spec(* Specification of Two-Phase Handshake to be proved using TLC*)  
INVARIANT Inv(x) (***The invariant definition for proof***)
===== End Configuration =====