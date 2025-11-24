---- MODULE TwoPhase ----

(***************************************************************************)
(* This module specifies the two-phase handshake, which is a simple but     *)
(* very important hardware protocol by which a Producer process and a       *)
(* Consumer process alternately perform actions. The system is pictured as follows:                               *)
(* ------------           p          ------------                       *)
(* |            | -----------------> |            |                      *)
(* | Producer  |                    |  Consumer  |  .                    *)
(* |            |<------------------ |            |   '                 *)
(* -------------- c          -----------               ''                  *)
*)
(* In the spec, we represent the Producer and Consumer actions in a way that represents A_0 (Produce) as P and A_1(Consume) as C. We then show that this specification implements the Alternate Specification under suitable refinement mapping  *)
***************************************************************************)
LOCAL INSTANCE RMConstants = {r1, r2, r3} (* Refinements for Producer-Consumer actions *)
INSTANCE TPVariables = <<p: P, c: C>>      (* Variable definitions in the module scope *) 

\* Definition of invariants and specification. The invariant is needed to prove that Specification holds at all times.*)
INVARIANT TPTypeOK == (TPVariables /\ p \in {Init, P} /\ c \in {Init, C}) (* Type OK for Two Phase Handshake *) 
SPECIFICATION TPSpec ==  [][p = Init -> XInit]_<<c>>[XAct]((p=P)/\(c=C))   (* Specification of the two phase handshake protocol*)
=============================================================================
(* The following statement imports, for every defined operator D of module Alternate *) 
\* a definition of ATPD to equal the definition of D with vBar substituted for v and parameters x, XInit, and XAct from this module. This is done by using a mapping function MAP_OPERATORS which maps each Operator in Alternate onto its corresponding operator in TwoPhaseHandshake *)
MAP_OPERATORS(Alternate) == <<A: A>> (* Map operators of the alternate specification to their counterparts here. This is done by hand, as it's a one-to-one mapping for our specific case*) 
ATPD (D) ==  MAP_OPERATORS[Alternate](D)(vBar)   (* Definition of ATPD *)
=============================================================================
(* The following theorem states that the specification TPSpec is implemented by substituting a state function vBar for the variable v. This can be proved using standard temporal logic rules*) 
THM_IMPLEMENTATION == [](ATPD /\ (TPVariables = <<p: P, c : C>>)) -> ([XInit]_<<c>>[XAct]((p=P)/\(c=C))) (* Theorem for proving that the specification is implemented *) 
=============================================================================
(* TLC Configuration*)
CONSTANTS RM = {r1, r2, r3}   (* Refinements: r1 - Producer Initiation, r2- Consumer Initiation and r3 - Exchange of Messages *)
INVARIANT TypeOK == (TPVariables /\ p \in {Init, P} /\ c \in {Init, C})  (* Invariant for type checking*)
SPECIFICATION Spec ==  [][p = Init -> XInit]_<<c>>[XAct]((p=P)/\(c=C))   (* The specification to be proved *)
=============================================================================