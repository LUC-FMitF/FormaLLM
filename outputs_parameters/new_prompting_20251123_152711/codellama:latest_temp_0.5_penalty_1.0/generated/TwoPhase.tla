---- MODULE TwoPhase ----
-------------------------------MODULE TwoPhaseHandshake-----------------------
(***************************************************************************)
(* This module specifies the two-phase handshake, which is a simple but    *)
* very important hardware protocol by which a Producer process and a      *)
* Consumer process alternately perform actions, with the Producer going   *)
* first.  The system is pictured as follows:                              *)
(****************************************************************)
CONSTANT RM = {r1, r2, r3}
INVARIANT TPTypeOK
SPECIFICATION TPSpec
====