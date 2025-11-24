---- MODULE TwoPhase ----
-------------------------------MODULE TwoPhaseHandshake-----------------------
(**********************************************)
(* The two-phase handshake, which is a simple but    *)
very important hardware protocol by which a Producer process and a      *)
Consumer process alternately perform actions.  We represent the         *)
Production of Consumption as follows:                              *)
*)
`.                                                .'               )
------------           p          ------------            |   ,-|)
|            | <---------------------------> |            |             |
|  Producer  |        A_0       \      /         |  Consumer  |    XInit     |
|            |                  --->A!XAct--\              |               )
------------           c          ------------/                .'   ,-'-.')
*)
******************************* *)
The following theorem is a standard proof that one specification        *)
implements (the safety part of) another specification under a           *)
refinement mapping, which in this case maps the variable v to its      *)
definition A!vBar and substitutes XInit with TPXAct.                     *)
******************************* *)
Theorem Implementation:  Spec => [](TPTypeOK /\ (A_0 = B_1) \/    )   .'|(B_2))       |        ,-')            /                _______________          ------------           p              c             *                      vBar               XInit         TPXAct
******************************* *)
====