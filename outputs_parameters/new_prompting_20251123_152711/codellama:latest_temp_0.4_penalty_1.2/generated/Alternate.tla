---- MODULE Alternate ----

(***************************************************************************)
(* Generated at Sat Oct 31 02:58:46 PDT 2009                              *)
(***************************************************************************)
CONSTANTS   v,      \* The variable representing the part of the state that is        changed by the A_0 and A_1 actions.
            XInit,  \* The constant operator used to assert that a value has a correct initial value.
            XAct    \* The constant operator used to assert that changing the value of x from xInit to xNext represents an A_i action, for i=0, 1.
VARIABLES   x       \* The part of the state changed by the A_0 and A_1 actions.
-----------------------------------------------------------------------------
Spec ==                                                                    *)
/\ v = 0 /\ XInit(x)     (* Initial value is correct. *)
\/ (v = 0 /\ x' = 2 /\ XAct(0, x, x'))   (* A_0 action changes the state correctly. *)
\/ (v = 1 /\ x' = 3 /\ XAct(1, x, x'))    (* A_1 action changes the state correctly. *)
-----------------------------------------------------------------------------
Theory ==                                                                     *)
/\ [](Spec)
-----------------------------------------------------------------------------
TLCConfig ==                                                                *)
CONSTANTS   v,      \* The variable representing the part of the state that is        changed by the A_0 and A_1 actions.
            XInit,  \* The constant operator used to assert that a value has a correct initial value.
            XAct    \* The constant operator used to assert that changing the value of x from xInit to xNext represents an A_i action, for i=0, 1.
VARIABLES   x       \* The part of the state changed by the A_0 and A_1 actions.
-----------------------------------------------------------------------------
Spec ==                                                                    *)
/\ v = 0 /\ XInit(x)     (* Initial value is correct. *)
\/ (v = 0 /\ x' = 2 /\ XAct(0, x, x'))   (* A_0 action changes the state correctly. *)
\/ (v = 1 /\ x' = 3 /\ XAct(1, x, x'))    (* A_1 action changes the state correctly. *)
-----------------------------------------------------------------------------
Theory ==                                                                     *)
/\ [](Spec)
=============================================================================
====