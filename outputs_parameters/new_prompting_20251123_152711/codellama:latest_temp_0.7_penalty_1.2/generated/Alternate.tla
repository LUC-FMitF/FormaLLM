---- MODULE Alternate ----

(*************************************************************************)
(* Generated at Sat Oct 31 02:58:46 PDT 2009 *)

CONSTANTS   v,     \* The variable representing the alternation of actions.
            XInit, \* The constant operator for initializing x.
            XAct      \* The constant operator for performing an action A_i.
VARIABLES  x        \* The part of the state that is changed by the two actions.
INIT v == TRUE    \* Initial value of v is always TRUE.
XInit(x) == FALSE   \* x has a correct initial value, which is FALSE.
-----------------------------------------------------------------------------
A_0 == XAct(0, FALSE, TRUE)  /\ A_1 == XAct(1, TRUE, FALSE)    \* Perform an action A_i if v = i.
x' == x                          \* No change in the state for both actions.
\EE[Spec]_<<v>>                       \* Specification with v hidden.
-----------------------------------------------------------------------------
TLC CONFIGURATION:
CONSTANTS   XInit,      \* The constant operator for initializing x.
            XAct    \* The constant operator for performing an action A_i.
VARIABLES  x          \* The part of the state that is changed by the two actions.
INIT v == TRUE    \* Initial value of v is always TRUE.
XInit(x) == FALSE   \* x has a correct initial value, which is FALSE.
-----------------------------------------------------------------------------
\EE[Spec]_<<v>>                       \* Specification with v hidden.
*************************************************************************)
====