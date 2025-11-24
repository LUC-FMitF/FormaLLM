---- MODULE Alternate ----

(*****************************************************************************)
(* Generated at Sat Oct 31 02:58:46 PDT 2009                                *)
(* This specifies a system that alternately performs two actions, which    *)
(* for now I will call A_0 and A_1.  It uses a variable v whose value      *)
(* alternates between 0 and 1, performing an A_0 action when v changes     *)
(* from 0 to 1, and an A_1 action when v changes from 1 to 0.              *)
(*****************************************************************************)
CONSTANTS   XInit,    \* The initial predicate.
            XAct      \* An action operator.
VARIABLES   x        \* The part of the state that is changed by the actions.
INITIAL     /\ x = 0                              \* Initial value for x.
TRANSITION  (v, x) -> [XInit(x), XAct(v, x, v')] \* Actions change the value of x.
FINAL       TRUE                                 \* The system is in a valid state if it reaches this line.
-----------------------------------------------------------------------------
Next ==   \* The next-state relation.
    /\ [](XInit(x) /\ (v = 0 => v' = 1))
    \/ \E v : XAct(v, x, v')
        
Spec == \* Initialize state with Init and transition with Next.
    [][Next]_<<x>>
-----------------------------------------------------------------------------
THEOREM Spec /\ [](XInit(0) /\ (v = 1 => v' = 0)) => FALSE
=============================================================================
====