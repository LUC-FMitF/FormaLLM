---- MODULE Alternate ----

(***************************************************************************)
(* Generated at Sat Oct 31 02:58:46 PDT 2009                               *)
(***************************************************************************)

CONSTANTS   v,          \* The variable whose value alternates between 0 and 1.
            XInit,      \* A constant operator representing the initial state.
            XAct        \* A constant operator representing an action.
VARIABLES   x           \* The part of the state that is changed by the actions.
----------------------------------------------------------------------------
Spec == \EE v :                                                          *)
    /\ Spec'[v = 0]
    /\ XInit(x)
    /\ Spec'[v = 1]
    /\ XAct(0, x, x')
    /\ Spec'[v = 0]
    /\ XAct(1, x', x'')
    /\ Spec'[v = 1]
    /\ XAct(0, x'', x''')
    ...

Spec' == \EE v :                                                         *)
    /\ Spec'[v = 0]
    /\ XInit(x)
    /\ Spec'[v = 1]
    /\ XAct(0, x, x')
    /\ Spec'[v = 0]
    /\ XAct(1, x', x'')
    ...

TypeOK == \EE v :                                                        *)
    /\ [](v \in {0, 1})
    /\ [](x \in <<>>)
    /\ XInit(x)
    /\ XAct(0, x, x')
    /\ XAct(1, x', x'')
    ...

===============================================================================
====