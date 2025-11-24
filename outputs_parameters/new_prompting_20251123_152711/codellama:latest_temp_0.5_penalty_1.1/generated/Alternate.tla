---- MODULE Alternate ----

(**************************************************************************)
(* A philosophical spec for a dining philosopher system.                *)
(*                                                                      *)
(* The system alternately performs two actions, which we will call     *)
(* A_0 and A_1.  It uses a variable v whose value alternates between   *)
(* 0 and 1, performing an A_0 action when v changes from 0 to 1, and    *)
(* an A_1 action when v changes from 1 to 0.                            *)
(**************************************************************************)

CONSTANTS   x,      \* The state variable.
            XInit,  \* The initial value of the state variable.
            XAct,   \* The action operator.
            A_0,    \* The first action.
            A_1     \* The second action.
VARIABLES   v       \* The variable that alternates between 0 and 1.

\* The specification.
Spec ==
    /\ v = XInit(x)
    /\ [][A_0]_<<v>>
    /\ [][A_1]_<<v>>

\* The initial predicate.
XInit ==
    \/ x = <<>>
    \/ x = [p |-> 0]

\* The action operator.
XAct ==
    /\ i : INTEGER
    /\ xInit : State
    /\ xNext : State
    /\ A_i : Action
    \/ (v = 0 /\ v' = 1 /\ XAct(i, xInit, xNext) \* Performing A_i changes the value of v from 0 to 1. *)
    [] (v = 1 /\ v' = 0 /\ XAct(i, xInit, xNext) \* Performing A_i changes the value of v from 1 to 0. *)
    [][A_i]_<<xInit>>

\* The first action.
A_0 ==
    /\ p : INTEGER
    \/ (p < Len(x) /\ x[p] = 0 /\ x'[p] = 1)

\* The second action.
A_1 ==
    /\ p : INTEGER
    \/ (p < Len(x) /\ x[p] = 1 /\ x'[p] = 0)

\* The set of all possible states.
State ==
    IF x = <<>>
    THEN {}
    ELSE {
        [p |-> v] : p \in DOMAIN x
    }

\* The set of all possible actions.
Action ==
    {A_0, A_1}

\* The set of all possible transitions.
Transition ==
    IF x = <<>>
    THEN {}
    ELSE {
        [
            p |-> p',
            v  |-> v',
            x' |-> XAct(i, xInit, xNext)
        ] : p \in DOMAIN x /\ p' < Len(x) /\ v \in {0, 1} /\ v' \in {0, 1} /\ x[p] = v /\ x'[p'] = v' /\ XAct(i, xInit, xNext) \* The transition from state x to state x'.
    }

\* The set of all possible initial states.
InitialState ==
    {x} : x \in State

\* The set of all possible final states.
FinalState ==
    IF x = <<>>
    THEN {}
    ELSE {
        [p |-> p'] : p' < Len(x) /\ x[p'] = 0
    }

\* The set of all possible reachable states from a given state.
ReachableState ==
    IF x = <<>>
    THEN {}
    ELSE {
        [p |-> p'] : p' < Len(x) /\ x[p'] = 0
    }

\* The set of all possible unreachable states from a given state.
UnreachableState ==
    IF x = <<>>
    THEN {}
    ELSE {
        [p |-> p'] : p' < Len(x) /\ x[p'] = 1
    }

\* The set of all possible deadlock states.
DeadlockState ==
    IF x = <<>>
    THEN {}
    ELSE {
        [p |-> p'] : p' < Len(x) /\ x[p'] = 0
    }

\* The set of all possible live states.
LiveState ==
    IF x = <<>>
    THEN {}
    ELSE {
        [p |-> p'] : p' < Len(x) /\ x[p'] = 1
    }

\* The set of all possible reachable and live states from a given state.
ReachableLiveState ==
    IF x = <<>>
    THEN {}
    ELSE {
        [p |-> p'] : p' < Len(x) /\ x[p'] = 1
    }

\* The set of all possible unreachable and deadlock states.
UnreachableDeadlockState ==
    IF x = <<>>
    THEN {}
    ELSE {
        [p |-> p'] : p' < Len(x) /\ x[p'] = 0
    }

\* The set of all possible reachable and deadlock states.
ReachableDeadlockState ==
    IF x = <<>>
    THEN {}
    ELSE {
        [p |-> p'] : p' < Len(x) /\ x[p'] = 0
    }

\* The set of all possible unreachable and live states.
UnreachableLiveState ==
    IF x = <<>>
    THEN {}
    ELSE {
        [p |-> p'] : p' < Len(x) /\ x[p'] = 1
    }

\* The set of all possible reachable and live states.
ReachableLiveState ==
    IF x = <<>>
    THEN {}
    ELSE {
        [p |-> p'] : p' < Len(x) /\ x[p'] = 1
    }

\* The set of all possible unreachable and deadlock states.
UnreachableDeadlockState ==
    IF x = <<>>
    THEN {}
    ELSE {
        [p |-> p'] : p' < Len(x) /\ x[p'] = 0
    }

\* The set of all possible reachable and deadlock states.
ReachableDeadlockState ==
    IF x = <<>>
    THEN {}
    ELSE {
        [p |-> p'] : p' < Len(x) /\ x[p'] = 0
    }

\* The set of all possible unreachable and live states.
UnreachableLiveState ==
    IF x = <<>>
    THEN {}
    ELSE {
        [p |-> p'] : p' < Len(x) /\ x[p'] = 1
    }

\* The set of all possible reachable and live states.
ReachableLiveState ==
    IF x = <<>>
    THEN {}
    ELSE {
        [p |-> p'] : p' < Len(x) /\ x[p'] = 1
    }

=============================================================================
====