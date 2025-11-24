---- MODULE Alternate ----
--------------------------------------------------------------------------------
(* This specifies a system that alternately performs two actions, which    *)
(* for now I will call A_0 and A_1.  It uses a variable v whose value      *)
(* alternates between 0 and 1, performing an A_0 action when v changes     *)
(* from 0 to 1, and an A_1 action when v changes from 1 to 0.              *)
**************************************************************************

CONSTANTS   Philosopher,  \* The set of all philosophers.
            Fork,        \* The set of all forks.
            Eat,         \* The set of all eating actions.
            Think,       \* The set of all thinking actions.
            EatTime,     \* The set of all eating times.
            ThinkTime,   \* The set of all thinking times.
            Time         \* The set of all times.
VARIABLES   v,           \* The variable representing the alternating action.
            x            \* The variable representing the part of the state that is changed by the A_0 and A_1 actions.
            Forks,       \* The set of all forks.
            State        \* The state variable.
--------------------------------------------------------------------------------
Init == \* The initial predicate.
    /\ v \in {0,1}   \* The variable representing the alternating action.
    /\ x \in Fork    \* The variable representing the part of the state that is changed by the A_0 and A_1 actions.
    /\ Forks = {f | f \in Fork}   \* The set of all forks.
    /\ State = <<>>   \* The initial state.
    
--------------------------------------------------------------------------------
Next == \* The transition predicate.
    /\ (State = <<>>) /\ (v = 0)
    ==> (v = 1) /\ (x = Fork) /\ (State = <<>>)
    ==> (v = 0) /\ (x = Fork) /\ (State = <<>>)
    
--------------------------------------------------------------------------------
Eat == \* The predicate that checks whether the philosopher can eat.
    /\ (v = 0)
    ==> (x \in Eat)
    
--------------------------------------------------------------------------------
EatTime == \* The predicate that checks whether the philosopher has the right to eat.
    /\ (v = 0)
    ==> (x \in EatTime)
    
--------------------------------------------------------------------------------
Think == \* The predicate that checks whether the philosopher can think.
    /\ (v = 1)
    ==> (x \in Think)
    
--------------------------------------------------------------------------------
ThinkTime == \* The predicate that checks whether the philosopher has the right to think.
    /\ (v = 1)
    ==> (x \in ThinkTime)
    
--------------------------------------------------------------------------------
INVARIANTS \EE v : Spec                                                         *)
*)

=============================================================================
====