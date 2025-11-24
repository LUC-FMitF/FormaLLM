---- MODULE MCDieHarder ----

(**************************************************************************)
(* The following definitions duplicate the original Die Hard problem.     *)
(**************************************************************************)

CONSTANTS Goal, Jug, Capacity  \* Constant parameters for the model.

VARIABLES x                    \* Auxiliary variable to help with proof.

Init ==
/\ (x = 0)                     \* The initial state is a single ball in   *)
                               \* the jug, and Goal balls are needed.      *)

Next ==
\/ [
    x' = x + 1,                \* If we have not yet reached our goal,     *)
    (x < Capacity /\ x' > Jug) \*   add another ball to the jug if it is   *)
                               \*   possible and there are still balls in  *)
                               \*   the original jug.                      *)
\/ [
    x' = x - 1,                \* If we have reached our goal, remove a     *)
    (x > Goal /\ x' < Jug)     \*   ball from the jug if it is possible and*)
]                             \*   there are still balls in the original *)
                               \*   jug.                                  *)

Spec == Init /\ [][Next]_<<x>>    \* The specification states that we start *)
                                \* with a single ball in the jug, and      *)
                                \* eventually reach our goal of four balls.*)

=============================================================================
====