---- MODULE MCDieHarder ----

(**************************************************************************)
(* The following definitions duplicate the original Die Hard problem.     *)
(**************************************************************************)

CONSTANTS Goal, Jug, Capacity  \* Constant parameters for the model.

VARIABLES x                    \* A variable to represent the current state of the system.

Init ==                        \* The initial predicate.
/\ x = EmptyZSeq                \* The set of all zero-indexed sequences of elements in S with length n.
/\ Goal > 0 /\ Capacity >= 1     \* The capacity must be greater than or equal to one, and the goal must be positive.

Next ==                        \* The next-state relation.
\/ x = <<>> : Goal <= 0         \* If we have emptied all of our ammunition, then there is no need for further exploration.
\/ x = Rotation(x, 1) : Capacity > 0 /\ Goal > 0   \* Otherwise, rotate the sequence by one index to simulate a shot being fired.

Spec ==                        \* The specification of the model.
Init /\ [][Next]_<<x>>         \* Initialize state with Init and transition with Next.
=============================================================================
====