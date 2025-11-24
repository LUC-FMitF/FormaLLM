---- MODULE EWD998ChanID_export ----

(**************************************************************************)
(* c properly initialized                                                 *)
(**************************************************************************)

CONSTANTS
    Node = {n1,n2,n3,n4,n5,n6,n7}
    Init <- MCInit

SPECIFICATION
    Spec

INVARIANT
    \* JsonInv
    PostInv

\* The simulator/generator may generate a prefix of a behavior whose length is
 \* less than what we wish to see.
CHECK_DEADLOCK
    FALSE

=============================================================================
====