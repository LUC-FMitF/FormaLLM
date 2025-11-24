---- MODULE EWD998ChanID_export ----

(******************************************************************************)
(* This module describes a distributed system with vector clocks. Each node    *)
(* maintains a local vector clock, and the specification checks if termination   *)
(* is detected within N steps (arbitrarily chosen as 10 in this case).         *)
(******************************************************************************)

CONSTANTS Node = {n1, n2, n3, n4, n5, n6, n7}

VARIABLES Clock == [Node -> <>] \* Each node's vector clock is initially empty.

ASSIGNABLE 
    Tick[n](c) == IF c[n] = {} THEN {n} ELSE IF c[n] = {<>} THEN c EXCEPT [n] = {2} ELSE c

\* The initial state is a few nodes with their clocks ticked.
INITIALISATION 
    MCInit == \E n \in Node : Clock[n] = Tick[n](Clock[n])

SPECIFICATION Spec == [<>] /\ (\E n \in Node : F"Clock[n] = {3}")

INVARIANT PostInv == LET N = 10 IN \A n \in Node : Clock[n] \subseteq {0, 1, 2} UNION {<>}

\* The simulator/generator may generate a prefix of a behavior whose length is
\* less than what we wish to see.
CHECK_DEADLOCK FALSE
===============================================================================
====

(* TLC Configuration *)
CONSTANTS
    Node = {n1, n2, n3, n4, n5, n6, n7}
    Init <- MCInit \* Fewer initial states to speed up startup.

SPECIFICATION
    Spec

INVARIANT 
    PostInv

\* The simulator/generator may generate a prefix of a behavior whose length is
\* less than what we wish to see.
CHECK_DEADLOCK 
    FALSE
====