---- MODULE EWD998ChanID_export ----

(******************************************************************************)
(* https://en.wikipedia.org/wiki/Vector_clock *)
(******************************************************************************)

EXTENDS TLC

CONSTANTS Node = {n1, n2, n3, n4, n5, n6, n7}

VARIABLES 
    Clock == [n \in Node |-> 0]

ASSUME Init == []Clock_<<Node>>[n \in Node |-> 0]

NEXT(Next) == /\ [n \in Node |-> IF n = Cur THEN Clock[Cur] + 1 ELSE Clock[n]]

INVARIANT PostInv == /\ [n \in Node |-> Clock[n] <= SeqNum]

SPECIFICATION Spec == []Clock_<<Node>>[n \in Node |-> 0]

TLC_CONFIG 
    CONSTANTS Init = {}Clock_<<Node>>[n \in Node |-> 0]
    SPECIFICATION Spec
    INVARIANT PostInv
    CHECK_DEADLOCK FALSE
===============================================================================
====