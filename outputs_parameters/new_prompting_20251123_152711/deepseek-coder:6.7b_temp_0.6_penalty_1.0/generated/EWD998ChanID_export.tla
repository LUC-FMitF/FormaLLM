---- MODULE EWD998ChanID_export ----

(***************************************************************************************)
(* Each node maintains a (local) vector clock                                           *)
(* https://en.wikipedia.<｜begin▁of▁sentence｜>.org/wiki/Vector_clock                                      *)
(***************************************************************************************)

CONSTANTS Node = {n1,n2,n3,n4,n5,n6,n7}

VARIABLES
    clock,
    msg,
    received

ASSIGN
    Init == [n ∈ Node |-> 0] /\ [][Node]_<<clock>>,
    Next == [n ∈ Node |-> IF msg[n] /= {} ∧ received[n] = {}
                       THEN ClockUpdate(n)
                       ELSE Clock(n)],
    Clock(n) == IF msg[n] /= {} ∧ received[n] = {}
                THEN clock[n] + 1
                ELSE clock[n],
    ClockUpdate(n) == Max(clock[n], received[n]),
    Spec == [n ∈ Node |-> clock[n] = Max{clock[m] : m ∈ Node}] /\ [][Node]_<<clock>>,
    PostInv == [n ∈ Node |-> clock[n] >= 0],
    JsonInv == <<"vector_clock": {n ∈ Node |-> clock[n]}>>

SPECIFICATION Spec

INVARIANT PostInv

CHECK_DEADLOCK FALSE

=============================================================================
====

TLC_CONFIG CONSTANTS
    Node = {n1,n2,n3,n4,n5,n6,n7}
    Init <- MCInit \* Fewer initial states to speed-up startup.

SPECIFICATION Spec

INVARIANT JsonInv

\* The simulator/generator may generate a prefix of a behavior whose length is
  \* less than what we wish to see.
CHECK_DEADLOCK FALSE

=============================================================================
====

\* Format the error-trace as JSON and write to a file.
FORMAT_ERR_TRACE_AS_JSON

\* Format the error-trace as JSON and ping some web endpoint.
HTTP_POST_ERR_TRACE_AS_JSON
====