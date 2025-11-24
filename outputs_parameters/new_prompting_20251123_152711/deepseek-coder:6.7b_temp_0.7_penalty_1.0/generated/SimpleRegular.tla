---- MODULE SimpleRegular ----
(***************************************************************************)
(* This module implements a simple algorithm using regular registers.       *)
(* See the comments below for more details.                                   *)
(***************************************************************************)

CONSTANT N == 8

VARIABLES x == [i \in 0..(N-1) |-> {0}], y == [i \in 0..(N-1) |-> {0}]

PROCESSES proc == [i \in 0..(N-1)]

ACTIONS a1, a2, b ==
  a1: x[self] := {0, 1}
  a2: x[self] := {1}
  b: with (v \in x[(self-1) % N]) {y[self] := v}

\* Inv is the same as in module Simple

\* PCorrect is the same as in module Simple

\* TypeOK is the same as in module Simple

=============================================================================
====

--algorithm Spec {
--vars == x /\ y /\ self
--init == \A i \in 0..(N-1) [x[i] = {0} /\ y[i] = {0}]
--trans == [a1]_i /\ [a2]_i /\ [b]_i
--inv == PCorrect /\ TypeOK /\ Inv
}
====

==== CONSTANTS N = 8
====