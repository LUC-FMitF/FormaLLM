---- MODULE MCDieHarder ----

(**************************************************************************)
(* The following definitions duplicate the original Die Hard problem.     *)
(*                                                                        *)
(* To have TLC find a solution, we must tell it what values to use for   *)
(* the constant parameters Jug, Capacity, and Goal.  However, TLC does    *)
(* not allow one to write function-valued expressions in a configuration *)
(* file.  So, we use this module, which extends module DieHarder, to      *)
(* define a function MCCapacity and have the configuration file TLC to     *)
(* substitute MCCapacity for Capacity.  Since we need to know the value of *)
(* Jug to define Capacity (which is a function having Jug as its domain),  *)
(* we also define MCJug and tell TLC to substitute it for Jug.             *)
(**************************************************************************)

MODULE DieHarder

CONSTANTS Goal     =  4
          Jug      <- MCJug
          Capacity <- MCCapacity 

VARIABLES  d, x, y : Nat

Spec ==
  /\ 0 <= x \* y < Capacity[Jug]
  /\ (
    (* Invariant: there is a solution if and only if x + y >= Goal *)
    GOAL(x, y) =
      IF x + y < Goal -> FALSE
      ELSE TRUE
    )
  /\ (
    (* Action: increment the goal by one *)
    IncGoal ==
      [x' |-> x + 1, y' |-> y]
    )
  /\ (
    (* Action: decrement the x value by one *)
    DecX ==
      [x' |-> x - 1, y' |-> y]
    )
  /\ (
    (* Action: decrement the y value by one *)
    DecY ==
      [x' |-> x, y' |-> y - 1]
    )
  /\ (
    (* Action: increment both values by one *)
    IncXy ==
      [x' |-> x + 1, y' |-> y + 1]
    )
  /\ (
    (* Action: decrement both values by one *)
    DecXy ==
      [x' |-> x - 1, y' |-> y - 1]
    )
  /\ (
    (* Precondition for actions: valid move *)
    ValidMove(d) ==
      IF d = IncGoal -> x + y >= Goal
      ELSE IF d = DecX -> x > 0
      ELSE IF d = DecY -> y > 0
      ELSE TRUE
    )
  /\ (
    (* Transition relation: the next state is obtained by applying *)
    (* one of the actions and checking the precondition.            *)
    Next ==
      [
        d' |-> d,
        x' |-> IF ValidMove(d) -> x + Action[d](x, y) ELSE x,
        y' |-> IF ValidMove(d) -> y + Action[d](x, y) ELSE y
      ]
    )

=============================================================================
====