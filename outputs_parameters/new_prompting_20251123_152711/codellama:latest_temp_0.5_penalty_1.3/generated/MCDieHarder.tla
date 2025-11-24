---- MODULE MCDieHarder ----

(**************************************************************************)
(* The following definitions duplicate the original Die Hard problem.     *)
(**************************************************************************)
CONSTANTS Goal, Jug              \* The goal and size of each jug.        *)
          Capacity <- [jug |-> 0]   \* Initially no liquid in any jug.      *)
VARIABLES x                       \* To hold the current state.           *)
-----------------------------------------------------------------------------
MCJug(n) ==    \* Choose a value for Jug to use as Capacity.            *)
    1 + n * 2   \/ (3 - n * 4)      \* Select one of three possible values.*)
                                \* that are multiples of four or           *)
                               /\\(5,9).                              *)
MCCapacity ==    \* Define Capacity as a function with Jug as its domain*)
   [jug |-> MCJug]            \* and values between 1..4.                *)
-----------------------------------------------------------------------------
Spec ==     \* The specification of the problem, including              *)
      /\ x =                    \* initial state and goal condition.       *)
        [[Goal >= Capacity[jug]] /\ [Capacity[jug] <= Jug ] |-> TRUE   *)/\TRUE
-----------------------------------------------------------------------------
TypeOK ==     \* The type invariant, ensuring that the types of all      *)
    /\\ (x : SUBSET {(Goal >= Capacity[Jug]),                            \*) variables are correct.  *)
         [Capacity[jug] <= Jug ] |-> BOOLEAN)                *)/\TRUE     )
-----------------------------------------------------------------------------
NotSolved ==    \* The invariant, ensuring that the problem has not been   *)
      /\ Goal >= Capacity[Jug]                       \* solved yet.         *)
=============================================================================