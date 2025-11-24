---- MODULE MCDieHarder ----

(**************************************************************************)
(* The following definitions duplicate the original Die Hard problem. *)
(**************************************************************************)

CONSTANTS Jug        \* The capacity of a single jug in liters, must be >= 10   *)
                    \* and <= 35.
      Capacity <- {j: j > 9 /\ j < 46}               \* A function mapping each       *)
                                \* jug to its capacity in liters.                     *)
GOAL Goal             \* The goal state, must be >= 10 and <= 35.      *)

Init == <<>>          \* No jars are initially filled with oil.               *)
Next ==              \* At each step of the model checker:                *)
    [][                   * Either a new jar is added to an existing        *)
     ?jug,?cap :            set of jugs and capacity in liters or             *)
      +Jugs(<<>>) = << >>  \* no jars are filled with oil.                       *)
    UNION              \* Or a single jar is emptied if it contains         *)
     [jug] :               enough oil to do so, and all other jugs remain   *)
      +Jugs(<<>>) = << >>  unchanged.                        *)
INVARIANTS TypeOK NotSolved []
-----------------------------------------------------------------------------
\* The empty set of jars is the initial state. * Init == << >> \* At each step, either a new jar    *)
(* is added to an existing set of jugs and capacity in liters or no     *)
(* jars are filled with oil. Or a single jar is emptied if it contains  *)
(* enough oil to do so, and all other jugs remain unchanged.             *)
\* The goal state must be >=10 and <=35. * GOAL Goal \* A set of jars     *)
(\* with their capacity in liters is the initial state.                  *)
(* No jars are initially filled with oil. * Init == << >> \* At each step, either a new jar    *)
(**************************************************************************)
====