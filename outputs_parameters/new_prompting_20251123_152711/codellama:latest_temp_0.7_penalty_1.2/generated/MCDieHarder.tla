---- MODULE MCDieHarder ----

(**************************************************************************)
(* The following definitions duplicate the original Die Hard problem. *)
(**************************************************************************)

CONSTANTS Goal     \* Goal is 4 in this example                            *)
      =  4      
VARIABLES Jug, Capacity                        (* JUG and CAPACITY are    *)
         : [0..5] / {0,1}             (* constants for the problem.      *)
CONSTANTS Goal     \* We have set GOAL to 4 in this example                *)
      =  4      
VARIABLES Jug, Capacity                        * JUG and CAPACITY are    *)
         : [0..5] / {0,1}             * constants for the problem.          *)
-----------------------------------------------------------------------------
MCJug == 3 \/ 4     \* Define MCJUG to be the value of Jug in this example*)
                   \* (in other words, it is either 3 or 4).                *)
MCCapacity(j) == IF j = 0 THEN 2 ELSE 5 ENDIF  * Define MCCAPACITY        *)
              : [Jug] / {1} -> [0..5]           * as the Capacity function. *)
                   \* The domain of this function is JUG, and it returns    *)
                   \* either 2 or 5 depending on whether its argument      *)
                   \* is 0 or not (respectively).                          *)
-----------------------------------------------------------------------------
Spec ==                                         * Define the specification*)
       /\ Capacity[Jug] = Goal                * for this problem.           *)
       /\ ( JUG -> ACCEPT )                     \* If we have reached our  *)
      /\\                                          goal, then accept the   *)
        (\E i \in DOMAIN Jug :                    input string.)            *)
         Capacity[i] = Goal /\                       * This is true iff     *)
           JUG \subseteq {0..5}                     * each of its elements*)
              /\\                                      * are in the set    *)
                (1 .. Goal) .                        * which we  *)
                 (\E i : Capacity[i] = Goal).               * defined as   *)
-----------------------------------------------------------------------------
INVARIANTS TypeOK NotSolved
====