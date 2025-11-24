---- MODULE MCDieHarder ----

(**************************************************************************)
(* The following definitions duplicate the original Die Hard problem.     *)
(**************************************************************************)
CONSTANTS Goal = 4   \* A constant representing a goal state for this    *)
                      (* module, which is used in specifications and       *)
                      (* invariants to ensure that solutions are valid.   *)
VARIABLES Jug     <- MCJug : [1 ..]         * The jugs of the problem  *)
          Capacity <- MCCapacity : [[j \in JUG |-> nat]]    * A function*)
                      (* representing capacity for each jug, where j is   *)
                      (* a variable in Jug and nat represents natural     *)
                      (* numbers. This allows us to use the same module  *)
                      (* multiple times with different values of Capacity.*)
------------------------------ SPECIFICATION ----------------------------    )
Init == \* The initial predicate, which defines a valid starting state   *
        /\ Jug = [1]            \* There is one jug.                */  *)
         /&/ (Capacity[Jug]) > 0)     /* It has positive capacity.      */
------------------------------ INVARIANTS ----------------------------    )
TypeOK ==                   * Type invariant, which ensures that all variables have the right type.*/
        /\ Jug \in [1 ..]         /&/ Capacity[Jug] = nat  /* The jugs are natural numbers and their capacity is a positive integer */)
NotSolved ==                /*** This predicate states whether or not we   *******have found an invalid solution.                      ***/
        /\ \A s : Spec |~ Goal     /&/ (Jug = [1] & Capacity[Jug]) > 0    /* If there is a state that satisfies the goal, then NotSolved must be false */)
------------------------------ SPECIFICATION ----------------------------   )
====