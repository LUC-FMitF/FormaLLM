---- MODULE MCDieHarder ----

(**************************************************************************)
(* The following definitions duplicate the original Die Hard problem.     *)
(**************************************************************************)

CONSTANTS Goal, Jug, Capacity   \* Constant parameters for the model.

VARIABLES MCCapacity            \* A function having Jug as its domain.
          MCJug                 \* Another function-valued expression.

MCJug == [j \in 0..1 : j = 0 OR j = 2]   \* The value of Jug for the model.
MCCapacity[j] == IF j = 0 THEN 4 ELSEIF j = 2 THEN 3 ELSE 5 ENDIF    \* A function-valued expression defining Capacity.

Spec ==                       \* Specification that describes the problem.
/\ [](Goal > Capacity(MCJug))   \* The goal is greater than capacity for jug MCJug.
\/ \A j \in 0..1 : Goal <= MCCapacity[j]     \* For all values of Jug, Goal must be less than or equal to the corresponding value of Capacity.

INVARIANTS TypeOK NotSolved   \* Invariants that describe what is always true about the model.

NotSolved == /\ [](Goal <= MCCapacity[MCJug])  \* The goal must be greater than capacity for jug MCJug.
             \/ (MCJug = 0 /\ Goal > Capacity(0))   \* If Jug is zero, the goal must be greater than capacity for that value of Jug.
             \/ (MCJug = 2 /\ Goal > Capacity(2))   \* If Jug is two, the goal must be greater than capacity for that value of Jug.
**************************************************************************)
====