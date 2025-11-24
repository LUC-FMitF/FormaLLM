---- MODULE MCDieHarder ----

(**************************************************************************)
(* The following definitions duplicate the original Die Hard problem.     *)
(**************************************************************************)

CONSTANTS   Capacity,      \* The capacity of a jug.                        *)
            Goal,          \* The goal to be achieved by refilling         *)
            Jug           \* A jug's current level.                       *)
VARIABLES   filler,       \* Filler is the process that moves water       *)
            fillerState  \* from the source to the target.                *)
-----------------------------------------------------------------------------
MCJug ==    \* Choose something to represent an unknown or unconstrained value.
    CHOOSE v : v \in Nat
    
MCCapacity(j) ==   \* The capacity of a jug j is its maximum level minus its minimum level.
    MAX((1 + j), Capacity - (1 + j))
        
Init ==                            *)
    /\ filler = {}               *  Initially, there are no processes     *)
    /\ fillerState \in {0, 2}   *  moving water in the system.           *)
-----------------------------------------------------------------------------
Next ==                             *)
    \/ (filler' = Union(filler, {1}))  *  A new process starts to move     *)
        /\ fillerState' = 0         *  from the source to the target.      *)
    \/ (filler' = Difference(filler, {1}))   *  An existing process stops  *)
        /\ fillerState' = 2           *  moving water in the system.       *)
-----------------------------------------------------------------------------
Spec ==                             *)
    Init /\ [][Next]_<<filler, fillerState>>      *  The specification is   *)
     \* that initially there are no processes  *)
     \* moving water in the system and at any  *)
     \* moment only one process can move      *)
     \* water from the source to the target.   *)
-----------------------------------------------------------------------------
INVARIANTS TypeOK NotSolved
====