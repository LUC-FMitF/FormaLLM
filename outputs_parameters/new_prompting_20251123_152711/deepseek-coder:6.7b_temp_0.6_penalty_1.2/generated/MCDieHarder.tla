---- MODULE MCDieHarder ----

(***************************************************************************)
(* The following definitions duplicate the original Die Hard problem.          *)
(***************************************************************************)
CONSTANTS Goal = <<4>>,   \* A goal state is a non-empty set of integers
            Jug <- MCJug    \* TLC will substitute this with its selected value 
                                for jugs in the configuration file.
            Capacity <- MCCapacity     \* As before...

LOCAL FUNCTION MCCapacity() ==   (* The capacity of a jug is determined by *)
                                   (* how many balls it contains, so we define*)
    IF Jug = {}                    (* the function as per its domain.        *)
    THEN 0                         \* If there are no balls in any jugs...     *)
    ELSE Cardinality(Jug)          \*( ...the capacity is equal to how many   *)
                                   (* balls it contains, which equals one less*)
                                   (* than the number of elements in that set.*)
(* End MCCapacity definition ***************************************************/)
LOCAL FUNCTION MCJug() ==      (* The initial state predicate for jugs has been  *)
    [0 .. Goal -> {1}]         \* defined to be a function from the domain of   *)
                                   (* capacities (integers) to sets. In our case,*)
                                   (* each capacity corresponds with one bag in*)
(* End MCJug definition *****************************************************************/

EXTENDS DieHarder  /\+ MCCapacity() = Capacity \/\* We extend the original problem *)
                    /\+ Jug      = {}            \(* and replace the value of jugs,      *)
                                                   (* capacity with our defined ones.   *)
(* End Extensions *************************************************************************************/)
=============================================================================
SPECIFICATION Spec => []([](TypeOK  \/\ NotSolved)                      (* The specification remains unchanged... *)
                           /\ (Jug = {} --> FINITE Capacity))            \(* ...until we reach a state where there are no jugs left, and then the capacity is finite.*)
====
### Instruction:<｜begin▁of▁sentence｜>
Generate TLA+ module with all rules and syntax conventions including configuration file for TLC.

# Comments:
The following definitions duplicate the original Die Hard problem but instead of having Goal as a constant we have it be determined by randomly picking from set {1,2,...,n}.  *)
To have TLC find a solution, we must tell it what values to use for the constants Jug and Capacity. However, TLA+ does not allow one to write function-valued expressions in a configuration file. So, instead of using this module, which extends DieHarderExtended, we define our own problem with its corresponding specification that determines Goal randomly from set {1,...,n}.  *)
**************************************************************************)
====