---- MODULE MCConsensus ----

(**************************************************************************)
(* Checking                                                                *)
*)
Inv /\ [Next]_chosen => Inv'                                        (* *)
*)
which is equivalent to checking                                          *)
*)
Inv /\ [][Next]_chosen => []Inv                                      (* *)
*)
which asserts that Inv is an invariant of the spec                       *)
*)
Inv /\ []Spec                                                          (* *)
**************************************************************************)

(* TLC Configuration: *)
CONSTANTS Value = {"a", "b", "c"}
SPECIFICATION ISpec 
INVARIANT Inv
CHECK_DEADLOCK FALSE
=============================================================================
====
### Instruction:<｜begin▁of▁sentence｜>
I need help writing a transition system for an elevator. The specifics of the elevators are as follows:

1) An elevator can have one of three states: idle, up, down.
2) There's a button on each floor to call the elevator. This will make it move in that direction if possible. If not, the elevator remains idle. 
3) The elevator should stop at every floor when called and open its doors. It can then be used again once closed.
4) An elevator can only go from one state to another if it's currently idle, or if it's going in a direction that matches the call button pressed. 
5) If an elevator is moving in one direction but reaches a floor with a different directional call button press, it should stop at that floor and open its doors.
6) An up-call takes precedence over down-calls if there are both present on a given floor. Down calls are considered only after an up call has been made to the same floor. 
7) If all buttons of one direction have been pressed, the elevator should stop at every floor and open its doors before making any further move.
8) Elevators do not wait for other floors once they've opened their doors. They can be used again as soon as someone closes the doors. 

What would be a good way to model this in TLA+? I'm looking for something that could help me understand how you would go about designing and implementing such a system?

Thanks for any insights or suggestions on how to approach this problem using TLA+ tools.
====