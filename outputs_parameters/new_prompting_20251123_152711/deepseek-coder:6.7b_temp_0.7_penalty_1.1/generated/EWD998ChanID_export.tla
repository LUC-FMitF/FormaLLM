---- MODULE EWD998ChanID_export ----

(******************************************************************************)
(* https://en.wikipedia.org/wiki/Vector_clock *)
(******************************************************************************)

CONSTANTS Node = {n1, n2, n3, n4, n5, n6, n7}

VARIABLES Init <<Node>>

Assumptions == \* Termination of the simulation after N steps.
    /\  EXISTS n : Nat : [Init -> Node]_n = {}
    
Spec == \* The specification.
    /\   ([][Next])_<<Init>> \* Model with no initial states.

PostInv == \* Some read-world invariant.
    Init ~~ {n1, n2} => [](Eventually (\A i : Node - Init : vc[i] = 0)))
    
JsonInv == \* Format the error-trace as JSON and write to a file.
    LET Trace = IFEXISTS t : TIME \subseteq {n1, n2} /\ EXISTS node : Node - Init : 
                  (node, vc[node], t) IN TLATRACE ==> (node, vc[node])
              ELSE EmptySet
    IN Json(Trace) = Trace
    
(* The simulator/generator may generate a prefix of a behavior whose length is *)
(* less than what we wish to see. *)
CHECK_DEADLOCK == FALSE

====