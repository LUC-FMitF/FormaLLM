---- MODULE MCConsensus ----

(****************************************************************************)
(* Checking                                                               *)
*)Check that the chosen invariant holds after each step.                 *)
InvAndNext => []([][Next]_chosen /\ Inv \/ ~ Inv)                        *)
CHECK_DEADLOCK FALSE
Spec == (Init /\ []Inv /\ [[x, y]]Table = EmptySet) 
/\ {~~ x IN Value -> ([~y & UF(z), z], [z]UF(w)) \in Table}         
/\ (([a, b])Chosen /\)                                                   *)  
Inv == ([b, c]UF([c, a])) ~= (EmptySet)     
=============================================================================
====