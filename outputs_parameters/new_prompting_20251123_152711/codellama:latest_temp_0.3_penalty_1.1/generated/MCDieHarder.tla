---- MODULE MCDieHarder ----

(**************************************************************************)
(* The following definitions duplicate the original Die Hard problem.     *)
(**************************************************************************)

CONSTANTS Goal     \* The goal state.
    == 4
Jug      \* The capacity of the jugs.
    <- MCJug
Capacity \* The capacity of the container.
    <- MCCapacity

VARIABLES   c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20
          \* The capacity of each jug.
          
Init == \* The initial predicate.
    /\ c1 = 0
    /\ c2 = 0
    /\ c3 = 0
    /\ c4 = 0
    /\ c5 = 0
    /\ c6 = 0
    /\ c7 = 0
    /\ c8 = 0
    /\ c9 = 0
    /\ c10 = 0
    /\ c11 = 0
    /\ c12 = 0
    /\ c13 = 0
    /\ c14 = 0
    /\ c15 = 0
    /\ c16 = 0
    /\ c17 = 0
    /\ c18 = 0
    /\ c19 = 0
    /\ c20 = 0
    
Next == \* The next-state relation.
    \/ [c1' |-> c1 + 1]
    \/ [c2' |-> c2 + 1]
    \/ [c3' |-> c3 + 1]
    \/ [c4' |-> c4 + 1]
    \/ [c5' |-> c5 + 1]
    \/ [c6' |-> c6 + 1]
    \/ [c7' |-> c7 + 1]
    \/ [c8' |-> c8 + 1]
    \/ [c9' |-> c9 + 1]
    \/ [c10' |-> c10 + 1]
    \/ [c11' |-> c11 + 1]
    \/ [c12' |-> c12 + 1]
    \/ [c13' |-> c13 + 1]
    \/ [c14' |-> c14 + 1]
    \/ [c15' |-> c15 + 1]
    \/ [c16' |-> c16 + 1]
    \/ [c17' |-> c17 + 1]
    \/ [c18' |-> c18 + 1]
    \/ [c19' |-> c19 + 1]
    \/ [c20' |-> c20 + 1]
    
Spec == \* Initialize state with Init and transition with Next.
    Init /\ [][Next]_<<c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20>>
=============================================================================
====