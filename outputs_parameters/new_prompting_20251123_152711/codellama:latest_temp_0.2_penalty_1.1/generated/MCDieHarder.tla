---- MODULE MCDieHarder ----

(**************************************************************************)
(* The following definitions duplicate the original Die Hard problem.     *)
(**************************************************************************)

CONSTANTS Goal     \* The goal number of bottles to be collected.
    == 4

Jug      \* The capacity of the jugs.
    <- MCJug

Capacity \* The capacity of the jugs.
    <- MCCapacity

Spec == \* The specification.
    Init /\ [][Next]_<<Goal, Jug, Capacity>>

Init == \* The initial predicate.
    Goal = 0 /\ Jug = 0 /\ Capacity = 0

Next == \* The next-state relation.
    \/ \E t \in Nat : Fill(t)
    \/ \E t \in Nat : Empty(t)
    \/ \E t \in Nat : Pour(t)
    \/ \E t \in Nat : Swap(t)

Fill(t) == \* Fills the jugs with water.
    /\ Goal' = Goal + 1
    /\ Jug' = Jug + 1
    /\ Capacity' = Capacity + 1
    
Empty(t) == \* Empties one of the jugs.
    /\ Goal' = Goal - 1
    /\ IF Jug > 0 THEN Jug' = Jug - 1 ELSE Jug' = Jug
    /\ Capacity' = Capacity - 1
    
Pour(t) == \* Pours water from one jug to the other.
    /\ Goal' = Goal + 1
    /\ IF Jug > 0 THEN Jug' = Jug - 1 ELSE Jug' = Jug
    /\ Capacity' = Capacity + 1
    
Swap(t) == \* Swaps the two jugs.
    /\ Goal' = Goal
    /\ IF Jug > 0 THEN Jug' = Jug - 1 ELSE Jug' = Jug
    /\ Capacity' = Capacity

TypeOK == \* Type invariant.
    /\ Goal \in Nat
    /\ Jug \in Nat
    /\ Capacity \in Nat
    
NotSolved == \* Invariant that ensures the problem is not solved.
    /\ Goal > 0

MCJug == \* The capacity of the jugs, defined as a function.
    [j |-> IF j = 1 THEN 3 ELSE 5]

MCCapacity == \* The capacity of the jugs, defined as a function.
    [j |-> IF j = 1 THEN 3 ELSE 5]

=============================================================================
====