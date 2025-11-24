---- MODULE MCDieHarder ----

(**************************************************************************)
(* The following definitions duplicate the original Die Hard problem.     *)
(**************************************************************************)

CONSTANTS Goal     \* The goal value.
    == 4

Jug      \* The capacity of the jug.
    == 3

Capacity \* The capacity of the container.
    == 5

Spec == \* The specification.
    \/ \E x \in 0..Capacity : \A y \in 0..Capacity :
        (x + y = Goal) \/ (x + y = Capacity - Goal)

Invariants == \* The invariants.
    TypeOK
    NotSolved

TypeOK == \* The type invariant.
    /\ Goal \in Nat
    /\ Jug \in Nat
    /\ Capacity \in Nat
    /\ Goal <= Capacity
    /\ Goal \in 0..Capacity

NotSolved == \* The NotSolved invariant.
    /\ \A x \in 0..Capacity :
        \A y \in 0..Capacity :
            (x + y = Goal) \/ (x + y = Capacity - Goal)

=============================================================================
====