---- MODULE MCDieHarder ----

(**************************************************************************)
(* The following definitions duplicate the original Die Hard problem. *)
(**************************************************************************)

CONSTANTS Goal     \* The goal value of the game.
    == 4

Jug      \* The capacity of the jugs.
    <- MCJug

Capacity \* The capacity of the jugs.
    <- MCCapacity

MCJug ==   \* A function that returns the capacity of a jug.
    [jug |-> Cap(jug)]

MCCapacity ==  \* A function that returns the capacity of a jug.
    [jug |-> IF jug = 1 THEN 3 ELSE 5]

Spec == \* The specification.
    Init /\ [][Next]_<<>>

Init == \* The initial predicate.
    ALL j : Jug | Goal > Capacity[j]

Next == \* The next-state relation.
    \/ \E j : Jug | \A s : State | (s = << >> /\ j \in MCJug) =>
        \A s' : State | (s' = << >> /\ j \notin MCJug)

State == \* The set of states.
    [j \in Jug |-> 0..Capacity[j]]

TypeOK == \* Type invariants.
    /\ ALL j : Jug | Goal > Capacity[j]
    /\ ALL s : State | LENGTH(s) <= 2
    /\ ALL s : State | DOMAIN(s) SUBSET {1, 2}
    /\ ALL s : State | (s = << >> ==> EMPTY(DOMAIN(s)))
    /\ ALL s : State | (s = << >> ==> LENGTH(s) = 0)
    /\ ALL s : State | (s \in {<<1,2>>} ==> LENGTH(s) = 2)
    /\ ALL s : State | (s \in {<<1,2>>} ==> DOMAIN(s) SUBSET {1, 2})
    /\ ALL s : State | (s \in {<<1,2>>} ==> EMPTY(DOMAIN(s)))

NotSolved == \* The NotSolved invariant.
    /\ ALL j : Jug | Goal > Capacity[j]
    /\ LENGTH(<< >>) = 0
    /\ (<< >> \in {<<1,2>>} <=> FALSE)

=============================================================================
====