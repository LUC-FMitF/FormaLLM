---- MODULE Hanoi ----

(*****************************************************************************)
(* Towers of Hanoi with N towers                                            *)
(*****************************************************************************)
CONSTANTS D, N \* Number of disks and towers respectively
VARIABLES t \* The tower state

Init == (* Initial predicate *)
    /\ DOMAIN t = {0 .. (2^D) - 1}
    /\ FORALL x \in DOMAIN t : Cardinality(x) = D
    /\ UNCHANGED <<t>>

Next == (* Next-state relation *)
    /\ MOVE(t, a, b)
    /\ UNCHANGED <<t>>

Move(s, a, b) == (* Action to move disk from tower 'a' to tower 'b' *)
    LET top \in s[a] & bottom \in s[b],
        newTop \= IF top = 0 THEN 0 ELSE (top - 1),
        newBottom \= IF bottom = (2^D) - 1 THEN (2^D) - 1 ELSE (bottom + 1)
    IN s[a] = newTop /\ s[b] = newBottom

Spec == (* Specification *)
    Init
    /\ WF_REC(t, \x. x INVARIANTS rightTower # 2^N - 1)

Invariant rightTower == (* Invariant: all disks are on the right tower *)
    FORALL x \in DOMAIN t : UNCHANGED <<x>>
====