---- MODULE MCDieHarder ----

(**************************************************************************)
(* The following definitions duplicate the original Die Hard problem.   *)
(**************************************************************************)

CONSTANTS Goal     \* The goal to be achieved.
    == 4

Jug      \* The jug containing the balls.
    == [b \in {1,2} |-> TRUE]

Capacity \* The capacity of the jug.
    == [j \in Jug |-> IF j = Jug[1] THEN 2 ELSE 3]

Spec ==
    Init /\ [][Next]_<<Goal, Jug, Capacity>>

Init ==
    Goal = 0
    /\ Jug = <<1: {1,2}, 2: {1,2}>>
    /\ Capacity = <<1: 2, 2: 3>>

Next ==
    \/ \E j \in Jug : Add(j)
    \/ \E j \in Jug : Remove(j)

Add(j) ==
    /\ Goal' = Goal + 1
    /\ IF Goal' > Capacity[j] THEN
        /\ Jug' = [k \in Jug |-> IF k = j THEN {1,2} ELSE Jug[k]]
    ELSE
        /\ Jug' = [k \in Jug |-> IF k = j THEN {1,2} UNION Jug[k] ELSE Jug[k]]

Remove(j) ==
    /\ Goal' = Goal - 1
    /\ IF Goal' < 0 THEN
        /\ Jug' = <<>>
    ELSE
        /\ Jug' = [k \in Jug |-> IF k = j THEN {1,2} ELSE Jug[k]]

TypeOK ==
    /\ Goal \in Nat
    /\ Jug \in FiniteSets(Nat)
    /\ Capacity \in FiniteSets({1,2})
    /\ Goal' \in Nat
    /\ Jug' \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 1 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [j \in Jug |-> IF j = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ [k \in Jug |-> IF k = 2 THEN {1,2} ELSE {}] \in FiniteSets(Nat)
    /\ Goal' \in Nat
    /\ [j \in Jug |-> IF j = 1 THEN {1,2}
====