---- MODULE Majority ----
EXTENDS Integer

CONSTANTS Val, Pos, Majority

VARIABLES seq[Pos], cand, lb, j, count, countTotal

ASSUME \* input sequence of values, never changes
    seq IN [Pos -> Val]

Init ==
    /\ j = 0
    /\ cand = seq[0]
    /\ lb = 0
    /\ count = 1
    /\ countTotal = Cardinality {i \in Pos |-> seq[i] = cand}

Next ==
    /\ IF j = Pos - 1
    /\ THEN j = Pos
    /\ ELSE j = j + 1
    /\ IF seq[j] = cand
    /\ THEN /\ count = count + 1
    /\ ELSE /\ count = count - 1
    /\ IF count = Majority
    /\ THEN /\ cand = seq[j]
    /\ /\ lb = count
    /\ /\ countTotal = Cardinality {i \in Pos |-> seq[i] = cand}

Invariant ==
    /\ IF j = Pos
    /\ THEN /\ countTotal = Cardinality {i \in Pos |-> seq[i] = cand}
    /\ /\ countTotal >= Majority
    /\ /\ cand = Max {v \in Val |-> Cardinality {i \in Pos |-> seq[i] = v} }

Spec ==
    Init /\ [](seq[j] = cand) /\ [](countTotal >= Majority) /\ [](cand = Max {v \in Val |-> Cardinality {i \in Pos |-> seq[i] = v} })

TLC Configuration:
CONSTANTS Val = {0, 1}
CONSTANTS Pos = {0, 1, 2}
CONSTANTS Majority = 2
====