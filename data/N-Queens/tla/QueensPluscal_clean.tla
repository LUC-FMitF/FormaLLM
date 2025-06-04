-------------------------- MODULE QueensPluscal -----------------------------
EXTENDS Naturals, Sequences

CONSTANT N
ASSUME N \in Nat \ {0}

Attacks(queens,i,j) ==
\/ queens[i] = queens[j]
\/ queens[i] - queens[j] = i - j
\/ queens[j] - queens[i] = i - j

IsSolution(queens) ==
\A i \in 1 .. Len(queens)-1 : \A j \in i+1 .. Len(queens) :
~ Attacks(queens,i,j)

Solutions == { queens \in [1..N -> 1..N] : IsSolution(queens) }

VARIABLES todo, sols, pc

vars == << todo, sols, pc >>

Init ==
/\ todo = { << >> }
/\ sols = {}
/\ pc = "nxtQ"

nxtQ == /\ pc = "nxtQ"
/\ IF todo # {}
THEN /\ \E queens \in todo:
LET nxtQ == Len(queens) + 1 IN
LET cols == { c \in 1..N : ~ \E i \in 1 .. Len(queens) :
Attacks( Append(queens, c), i, nxtQ ) } IN
LET exts == { Append(queens,c) : c \in cols } IN
IF (nxtQ = N)
THEN /\ todo' = todo \ {queens}
/\ sols' = (sols \union exts)
ELSE /\ todo' = ((todo \ {queens}) \union exts)
/\ sols' = sols
/\ pc' = "nxtQ"
ELSE /\ pc' = "Done"
/\ UNCHANGED << todo, sols >>

Terminating == pc = "Done" /\ UNCHANGED vars

Next == nxtQ
\/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

TypeInvariant ==
/\ todo \in SUBSET Seq(1 .. N) /\ \A s \in todo : Len(s) < N
/\ sols \in SUBSET Seq(1 .. N) /\ \A s \in sols : Len(s) = N

Invariant ==
/\ sols \subseteq Solutions
/\ todo = {} => Solutions \subseteq sols

NoSolutions == sols = {}

Liveness == WF_vars(nxtQ)
LiveSpec == Spec /\ Liveness

=============================================================================
