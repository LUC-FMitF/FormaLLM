------------------------------ MODULE HanoiSeq ------------------------------
EXTENDS TLC, Sequences, Integers

CONSTANTS A, B, C
VARIABLES towers

ASSUME A \in [1..Len(A) -> Nat]
ASSUME B \in [1..Len(B) -> Nat]
ASSUME C \in [1..Len(C) -> Nat]

Init ==
towers = <<A, B, C>>

CanMove(from, to) ==
/\ from /= to
/\ towers[from] /= <<>>
/\ IF
towers[to] = <<>>
THEN
TRUE
ELSE
Head(towers[from]) < Head(towers[to])

Move(from, to) ==
towers' = [
towers EXCEPT
![from] = Tail(towers[from]),
![to] = <<Head(towers[from])>> \o towers[to]
]

Next ==
\E from, to \in 1..Len(towers):
/\ CanMove(from, to)
/\ Move(from, to)

Range(sequence) ==
{sequence[i]: i \in DOMAIN sequence}

TypeOK ==
/\ DOMAIN towers = 1..3
/\ \A sequence \in Range(towers):
sequence \in [1..Len(sequence) -> Nat]

NoNewElements ==
LET
originalElements ==
UNION {Range(A), Range(B), Range(C)}
towerElements ==
UNION {Range(towers[1]), Range(towers[2]), Range(towers[3])}
IN
towerElements = originalElements

TotalConstant ==
LET
originalTotal ==
Len(A) + Len(B) + Len(C)
towerTotal==
Len(towers[1]) + Len(towers[2]) + Len(towers[3])
IN
towerTotal = originalTotal

NotSolved ==
~(
/\ towers[1] = <<>>
/\ towers[2] = <<>>
/\ towers[3] = [i \in 1..Len(towers[3]) |-> i]
)
=============================================================================
