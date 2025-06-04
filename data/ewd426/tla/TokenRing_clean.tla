--------------------------------- MODULE TokenRing ---------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS  N, M
ASSUME NAssumption == N \in Nat \ {0}
ASSUME MAssumption == M \in Nat \ {0}

ASSUME NMAssumption == N <= M + 1

Node == 0 .. N-1

VARIABLES
c

vars == << c >>

TypeOK ==
/\ c \in [ Node -> 0 .. M-1 ]
------------------------------------------------------------------------------------

Init ==
/\ c \in [ Node -> 0 .. M-1 ]

CreateToken ==

/\ c [0] = c [N-1]
/\ c' = [ c EXCEPT ![0] = (c[N-1]+ 1) % M ]

PassToken(i) ==

/\ i # 0
/\ c [i] # c [i-1]
/\ c' = [ c EXCEPT ![i] = c[i-1]]

---------------------------------------------------------------------------------------
Next ==
\/ CreateToken
\/ \E i \in Node \ {0} : PassToken(i)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

---------------------------------------------------------------------------------------
UniqueToken ==
\E i \in 0 .. N :
/\ \A j \in 0..i-1: c[j]= c[0]
/\ \A j \in i..N-1: c[j]= (c[0]-1) % M

Stab  == <>[]UniqueToken

---------------------------------------------------------------------------------------

Alias ==
[
counter|-> c,
unique |-> UniqueToken
]

=======================================================================================
