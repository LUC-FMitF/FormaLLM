----------------------------- MODULE EWD998Chan -----------------------------

EXTENDS Integers, Sequences, FiniteSets, Utils

CONSTANT N
ASSUME NAssumption == N \in Nat \ {0}

Node == 0 .. N-1
Color == {"white", "black"}

VARIABLES
active,
color,
counter,
inbox

vars == <<active, color, counter, inbox>>

TokenMsg == [type : {"tok"}, q : Int, color : Color]
BasicMsg == [type : {"pl"}]
Message == TokenMsg \cup BasicMsg

TypeOK ==
/\ counter \in [Node -> Int]
/\ active \in [Node -> BOOLEAN]
/\ color \in [Node -> Color]
/\ inbox \in [Node -> Seq(Message)]

/\ \E i \in Node : \E j \in 1..Len(inbox[i]): inbox[i][j].type = "tok"
/\ \A i,j \in Node : \A k \in 1 .. Len(inbox[i]) : \A l \in 1 .. Len(inbox[j]) :
inbox[i][k].type = "tok" /\ inbox[j][l].type = "tok"
=> i = j /\ k = l

------------------------------------------------------------------------------

Init ==

/\ counter = [i \in Node |-> 0]

/\ inbox \in { f \in
[ Node -> {<<>>, <<[type |-> "tok", q |-> 0, color |-> "black" ]>> } ] :
Cardinality({ i \in DOMAIN f: f[i] # <<>> }) = 1 }

/\ active \in [Node -> BOOLEAN]
/\ color \in [Node -> Color]

InitiateProbe ==

/\ \E j \in 1..Len(inbox[0]):

/\ inbox[0][j].type = "tok"
/\
\/ inbox[0][j].color = "black"
\/ color[0] = "black"

\/ counter[0] + inbox[0][j].q # 0
/\ inbox' = [inbox EXCEPT ![N-1] = Append(@,
[type |-> "tok", q |-> 0,

color |-> "white"]),
![0] = RemoveAt(@, j) ]

/\ color' = [ color EXCEPT ![0] = "white" ]

/\ UNCHANGED <<active, counter>>

PassToken(i) ==

/\ ~ active[i]
/\ \E j \in 1..Len(inbox[i]) :
/\ inbox[i][j].type = "tok"

/\ LET tkn == inbox[i][j]
IN  inbox' = [inbox EXCEPT ![i-1] =
Append(@, [tkn EXCEPT !.q = tkn.q + counter[i],
!.color = IF color[i] = "black"
THEN "black"
ELSE tkn.color]),
![i] = RemoveAt(@, j) ]

/\ color' = [ color EXCEPT ![i] = "white" ]

/\ UNCHANGED <<active, counter>>

System == \/ InitiateProbe
\/ \E i \in Node \ {0} : PassToken(i)

-----------------------------------------------------------------------------

SendMsg(i) ==

/\ active[i]

/\ counter' = [counter EXCEPT ![i] = @ + 1]

/\ \E j \in Node \ {i} :

/\ inbox' = [inbox EXCEPT ![j] = Append(@, [type |-> "pl" ] ) ]

/\ UNCHANGED <<active, color>>

RecvMsg(i) ==

/\ counter' = [counter EXCEPT ![i] = @ - 1]

/\ color' = [ color EXCEPT ![i] = "black" ]

/\ active' = [ active EXCEPT ![i] = TRUE ]

/\ \E j \in 1..Len(inbox[i]) :
/\ inbox[i][j].type = "pl"
/\ inbox' = [inbox EXCEPT ![i] = RemoveAt(@, j) ]
/\ UNCHANGED <<>>

Deactivate(i) ==
/\ active[i]
/\ active' = [active EXCEPT ![i] = FALSE]
/\ UNCHANGED <<color, inbox, counter>>

Environment == \E i \in Node : SendMsg(i) \/ RecvMsg(i) \/ Deactivate(i)

-----------------------------------------------------------------------------

Next ==
System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------

NumberOfMsg(ibx) ==
Len(SelectSeq(ibx, LAMBDA msg: msg.type = "pl"))

StateConstraint ==
/\ \A i \in DOMAIN inbox : NumberOfMsg(inbox[i]) < 3

/\ \A i \in DOMAIN counter : counter[i] <= 3

-----------------------------------------------------------------------------

tpos ==
CHOOSE i \in Node : \E j \in 1..Len(inbox[i]) : inbox[i][j].type = "tok"

token ==
LET idx == CHOOSE i \in 1 .. Len(inbox[tpos]): inbox[tpos][i].type = "tok"
IN inbox[tpos][idx]

EWD998 == INSTANCE EWD998 WITH token <-
[pos   |-> tpos,
q     |-> token.q,
color |-> token.color],
pending <-

[n \in Node |->
Len(SelectSeq(inbox[n],
LAMBDA msg: msg.type = "pl")) ]

EWD998Spec == EWD998!Spec

THEOREM Spec => EWD998Spec

=============================================================================
