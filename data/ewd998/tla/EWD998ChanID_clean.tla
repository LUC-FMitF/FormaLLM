---------------------------- MODULE EWD998ChanID ----------------------------

EXTENDS Integers, Sequences, FiniteSets, Naturals, Utils

Merge(n, r, l) ==
LET max(a, b) == IF a > b THEN a ELSE b
IN [ m \in DOMAIN l |-> IF m = n THEN l[m] + 1 ELSE max(r[m], l[m]) ]

CONSTANT Node
ASSUME IsFiniteSet(Node) /\ Node # {}

N == Cardinality(Node)

Initiator == CHOOSE n \in Node : TRUE

RingOfNodes ==
CHOOSE r \in [ Node -> Node ]: IsSimpleCycle(Node, r)

nat2node[ i \in 0..N-1 ] ==
IF i = 0 THEN Initiator ELSE AntiFunction(RingOfNodes)[nat2node[i-1]]

node2nat ==
AntiFunction(nat2node)

Color == {"white", "black"}

VARIABLES
active,
color,
counter,
inbox,
clock,
passes

vars == <<active, color, counter, inbox, clock, passes>>

terminated ==
\A n \in Node :
/\ ~ active[n]

/\ [m \in Node |->
Len(SelectSeq(inbox[m],
LAMBDA msg: msg.type = "pl")) ][n] = 0

terminationDetected ==
/\ \E j \in 1..Len(inbox[Initiator]):
/\ inbox[Initiator][j].type = "tok"
/\ inbox[Initiator][j].color = "white"
/\ inbox[Initiator][j].q + counter[Initiator] = 0
/\ color[Initiator] = "white"
/\ ~ active[Initiator]

------------------------------------------------------------------------------

Init ==

/\ clock = [ n \in Node |-> IF n = Initiator
THEN [ m \in Node |-> IF m = Initiator THEN 1 ELSE 0 ]
ELSE [ m \in Node |-> 0 ] ]

/\ counter = [n \in Node |-> 0]

/\ inbox = [n \in Node |-> IF n = nat2node[N-2]
THEN << [type |-> "tok", q |-> 0, color |-> "black", vc |-> clock[n] ] >>
ELSE <<>>]

/\ active \in [Node -> {FALSE}]
/\ color \in [Node -> {"black"}]
/\ passes = IF terminated THEN 0 ELSE -1

InitiateProbe(n) ==
/\ n = Initiator

/\ \E j \in 1..Len(inbox[Initiator]):

/\ inbox[Initiator][j].type = "tok"
/\ clock' = [clock EXCEPT ![n] = Merge(n, inbox[n][j].vc, @)]
/\
\/ inbox[Initiator][j].color = "black"
\/ color[Initiator] = "black"

\/ counter[Initiator] + inbox[Initiator][j].q # 0
/\ inbox' = [inbox EXCEPT ![RingOfNodes[Initiator]] = Append(@,
[type |-> "tok", q |-> 0,

color |-> "white", vc |-> clock[n]']),
![Initiator] = RemoveAt(@, j) ]

/\ color' = [ color EXCEPT ![Initiator] = "white" ]

/\ UNCHANGED <<active, counter>>
/\ passes' = IF passes >= 0 THEN passes + 1 ELSE passes

PassToken(n) ==
/\ n # Initiator

/\ ~ active[n]
/\ \E j \in 1..Len(inbox[n]) :
/\ inbox[n][j].type = "tok"
/\ clock' = [clock EXCEPT ![n] = Merge(n, inbox[n][j].vc, @)]

/\ LET tkn == inbox[n][j]
IN  inbox' = [inbox EXCEPT ![RingOfNodes[n]] =
Append(@, [tkn EXCEPT !.q = tkn.q + counter[n],
!.color = IF color[n] = "black"
THEN "black"
ELSE tkn.color,
!.vc = clock[n]' ]),
![n] = RemoveAt(@, j) ]

/\ color' = [ color EXCEPT ![n] = "white" ]

/\ UNCHANGED <<active, counter>>
/\ passes' = IF passes >= 0 THEN passes + 1 ELSE passes

System(n) == \/ InitiateProbe(n)
\/ PassToken(n)

-----------------------------------------------------------------------------

SendMsg(n) ==

/\ active[n]

/\ counter' = [counter EXCEPT ![n] = @ + 1]
/\ clock' = [ clock EXCEPT ![n][n] = @ + 1 ]

/\ \E j \in Node \ {n} :

/\ inbox' = [inbox EXCEPT ![j] = Append(@, [type |-> "pl", src |-> n, vc |-> clock[n]' ] ) ]

/\ UNCHANGED <<active, color, passes>>

RecvMsg(n) ==

/\ counter' = [counter EXCEPT ![n] = @ - 1]

/\ color' = [ color EXCEPT ![n] = "black" ]

/\ active' = [ active EXCEPT ![n] = TRUE ]

/\ \E j \in 1..Len(inbox[n]) :
/\ inbox[n][j].type = "pl"
/\ inbox' = [inbox EXCEPT ![n] = RemoveAt(@, j) ]
/\ clock' = [ clock EXCEPT ![n] = Merge(n, inbox[n][j].vc, @) ]
/\ UNCHANGED passes

Deactivate(n) ==
/\ active[n]
/\ active' = [active EXCEPT ![n] = FALSE]
/\ clock' = [ clock EXCEPT ![n][n] = @ + 1 ]
/\ UNCHANGED <<color, inbox, counter>>
/\ passes' = IF terminated' THEN 0 ELSE passes

Environment(n) ==
\/ SendMsg(n)
\/ RecvMsg(n)
\/ Deactivate(n)

-----------------------------------------------------------------------------

Next(n) ==
System(n) \/ Environment(n)

Spec == Init /\ [][\E n \in Node: Next(n)]_vars
/\ \A n \in Node: WF_vars(System(n))

Max3TokenRounds ==

passes <= 3 * N

THEOREM Spec => []Max3TokenRounds

-----------------------------------------------------------------------------

a \prec b ==

node2nat[a] < node2nat[b]

a ++ b ==

LET i == node2nat[a]
j == node2nat[b]
IN { nat2node[k] : k \in i..j }

Node2Nat(fcn) ==
[ i \in 0..N-1 |->  fcn[nat2node[i]] ]

MapSeq(seq, Op(_)) ==
LET F[i \in 0..Len(seq)] == IF i = 0
THEN << >>
ELSE Append(F[i - 1], Op(seq[i]))
IN F[Len(seq)]

EWD998ChanInbox ==

[n \in DOMAIN inbox |->
MapSeq(inbox[n],
LAMBDA m:
IF m.type = "pl"
THEN [type |-> "pl"]
ELSE IF m.type = "tok"
THEN [type |-> "tok", q |-> m.q, color |-> m.color]
ELSE m)
]

EWD998Chan == INSTANCE EWD998Chan WITH active <- Node2Nat(active),
color <- Node2Nat(color),
counter <- Node2Nat(counter),
inbox <- Node2Nat(EWD998ChanInbox)

EWD998ChanStateConstraint == EWD998Chan!StateConstraint
EWD998ChanSpec == EWD998Chan!Spec

THEOREM Spec => EWD998ChanSpec

EWD998Safe == EWD998Chan!EWD998!TD!Safe
EWD998Live == EWD998Chan!EWD998!TD!Live

THEOREM Spec => EWD998Safe /\ EWD998Live
-----------------------------------------------------------------------------

View ==
<<active, color, counter, EWD998ChanInbox, passes>>

=============================================================================
