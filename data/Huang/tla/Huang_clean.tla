------------------------------ MODULE Huang ------------------------------

EXTENDS Naturals, DyadicRationals, Sequences, SequencesExt, Functions

CONSTANTS Procs, Leader

ASSUME

Leader \in Procs

VARIABLES
active,
weight,
msgs

vars == <<active, weight, msgs>>

RECURSIVE Sum(_,_)
Sum(fun, set) ==
IF set = {} THEN Zero
ELSE LET p == CHOOSE p \in set: TRUE
IN Add(FoldFunction(Add, Zero, fun[p]), Sum(fun, set \ {p}))

TypeOK ==
/\ active \in [ Procs -> BOOLEAN ]
/\ \A p \in Procs :
\A i \in 1..Len(msgs[p]) :
IsDyadicRational(msgs[p][i])
/\ \A p \in Procs : IsDyadicRational(weight[p])

/\ LET M == Sum(msgs, Procs)
IN Add(FoldFunction(Add, Zero, weight), M) = One

----------------------------------------------------------------------------

Init ==

/\ active = [ p \in Procs |-> IF p = Leader THEN TRUE ELSE FALSE ]

/\ weight = [ p \in Procs |-> IF p = Leader THEN One ELSE Zero ]

/\ msgs \in [ Procs -> {<<>>} ]

SendMsg(p) ==
/\ active[p]

/\ \E q \in Procs :
/\ weight' = [weight EXCEPT ![p] = Half(weight[p])]
/\ msgs' = [msgs EXCEPT ![q] = Append(@, weight[p]')]
/\ UNCHANGED <<active>>

RcvMsg(p) ==

\E i \in 1..Len(msgs[p]) :
/\ active' = [active EXCEPT ![p] = TRUE]
/\ weight' = [weight EXCEPT ![p] = Add(@, msgs[p][i])]
/\ msgs' = [msgs EXCEPT ![p] = RemoveAt(@, i)]

Idle(p) ==
/\ active[p]
/\ active' = [active EXCEPT ![p] = FALSE]

/\ msgs' = [msgs EXCEPT ![Leader] = Append(@, weight[p])]
/\ weight' = [weight EXCEPT ![p] = Zero]

----------------------------------------------------------------------------

IdleLdr ==
/\ active[Leader]
/\ active' = [active EXCEPT ![Leader] = FALSE]
/\ UNCHANGED <<weight, msgs>>

RcvLdr ==

\E i \in 1..Len(msgs[Leader]) :
/\ weight' = [weight EXCEPT ![Leader] = Add(@, msgs[Leader][i])]
/\ msgs' = [msgs EXCEPT ![Leader] = RemoveAt(@, i)]
/\ UNCHANGED active

Next ==
\/ \E p \in Procs : SendMsg(p)
\/ \E p \in Procs \ {Leader} : RcvMsg(p) \/ Idle(p)
\/ RcvLdr \/ IdleLdr

Spec ==
/\ Init
/\ [][Next]_vars
/\ WF_vars(RcvLdr)
/\ WF_vars(IdleLdr)
/\ \A p \in Procs \ {Leader}: WF_vars(RcvMsg(p))
/\ \A p \in Procs \ {Leader}: WF_vars(Idle(p))

----------------------------------------------------------------------------
TerminationDetected ==
/\ ~active[Leader]
/\ weight[Leader] = One

Terminated ==
\A p \in Procs :
/\ ~active[p]
/\ msgs[p] = <<>>

Safe ==
[](TerminationDetected => []Terminated)

THEOREM Spec => Safe

Live ==
Terminated ~> TerminationDetected

THEOREM Spec => Live

----------------------------------------------------------------------------

StateConstraint ==

\A p \in Procs : weight[p].den <= 8

Alias ==
[

active |-> {p \in Procs : active[p]},
weights |-> [p \in { q \in Procs: weight[q] # Zero}
|-> PrettyPrint(weight[p])],
msgs |-> [p \in { q \in Procs: msgs[q] # <<>>}
|-> [ i \in 1..Len(msgs[p]) |-> PrettyPrint(msgs[p][i])]]
]

===============================================================================
