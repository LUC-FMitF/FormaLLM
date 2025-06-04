---------------------- MODULE TwoPhase -----------------------

EXTENDS Naturals, TLAPS

CONSTANT XInit(_), XAct(_, _, _)

VARIABLE p, c, x

Init == /\ p = 0
/\ c = 0
/\ XInit(x)

ProducerStep == /\ p = c
/\ XAct(0, x, x')
/\ p' = (p + 1) % 2
/\ c' = c

ConsumerStep == /\ p # c
/\ XAct(1, x, x')
/\ c' = (c + 1) % 2
/\ p' = p

Next == ProducerStep \/ ConsumerStep

Spec == Init /\ [][Next]_<<p, c, x>>

Inv == (p \in {0,1}) /\ (c \in {0,1})

vBar == (p + c) % 2

A == INSTANCE Alternate WITH v <- vBar

THEOREM Implementation == Spec => A!Spec
<1>1. Spec => []Inv
<2>1. Init => Inv
BY DEF Init, Inv
<2>2. Inv /\ [Next]_<<p, c, x>> => Inv'
BY Z3 DEF Inv, Next, ProducerStep, ConsumerStep
<2>. QED
BY <2>1, <2>2, PTL DEF Spec
<1>2. QED
<2>1. Init => A!Init
BY Z3 DEF Init, A!Init, vBar
<2>2. Inv /\ [Next]_<<p, c, x>>  => [A!Next]_<<vBar, x>>
BY Z3 DEF Inv, Next, ProducerStep, ConsumerStep, A!Next, vBar
<2>3. []Inv /\ [][Next]_<<p, c, x>>  => [][A!Next]_<<vBar, x>>
BY <2>1, <2>2, PTL
<2>. QED
BY <2>1, <2>3, <1>1, PTL DEF Spec, A!Spec

==============================================================
