---------------------------- MODULE EWD840_proof ----------------------------

EXTENDS EWD840, TLAPS

LEMMA TypeCorrect == Spec => []TypeOK
<1>1. Init => TypeOK
BY DEF Init, TypeOK, Color
<1>2. TypeOK /\ [Next]_vars => TypeOK'
<2> SUFFICES ASSUME TypeOK,
[Next]_vars
PROVE  TypeOK'
OBVIOUS
<2>. USE NAssumption DEF TypeOK, Node, Color
<2>1. CASE InitiateProbe
BY <2>1 DEF InitiateProbe
<2>2. ASSUME NEW i \in Node \ {0},
PassToken(i)
PROVE  TypeOK'
BY <2>2 DEF PassToken
<2>3. ASSUME NEW i \in Node,
SendMsg(i)
PROVE  TypeOK'
BY <2>3 DEF SendMsg
<2>4. ASSUME NEW i \in Node,
Deactivate(i)
PROVE  TypeOK'
BY <2>4 DEF Deactivate
<2>5. CASE UNCHANGED vars
BY <2>5 DEF vars
<2>. QED
BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Environment, Next, System
<1>. QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM Safety == Spec => []TerminationDetection
<1>1. Init => Inv
BY NAssumption DEF Init, Inv, Node
<1>2. TypeOK /\ Inv /\ [Next]_vars => Inv'
BY NAssumption
DEF TypeOK, Inv, Next, vars, Node, Color,
System, Environment, InitiateProbe, PassToken, SendMsg, Deactivate
<1>3. Inv => TerminationDetection
BY NAssumption DEF Inv, TerminationDetection, terminationDetected, Node
<1>. QED
BY <1>1, <1>2, <1>3, TypeCorrect, PTL DEF Spec

LEMMA Inv => TerminationDetection
<1>1. SUFFICES ASSUME tpos = 0, tcolor = "white",
color[0] = "white", ~ active[0],
Inv
PROVE  \A i \in Node : ~ active[i]
BY <1>1 DEF TerminationDetection, terminationDetected
<1>2. ~ Inv!P2  BY tcolor = "white" DEF Inv
<1>3. ~ Inv!P1  BY <1>1 DEF Inv
<1>. QED
<2>1. Inv!P0  BY Inv, <1>2, <1>3 DEF Inv
<2>.  TAKE i \in Node
<2>3. CASE i = 0  BY <2>1, <1>1, <2>3
<2>4. CASE i \in 1 .. N-1
<3>1. tpos < i  BY tpos=0, <2>4, NAssumption
<3>2. i < N  BY NAssumption, <2>4
<3>. QED  BY <3>1, <3>2, <2>1
<2>. QED  BY <2>3, <2>4 DEF Node

=============================================================================
