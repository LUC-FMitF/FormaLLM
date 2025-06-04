------------------------------- MODULE TLAPS --------------------------------

SimpleArithmetic == TRUE

SMT == TRUE
SMTT(X) == TRUE

CVC3 == TRUE
CVC3T(X) == TRUE

CVC4 == TRUE
CVC4T(X) == TRUE

Yices == TRUE
YicesT(X) == TRUE

veriT == TRUE
veriTT(X) == TRUE

Z3 == TRUE
Z3T(X) == TRUE

Spass == TRUE
SpassT(X) == TRUE

LS4 == TRUE
LS4T(X) == TRUE
PTL == TRUE

Zenon == TRUE
ZenonT(X) == TRUE

Isa == TRUE
IsaT(X) ==  TRUE
IsaM(X) ==  TRUE
IsaMT(X,Y) ==  TRUE

IsaWithSetExtensionality == TRUE

THEOREM SetExtensionality == \A S,T : (\A x : x \in S <=> x \in T) => S = T
OBVIOUS

THEOREM NoSetContainsEverything == \A S : \E x : x \notin S
OBVIOUS
-----------------------------------------------------------------------------

SlowZenon == TRUE
SlowerZenon == TRUE
VerySlowZenon == TRUE
SlowestZenon == TRUE

Auto == TRUE
SlowAuto == TRUE
SlowerAuto == TRUE
SlowestAuto == TRUE

Force == TRUE
SlowForce == TRUE
SlowerForce == TRUE
SlowestForce == TRUE

SimplifyAndSolve        == TRUE

SlowSimplifyAndSolve    == TRUE

SlowerSimplifyAndSolve  == TRUE

SlowestSimplifyAndSolve == TRUE

Simplification == TRUE
SlowSimplification == TRUE

SlowerSimplification  == TRUE

SlowestSimplification == TRUE

Blast == TRUE
SlowBlast == TRUE
SlowerBlast == TRUE
SlowestBlast == TRUE

AutoBlast == TRUE

AllProvers == TRUE
AllProversT(X) == TRUE

AllSMT == TRUE
AllSMTT(X) == TRUE

AllIsa == TRUE
AllIsaT(X) == TRUE

ExpandENABLED == TRUE
ExpandCdot == TRUE
AutoUSE == TRUE
Lambdify == TRUE
ENABLEDaxioms == TRUE
ENABLEDrewrites == TRUE
ENABLEDrules == TRUE
LevelComparison == TRUE

EnabledWrapper(Op(_)) == FALSE
CdotWrapper(Op(_)) == FALSE

Trivial == TRUE

=============================================================================

The material below is obsolete: the TLA proof rules below are superseded by
the PTL decision procedure, and their formulation is unsound for the semantics
of temporal reasoning that TLAPS adopts.

----------------------------------------------------------------------------

THEOREM RuleTLA1 == ASSUME STATE P, STATE f,
P /\ (f' = f) => P'
PROVE  []P <=> P /\ [][P => P']_f

THEOREM RuleTLA2 == ASSUME STATE P, STATE Q, STATE f, STATE g,
ACTION A, ACTION B,
P /\ [A]_f => Q /\ [B]_g
PROVE  []P /\ [][A]_f => []Q /\ [][B]_g

THEOREM RuleINV1 == ASSUME STATE I, STATE F,  ACTION N,
I /\ [N]_F => I'
PROVE  I /\ [][N]_F => []I

THEOREM RuleINV2 == ASSUME STATE I, STATE f, ACTION N
PROVE  []I => ([][N]_f <=> [][N /\ I /\ I']_f)

THEOREM RuleWF1 == ASSUME STATE P, STATE Q, STATE f, ACTION N, ACTION A,
P /\ [N]_f => (P' \/ Q'),
P /\ <<N /\ A>>_f => Q',
P => ENABLED <<A>>_f
PROVE  [][N]_f /\ WF_f(A) => (P ~> Q)

THEOREM RuleSF1 == ASSUME STATE P, STATE Q, STATE f,
ACTION N, ACTION A, TEMPORAL F,
P /\ [N]_f => (P' \/ Q'),
P /\ <<N /\ A>>_f => Q',
[]P /\ [][N]_f /\ []F => <> ENABLED <<A>>_f
PROVE  [][N]_f /\ SF_f(A) /\ []F => (P ~> Q)

THEOREM RuleWF2 == ASSUME STATE P, STATE f, STATE g, STATE EM,
ACTION A, ACTION B, ACTION N, ACTION M,
TEMPORAL F,
<<N /\ B>>_f => <<M>>_g,
P /\ P' /\ <<N /\ A>>_f /\ EM => B,
P /\ EM => ENABLED A,
[][N /\ ~B]_f /\ WF_f(A) /\ []F /\ <>[]EM => <>[]P
PROVE  [][N]_f /\ WF_f(A) /\ []F => []<><<M>>_g \/ []<>(~EM)

THEOREM RuleSF2 == ASSUME STATE P, STATE f, STATE g, STATE EM,
ACTION A, ACTION B, ACTION N, ACTION M,
TEMPORAL F,
<<N /\ B>>_f => <<M>>_g,
P /\ P' /\ <<N /\ A>>_f /\ EM => B,
P /\ EM => ENABLED A,
[][N /\ ~B]_f /\ SF_f(A) /\ []F /\ []<>EM => <>[]P
PROVE  [][N]_f /\ SF_f(A) /\ []F => []<><<M>>_g \/ <>[](~EM)

THEOREM RuleInvImplication ==
ASSUME STATE F, STATE G,
F => G
PROVE  []F => []G
PROOF OMITTED

THEOREM RuleStepSimulation ==
ASSUME STATE I, STATE f, STATE g,
ACTION M, ACTION N,
I /\ I' /\ [M]_f => [N]_g
PROVE  []I /\ [][M]_f => [][N]_g
PROOF OMITTED

PropositionalTemporalLogic == TRUE
=============================================================================
