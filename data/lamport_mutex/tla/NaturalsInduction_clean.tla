------------------------- MODULE NaturalsInduction -------------------------

EXTENDS Integers, TLAPS

THEOREM NatInduction ==
ASSUME NEW P(_),
P(0),
\A n \in Nat : P(n) => P(n+1)
PROVE  \A n \in Nat : P(n)

THEOREM DownwardNatInduction ==
ASSUME NEW P(_), NEW m \in Nat, P(m),
\A n \in 1 .. m : P(n) => P(n-1)
PROVE  P(0)

THEOREM GeneralNatInduction ==
ASSUME NEW P(_),
\A n \in Nat : (\A m \in 0..(n-1) : P(m)) => P(n)
PROVE  \A n \in Nat : P(n)

THEOREM SmallestNatural ==
ASSUME NEW P(_), NEW n \in Nat, P(n)
PROVE  \E m \in Nat : /\ P(m)
/\ \A k \in 0 .. m-1 : ~ P(k)

THEOREM RecursiveFcnOfNat ==
ASSUME NEW Def(_,_),
ASSUME NEW n \in Nat, NEW g, NEW h,
\A i \in 0..(n-1) : g[i] = h[i]
PROVE  Def(g, n) = Def(h, n)
PROVE  LET f[n \in Nat] == Def(f, n)
IN  f = [n \in Nat |-> Def(f, n)]

NatInductiveDefHypothesis(f, f0, Def(_,_)) ==
(f =  CHOOSE g : g = [i \in Nat |-> IF i = 0 THEN f0 ELSE Def(g[i-1], i)])
NatInductiveDefConclusion(f, f0, Def(_,_)) ==
f = [i \in Nat |-> IF i = 0 THEN f0 ELSE Def(f[i-1], i)]

THEOREM NatInductiveDef ==
ASSUME NEW Def(_,_), NEW f, NEW f0,
NatInductiveDefHypothesis(f, f0, Def)
PROVE  NatInductiveDefConclusion(f, f0, Def)

THEOREM RecursiveFcnOfNatType ==
ASSUME NEW f, NEW S, NEW Def(_,_), f = [n \in Nat |-> Def(f,n)],
ASSUME NEW n \in Nat, NEW g, \A i \in 0 .. n-1 : g[i] \in S
PROVE  Def(g,n) \in S
PROVE  f \in [Nat -> S]

THEOREM NatInductiveDefType ==
ASSUME NEW Def(_,_), NEW S, NEW f, NEW f0 \in S,
NatInductiveDefConclusion(f, f0, Def),
f0 \in S,
\A v \in S, n \in Nat \ {0} : Def(v, n) \in S
PROVE  f \in [Nat -> S]

THEOREM RecursiveFcnOfNatUnique ==
ASSUME NEW Def(_,_), NEW f, NEW g,
f = [n \in Nat |-> Def(f,n)],
g = [n \in Nat |-> Def(g,n)],
ASSUME NEW n \in Nat, NEW ff, NEW gg,
\A i \in 0..(n-1) : ff[i] = gg[i]
PROVE  Def(ff, n) = Def(gg, n)
PROVE  f = g

THEOREM NatInductiveUnique ==
ASSUME NEW Def(_,_), NEW f, NEW g, NEW f0,
NatInductiveDefConclusion(f, f0, Def),
NatInductiveDefConclusion(g, f0, Def)
PROVE  f = g

FiniteNatInductiveDefHypothesis(f, c, Def(_,_), m, n) ==
(f =  CHOOSE g : g = [i \in m..n |-> IF i = m THEN c ELSE Def(g[i-1], i)])
FiniteNatInductiveDefConclusion(f, c, Def(_,_), m, n) ==
f = [i \in m..n |-> IF i = m THEN c ELSE Def(f[i-1], i)]

THEOREM FiniteNatInductiveDef ==
ASSUME NEW Def(_,_), NEW f, NEW c, NEW m \in Nat, NEW n \in Nat,
FiniteNatInductiveDefHypothesis(f, c, Def, m, n)
PROVE  FiniteNatInductiveDefConclusion(f, c, Def, m, n)

THEOREM FiniteNatInductiveDefType ==
ASSUME NEW S, NEW Def(_,_), NEW f, NEW c \in S, NEW m \in Nat, NEW n \in Nat,
FiniteNatInductiveDefConclusion(f, c, Def, m, n),
\A v \in S, i \in (m+1) .. n : Def(v,i) \in S
PROVE  f \in [m..n -> S]

THEOREM FiniteNatInductiveUnique ==
ASSUME NEW Def(_,_), NEW f, NEW g, NEW c, NEW m \in Nat, NEW n \in Nat,
FiniteNatInductiveDefConclusion(f, c, Def, m, n),
FiniteNatInductiveDefConclusion(g, c, Def, m, n)
PROVE  f = g

=============================================================================

FiniteNatInductiveDefHypothesis(f, c, Def(_,_), m, n) ==
(f =  CHOOSE g : g = [i \in m..n |-> IF i = m THEN c ELSE Def(g[i-1], i)])
FiniteNatInductiveDefConclusion(f, c, Def(_,_), m, n) ==
f = [i \in m..n |-> IF i = m THEN c ELSE Def(f[i-1], i)]

THEOREM FiniteNatInductiveDef ==
ASSUME NEW Def(_,_), NEW f, NEW c, NEW m \in Nat, NEW n \in Nat,
FiniteNatInductiveDefHypothesis(f, c, Def, m, n)
PROVE  FiniteNatInductiveDefConclusion(f, c, Def, m, n)

THEOREM FiniteNatInductiveDefType ==
ASSUME NEW S, NEW Def(_,_), NEW f, NEW c \in S, NEW m \in Nat, NEW n \in Nat,
FiniteNatInductiveDefConclusion(f, c, Def, m, n),
\A v \in S, i \in (m+1) .. n : Def(v,i) \in S
PROVE  f \in [m..n -> S]

THEOREM FiniteNatInductiveUnique ==
ASSUME NEW Def(_,_), NEW f, NEW g, NEW c, NEW m \in Nat, NEW n \in Nat,
FiniteNatInductiveDefConclusion(f, c, Def, m, n),
FiniteNatInductiveDefConclusion(g, c, Def, m, n)
PROVE  f = g

factorial[n \in Nat] == IF n = 0 THEN 1 ELSE n * factorial[n-1]

THEOREM FactorialDefConclusion == NatInductiveDefConclusion(factorial, 1, LAMBDA v,n : n*v)
<1>1. NatInductiveDefHypothesis(factorial, 1, LAMBDA v,n : n*v)
BY DEF NatInductiveDefHypothesis, factorial
<1>2. QED
BY <1>1, NatInductiveDef

THEOREM FactorialDef == \A n \in Nat : factorial[n] = IF n = 0 THEN 1 ELSE n * factorial[n-1]
BY FactorialDefConclusion DEFS NatInductiveDefConclusion

THEOREM FactorialType == factorial \in [Nat -> Nat]
<1>1. \A v \in Nat, n \in Nat \ {0} : n * v \in Nat
OBVIOUS
<1>2. QED
BY <1>1, 1 \in Nat, NatInductiveDefType, FactorialDefConclusion, Isa

=============================================================================
