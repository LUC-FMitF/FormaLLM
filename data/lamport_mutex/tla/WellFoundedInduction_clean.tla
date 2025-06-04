------------------------ MODULE WellFoundedInduction ------------------------

EXTENDS NaturalsInduction

IsTransitivelyClosedOn(R, S) ==
\A i, j, k \in S : (<<i, j>> \in R)  /\ (<<j, k>> \in  R)
=> (<<i, k>> \in R)

IsWellFoundedOn(R, S) ==
~ \E f \in [Nat -> S] : \A n \in Nat : <<f[n+1], f[n]>> \in R

LEMMA EmptyIsWellFounded == \A S : IsWellFoundedOn({}, S)

LEMMA IsWellFoundedOnSubset ==
ASSUME NEW R, NEW S, NEW T \in SUBSET S,
IsWellFoundedOn(R,S)
PROVE  IsWellFoundedOn(R,T)

LEMMA IsWellFoundedOnSubrelation ==
ASSUME NEW S, NEW R, NEW RR, RR \cap (S \X S) \subseteq R,
IsWellFoundedOn(R,S)
PROVE  IsWellFoundedOn(RR,S)

SetLessThan(x, R, S) ==  {y \in S : <<y, x>> \in R}

THEOREM WFMin ==
ASSUME NEW R, NEW S,
IsWellFoundedOn(R, S),
NEW T, T \subseteq S, T # {}
PROVE  \E x \in T : \A y \in T : ~ (<<y, x>> \in R)

THEOREM MinWF ==
ASSUME NEW R, NEW S,
\A T \in SUBSET S : T # {} => \E x \in T : \A y \in T : ~ (<<y, x>> \in R)
PROVE  IsWellFoundedOn(R,S)

LEMMA WellFoundedIsIrreflexive ==
ASSUME NEW R, NEW S, NEW x \in S,
IsWellFoundedOn(R, S)
PROVE  <<x, x>> \notin R

LEMMA WellFoundedIsAsymmetric ==
ASSUME NEW R, NEW S, NEW x \in S, NEW y \in S,
IsWellFoundedOn(R,S),
<<x,y>> \in R, <<y,x>> \in R
PROVE  FALSE

LEMMA WFSetLessThanIrreflexive ==
ASSUME NEW R, NEW S, NEW x \in S,
IsWellFoundedOn(R,S)
PROVE  x \notin SetLessThan(x,R,S)

LEMMA SetLessTransitive ==
ASSUME NEW R, NEW S, NEW x \in S, NEW y \in SetLessThan(x,R,S),
IsTransitivelyClosedOn(R, S)
PROVE  SetLessThan(y, R, S) \subseteq SetLessThan(x, R, S)

----------------------------------------------------------------------------

THEOREM WFInduction ==
ASSUME NEW P(_), NEW R, NEW S,
IsWellFoundedOn(R, S),
\A x \in S : (\A y \in SetLessThan(x, R, S) : P(y))
=> P(x)
PROVE  \A x \in S : P(x)

WFDefOn(R, S, Def(_,_)) ==
\A g, h :
\A x \in S :
(\A y \in SetLessThan(x, R, S) : g[y] = h[y])
=> (Def(g,x) = Def(h,x))

OpDefinesFcn(f, S, Def(_,_)) ==
f =  CHOOSE g : g = [x \in S |-> Def(g, x)]

WFInductiveDefines(f, S, Def(_,_)) ==
f = [x \in S |-> Def(f, x)]

WFInductiveUnique(S, Def(_,_)) ==
\A g, h : /\ WFInductiveDefines(g, S, Def)
/\ WFInductiveDefines(h, S, Def)
=> (g = h)

THEOREM WFDefOnUnique ==
ASSUME NEW Def(_,_), NEW R, NEW S,
IsWellFoundedOn(R, S), WFDefOn(R, S, Def)
PROVE  WFInductiveUnique(S, Def)

LEMMA WFInductiveDefLemma ==
ASSUME NEW Def(_,_), NEW R, NEW S, NEW f,
IsWellFoundedOn(R, S),
IsTransitivelyClosedOn(R, S),
WFDefOn(R, S, Def),
OpDefinesFcn(f, S, Def)
PROVE  WFInductiveDefines(f, S, Def)

TransitiveClosureOn(R,S) ==
{ ss \in S \X S :
\A U \in SUBSET (S \X S) :
/\ R \cap S \X S \subseteq U
/\ IsTransitivelyClosedOn(U, S)
=> ss \in U }

LEMMA TransitiveClosureThm ==
\A R, S :
/\ R \cap S \X S \subseteq TransitiveClosureOn(R, S)
/\ IsTransitivelyClosedOn(TransitiveClosureOn(R, S), S)

LEMMA TransitiveClosureMinimal ==
ASSUME NEW R, NEW S, NEW U \in SUBSET (S \X S),
R \cap S \X S \subseteq U,
IsTransitivelyClosedOn(U,S)
PROVE  TransitiveClosureOn(R,S) \subseteq U

LEMMA TCTCTC ==
ASSUME NEW R, NEW S, NEW i \in S, NEW j \in S, NEW k \in S,
<<i,j>> \in TransitiveClosureOn(R,S),
<<j,k>> \in TransitiveClosureOn(R,S)
PROVE  <<i,k>> \in TransitiveClosureOn(R,S)

LEMMA TCRTC ==
ASSUME NEW R, NEW S, NEW i \in S, NEW j \in S, NEW k \in S,
<<i,j>> \in TransitiveClosureOn(R,S), <<j,k>> \in R
PROVE  <<i,k>> \in TransitiveClosureOn(R,S)

LEMMA RTCTC ==
ASSUME NEW R, NEW S, NEW i \in S, NEW j \in S, NEW k \in S,
<<i,j>> \in R, <<j,k>> \in TransitiveClosureOn(R,S)
PROVE  <<i,k>> \in TransitiveClosureOn(R,S)

LEMMA TransitiveClosureChopLast ==
ASSUME NEW R, NEW S, NEW i \in S, NEW k \in S, <<i,k>> \in TransitiveClosureOn(R,S)
PROVE  \E j \in S : /\ <<j,k>> \in R
/\ i = j \/ <<i,j>> \in TransitiveClosureOn(R,S)

THEOREM TransitiveClosureWF ==
ASSUME NEW R, NEW S, IsWellFoundedOn(R,S)
PROVE  IsWellFoundedOn(TransitiveClosureOn(R, S), S)

THEOREM WFInductiveDef ==
ASSUME NEW Def(_,_), NEW R, NEW S, NEW f,
IsWellFoundedOn(R, S),
WFDefOn(R, S, Def),
OpDefinesFcn(f, S, Def)
PROVE  WFInductiveDefines(f, S, Def)

THEOREM WFInductiveDefType ==
ASSUME NEW Def(_,_), NEW f, NEW R, NEW S, NEW T,
T # {},
IsWellFoundedOn(R, S),
WFDefOn(R, S, Def),
WFInductiveDefines(f, S, Def),
\A g \in [S -> T], s \in S : Def(g, s) \in T
PROVE  f \in [S -> T]

----------------------------------------------------------------------------

OpToRel(_\prec_, S) == {ss \in S \X S : ss[1] \prec ss[2]}

THEOREM NatLessThanWellFounded == IsWellFoundedOn(OpToRel(<,Nat), Nat)

PreImage(f(_), S, R) == {ss \in S \X S : <<f(ss[1]), f(ss[2])>> \in R}

THEOREM PreImageWellFounded ==
ASSUME NEW S, NEW T, NEW R, NEW f(_),
\A s \in S : f(s) \in T,
IsWellFoundedOn(R, T)
PROVE  IsWellFoundedOn(PreImage(f, S, R), S)

LexPairOrdering(R1, R2, S1, S2) ==
{ss \in (S1 \X S2) \X (S1 \X S2) :
\/ <<ss[1][1], ss[2][1]>> \in R1
\/ /\ ss[1][1] = ss[2][1]
/\ <<ss[1][2], ss[2][2]>> \in R2}

THEOREM WFLexPairOrdering ==
ASSUME NEW R1, NEW R2, NEW S1, NEW S2,
IsWellFoundedOn(R1, S1),
IsWellFoundedOn(R2, S2)
PROVE  IsWellFoundedOn(LexPairOrdering(R1, R2, S1, S2), S1 \X S2)

LexProductOrdering(R, S, n) ==
{ ff \in [1..n -> S] \X [1..n -> S] :
\E j \in 1..n :
/\ \A i \in 1..(j-1) : ff[1][i] = ff[2][i]
/\ <<ff[1][j], ff[2][j]>> \in R }

THEOREM WFLexProductOrdering ==
ASSUME NEW R, NEW S, NEW n \in Nat,
IsWellFoundedOn(R, S)
PROVE  IsWellFoundedOn(LexProductOrdering(R, S, n), [1..n -> S])

=============================================================================
