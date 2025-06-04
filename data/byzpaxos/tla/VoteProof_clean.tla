----------------------------- MODULE VoteProof ------------------------------

EXTENDS Integers, NaturalsInduction, FiniteSets, FiniteSetTheorems,
WellFoundedInduction, TLC, TLAPS

CONSTANT Value,
Acceptor,
Quorum

ASSUME QA == /\ \A Q \in Quorum : Q \subseteq Acceptor
/\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

THEOREM QuorumNonEmpty == \A Q \in Quorum : Q # {}
PROOF BY QA
-----------------------------------------------------------------------------

Ballot == Nat
-----------------------------------------------------------------------------

VotedFor(a, b, v) == <<b, v>> \in votes[a]

DidNotVoteIn(a, b) == \A v \in Value : ~ VotedFor(a, b, v)

SafeAt(b, v) ==
LET SA[bb \in Ballot] ==

\/ bb = 0
\/ \E Q \in Quorum :
/\ \A a \in Q : maxBal[a] \geq bb
/\ \E c \in -1..(bb-1) :
/\ (c # -1) => /\ SA[c]
/\ \A a \in Q :
\A w \in Value :
VotedFor(a, c, w) => (w = v)
/\ \A d \in (c+1)..(bb-1), a \in Q : DidNotVoteIn(a, d)
IN  SA[b]
}

macro IncreaseMaxBal(b) {
when b > maxBal[self] ;
maxBal[self] := b
}

macro VoteFor(b, v) {
when /\ maxBal[self] \leq b
/\ DidNotVoteIn(self, b)
/\ \A p \in Acceptor \ {self} :
\A w \in Value : VotedFor(p, b, w) => (w = v)
/\ SafeAt(b, v) ;
votes[self]  := votes[self] \cup {<<b, v>>};
maxBal[self] := b
}

process (acceptor \in Acceptor) {
acc : while (TRUE) {
with (b \in Ballot) {
either IncreaseMaxBal(b)
or     with (v \in Value) { VoteFor(b, v) }
}
}
}
}

The following is the TLA+ specification produced by the translation.
Blank lines, produced by the translation because of the comments, have
been deleted.
****************************)

VARIABLES votes, maxBal

VotedFor(a, b, v) == <<b, v>> \in votes[a]

DidNotVoteIn(a, b) == \A v \in Value : ~ VotedFor(a, b, v)

SafeAt(b, v) ==
LET SA[bb \in Ballot] ==
\/ bb = 0
\/ \E Q \in Quorum :
/\ \A a \in Q : maxBal[a] \geq bb
/\ \E c \in -1..(bb-1) :
/\ (c # -1) => /\ SA[c]
/\ \A a \in Q :
\A w \in Value :
VotedFor(a, c, w) => (w = v)
/\ \A d \in (c+1)..(bb-1), a \in Q : DidNotVoteIn(a, d)
IN  SA[b]

vars == << votes, maxBal >>

ProcSet == (Acceptor)

Init ==
/\ votes = [a \in Acceptor |-> {}]
/\ maxBal = [a \in Acceptor |-> -1]

acceptor(self) == \E b \in Ballot:
\/ /\ b > maxBal[self]
/\ maxBal' = [maxBal EXCEPT ![self] = b]
/\ UNCHANGED votes
\/ /\ \E v \in Value:
/\ /\ maxBal[self] \leq b
/\ DidNotVoteIn(self, b)
/\ \A p \in Acceptor \ {self} :
\A w \in Value : VotedFor(p, b, w) => (w = v)
/\ SafeAt(b, v)
/\ votes' = [votes EXCEPT ![self] = votes[self] \cup {<<b, v>>}]
/\ maxBal' = [maxBal EXCEPT ![self] = b]

Next == (\E self \in Acceptor: acceptor(self))

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

THEOREM SafeAtProp ==
\A b \in Ballot, v \in Value :
SafeAt(b, v) <=>
\/ b = 0
\/ \E Q \in Quorum :
/\ \A a \in Q : maxBal[a] \geq b
/\ \E c \in -1..(b-1) :
/\ (c # -1) => /\ SafeAt(c, v)
/\ \A a \in Q :
\A w \in Value :
VotedFor(a, c, w) => (w = v)
/\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteIn(a, d)
<1>1. SUFFICES ASSUME NEW v \in Value
PROVE  \A b \in Ballot : SafeAtProp!(b, v)
BY Zenon
<1> USE DEF Ballot
<1> DEFINE Def(SA, bb) ==
\/ bb = 0
\/ \E Q \in Quorum :
/\ \A a \in Q : maxBal[a] \geq bb
/\ \E c \in -1..(bb-1) :
/\ (c # -1) => /\ SA[c]
/\ \A a \in Q :
\A w \in Value :
VotedFor(a, c, w) => (w = v)
/\ \A d \in (c+1)..(bb-1), a \in Q : DidNotVoteIn(a, d)
SA[bb \in Ballot] == Def(SA, bb)
<1>2. \A b : SafeAt(b, v) = SA[b]
BY DEF SafeAt
<1>3. ASSUME NEW n \in Nat, NEW g, NEW h,
\A i \in 0..(n-1) : g[i] = h[i]
PROVE  Def(g, n) = Def(h, n)
BY <1>3
<1>4. SA = [b \in Ballot |-> Def(SA, b)]
<2> HIDE DEF Def
<2> QED
BY <1>3, RecursiveFcnOfNat, Isa
<1>5. \A b \in Ballot : SA[b] = Def(SA, b)
<2> HIDE DEF Def
<2> QED
BY <1>4, Zenon
<1>6. QED
BY <1>2, <1>5, Zenon DEF SafeAt
-----------------------------------------------------------------------------

TypeOK == /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
/\ maxBal \in [Acceptor -> Ballot \cup {-1}]

ChosenIn(b, v) == \E Q \in Quorum : \A a \in Q : VotedFor(a, b, v)

chosen == {v \in Value : \E b \in Ballot : ChosenIn(b, v)}
-----------------------------------------------------------------------------

LEMMA SafeLemma ==
TypeOK =>
\A b \in Ballot :
\A v \in Value :
SafeAt(b, v) =>
\A c \in 0..(b-1) :
\E Q \in Quorum :
\A a \in Q : /\ maxBal[a] >= c
/\ \/ DidNotVoteIn(a, c)
\/ VotedFor(a, c, v)
<1> SUFFICES ASSUME TypeOK
PROVE  SafeLemma!2
OBVIOUS
<1> DEFINE P(b) == \A c \in 0..b : SafeLemma!2!(c)
<1> USE DEF Ballot
<1>1. P(0)
OBVIOUS
<1>2. ASSUME NEW b \in Ballot, P(b)
PROVE  P(b+1)
<2>1. /\ b+1 \in Ballot \ {0}
/\ (b+1) - 1 = b
OBVIOUS
<2>2. 0..(b+1) = (0..b) \cup {b+1}
OBVIOUS
<2>3. SUFFICES ASSUME NEW v \in Value,
SafeAt(b+1, v),
NEW c \in 0..b
PROVE  \E Q \in Quorum :
\A a \in Q : /\ maxBal[a] >= c
/\ \/ DidNotVoteIn(a, c)
\/ VotedFor(a, c, v)
BY <1>2
<2>4. PICK Q \in Quorum :
/\ \A a \in Q : maxBal[a] \geq (b+1)
/\ \E cc \in -1..b :
/\ (cc # -1) => /\ SafeAt(cc, v)
/\ \A a \in Q :
\A w \in Value :
VotedFor(a, cc, w) => (w = v)
/\ \A d \in (cc+1)..b, a \in Q : DidNotVoteIn(a, d)
BY SafeAtProp, <2>3, <2>1, Zenon
<2>5. PICK cc \in -1..b :
/\ (cc # -1) => /\ SafeAt(cc, v)
/\ \A a \in Q :
\A w \in Value :
VotedFor(a, cc, w) => (w = v)
/\ \A d \in (cc+1)..b, a \in Q : DidNotVoteIn(a, d)
BY <2>4
<2>6. CASE c > cc
BY <2>4, <2>5, <2>6, QA DEF TypeOK
<2>7. CASE c = cc
<3>2. \A a \in Q : maxBal[a] \in Ballot \cup {-1}
BY QA DEF TypeOK
<3>3. \A a \in Q : maxBal[a] \geq c
BY <2>4, <2>7, <3>2
<3>4. \A a \in Q : \/ DidNotVoteIn(a, c)
\/ VotedFor(a, c, v)
BY <2>7, <2>5 DEF DidNotVoteIn
<3>5. QED
BY <3>3, <3>4
<2>8. CASE c < cc
BY <2>8, <1>2, <2>5
<2>9. QED
BY <2>6, <2>7, <2>8
<1>3. \A b \in Ballot : P(b)
BY <1>1, <1>2, NatInduction, Isa
<1>4. QED
BY <1>3
-----------------------------------------------------------------------------

VInv1 == \A a \in Acceptor, b \in Ballot, v, w \in Value :
VotedFor(a, b, v) /\ VotedFor(a, b, w) => (v = w)

VInv2 == \A a \in Acceptor, b \in Ballot, v \in Value :
VotedFor(a, b, v) => SafeAt(b, v)

VInv3 ==  \A a1, a2 \in Acceptor, b \in Ballot, v1, v2 \in Value :
VotedFor(a1, b, v1) /\ VotedFor(a2, b, v2) => (v1 = v2)

THEOREM VInv3 => VInv1
BY DEF VInv1, VInv3
-----------------------------------------------------------------------------

LEMMA VT0 == /\ TypeOK
/\ VInv1
/\ VInv2
=> \A v, w \in Value, b, c \in Ballot :
(b > c) /\ SafeAt(b, v) /\ ChosenIn(c, w) => (v = w)
<1> SUFFICES ASSUME TypeOK, VInv1, VInv2,
NEW v \in Value, NEW w \in Value
PROVE  \A b, c \in Ballot :
(b > c) /\ SafeAt(b, v) /\ ChosenIn(c, w) => (v = w)
OBVIOUS
<1> P(b) == \A c \in Ballot :
(b > c) /\ SafeAt(b, v) /\ ChosenIn(c, w) => (v = w)
<1> USE DEF Ballot

<1>1. P(0)
OBVIOUS
<1>2. ASSUME NEW b \in Ballot, \A i \in 0..(b-1) : P(i)
PROVE  P(b)
<2>1. CASE b = 0
BY <2>1
<2>2. CASE b # 0
<3>1. SUFFICES ASSUME NEW c \in Ballot, b > c, SafeAt(b, v), ChosenIn(c, w)
PROVE  v=w
OBVIOUS
<3>2. PICK Q \in Quorum : \A a \in Q : VotedFor(a, c, w)
BY <3>1 DEF ChosenIn
<3>3. PICK QQ \in Quorum,
d \in -1..(b-1) :
/\ (d # -1) => /\ SafeAt(d, v)
/\ \A a \in QQ :
\A x \in Value :
VotedFor(a, d, x) => (x = v)
/\ \A e \in (d+1)..(b-1), a \in QQ : DidNotVoteIn(a, e)
BY <2>2, <3>1, SafeAtProp, Zenon
<3> PICK aa \in QQ \cap Q : TRUE
BY QA
<3>4. c \leq d
BY <3>1, <3>2, <3>3 DEF DidNotVoteIn
<3>5. CASE c = d
BY <3>2, <3>3, <3>4, <3>5
<3>6. CASE d > c
BY <1>2, <3>1, <3>3, <3>4, <3>6
<3>7. QED
BY <3>4, <3>5, <3>6
<2>. QED  BY <2>1, <2>2
<1>3. \A b \in Ballot : P(b)
<2>. HIDE DEF P
<2>. QED  BY <1>2, GeneralNatInduction, Isa
<1>4. QED
BY <1>3

THEOREM VT1 == /\ TypeOK
/\ VInv1
/\ VInv2
=> \A v, w :
(v \in chosen) /\ (w \in chosen) => (v = w)
<1>1. SUFFICES ASSUME TypeOK, VInv1, VInv2,
NEW v, NEW w,
v \in chosen, w \in chosen
PROVE  v = w
OBVIOUS
<1>2. v \in Value /\ w \in Value
BY <1>1 DEF chosen
<1>3. PICK b \in Ballot, c \in Ballot : ChosenIn(b, v) /\ ChosenIn(c, w)
BY <1>1 DEF chosen
<1>4. PICK Q \in Quorum, R \in Quorum :
/\ \A a \in Q : VotedFor(a, b, v)
/\ \A a \in R : VotedFor(a, c, w)
BY <1>3 DEF ChosenIn
<1>5. PICK av \in Q, aw \in R: /\ VotedFor(av, b, v)
/\ VotedFor(aw, c, w)
BY <1>4, QuorumNonEmpty
<1>6. SafeAt(b, v) /\ SafeAt(c, w)
BY <1>1, <1>2, <1>5, QA DEF VInv2
<1>7. CASE b = c
<2> PICK a \in Q \cap R : TRUE
BY QA
<2>1. /\ VotedFor(a, b, v)
/\ VotedFor(a, c, w)
BY <1>4
<2>2. QED
BY <1>1, <1>2, <1>7, <2>1, QA DEF VInv1
<1>8. CASE b > c
BY <1>1, <1>6, <1>3, <1>8, VT0, <1>2
<1>9. CASE c > b
BY <1>1, <1>6, <1>3, <1>9, VT0, <1>2
<1>10. QED
BY <1>7, <1>8, <1>9 DEF Ballot

THEOREM SafeAtPropPrime ==
\A b \in Ballot, v \in Value :
SafeAt(b, v)' <=>
\/ b = 0
\/ \E Q \in Quorum :
/\ \A a \in Q : maxBal'[a] \geq b
/\ \E c \in -1..(b-1) :
/\ (c # -1) => /\ SafeAt(c, v)'
/\ \A a \in Q :
\A w \in Value :
VotedFor(a, c, w)' => (w = v)
/\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteIn(a, d)'
<1>1. SafeAtProp'   BY SafeAtProp, PTL
<1>. QED            BY <1>1

LEMMA VT0Prime ==
/\ TypeOK'
/\ VInv1'
/\ VInv2'
=> \A v, w \in Value, b, c \in Ballot :
(b > c) /\ SafeAt(b, v)' /\ ChosenIn(c, w)' => (v = w)
<1>1. VT0'   BY VT0, PTL
<1>. QED     BY <1>1

THEOREM VT1Prime ==
/\ TypeOK'
/\ VInv1'
/\ VInv2'
=> \A v, w :
(v \in chosen') /\ (w \in chosen') => (v = w)
<1>1. VT1'   BY VT1, PTL
<1>. QED     BY <1>1

-----------------------------------------------------------------------------

VInv4 == \A a \in Acceptor, b \in Ballot :
maxBal[a] < b => DidNotVoteIn(a, b)

VInv == TypeOK /\ VInv2 /\ VInv3 /\ VInv4
-----------------------------------------------------------------------------

IncreaseMaxBal(self, b) ==
/\ b > maxBal[self]
/\ maxBal' = [maxBal EXCEPT ![self] = b]
/\ UNCHANGED votes

VoteFor(self, b, v) ==
/\ maxBal[self] \leq b
/\ DidNotVoteIn(self, b)
/\ \A p \in Acceptor \ {self} :
\A w \in Value : VotedFor(p, b, w) => (w = v)
/\ SafeAt(b, v)
/\ votes' = [votes EXCEPT ![self] = votes[self] \cup {<<b, v>>}]
/\ maxBal' = [maxBal EXCEPT ![self] = b]

BallotAction(self, b) ==
\/ IncreaseMaxBal(self, b)
\/ \E v \in Value : VoteFor(self, b, v)

ASSUME AcceptorNonempty == Acceptor # {}

LEMMA NextDef ==
TypeOK =>
(Next =  \E self \in Acceptor :
\E b \in Ballot : BallotAction(self, b) )
<1> HAVE TypeOK
<1>2. Next = \E self \in Acceptor: acceptor(self)
BY AcceptorNonempty DEF Next, ProcSet
<1>3. @ = NextDef!2!2
BY DEF Next, BallotAction, IncreaseMaxBal, VoteFor, ProcSet, acceptor
<1>4. QED
BY <1>2, <1>3
-----------------------------------------------------------------------------

THEOREM InductiveInvariance == VInv /\ [Next]_vars => VInv'
<1>1. VInv /\ (vars' = vars) => VInv'
BY Isa
DEF VInv, vars, TypeOK, VInv2, VotedFor, SafeAt, DidNotVoteIn, VInv3, VInv4
<1> SUFFICES ASSUME VInv,
NEW self \in Acceptor,
NEW b \in Ballot,
BallotAction(self, b)
PROVE  VInv'
BY <1>1, NextDef DEF VInv

<1>2. TypeOK'
<2>1. CASE IncreaseMaxBal(self, b)
BY <2>1 DEF IncreaseMaxBal, VInv, TypeOK
<2>2. CASE \E v \in Value : VoteFor(self, b, v)
BY <2>2 DEF VInv, TypeOK, VoteFor
<2>3. QED
BY <2>1, <2>2 DEF BallotAction

<1>3. ASSUME NEW a \in Acceptor, NEW c \in Ballot, NEW w \in Value,
VotedFor(a, c, w)
PROVE  VotedFor(a, c, w)'
<2>1. CASE IncreaseMaxBal(self, b)
BY <2>1, <1>3 DEF IncreaseMaxBal, VotedFor
<2>2. CASE \E v \in Value : VoteFor(self, b, v)
<3>1. PICK v \in Value : VoteFor(self, b, v)
BY <2>2
<3>2. CASE a = self
<4>1. votes'[a] = votes[a] \cup {<<b, v>>}
BY <3>1, <3>2 DEF VoteFor, VInv, TypeOK
<4>2. QED
BY <1>3, <4>1 DEF VotedFor
<3>3. CASE a # self
<4>1. votes[a] = votes'[a]
BY <3>1, <3>3 DEF VoteFor, VInv, TypeOK
<4>2. QED
BY <1>3, <4>1 DEF VotedFor
<3>4. QED
BY <3>2, <3>3 DEF VoteFor
<2>3. QED
BY <2>1, <2>2 DEF BallotAction

<1>4. ASSUME NEW a \in Acceptor, NEW c \in Ballot, NEW w \in Value,
~VotedFor(a, c, w), VotedFor(a, c, w)'
PROVE  (a = self) /\ (c = b) /\ VoteFor(self, b, w)
<2>1. CASE IncreaseMaxBal(self, b)
BY <2>1, <1>4 DEF IncreaseMaxBal, VInv, TypeOK, VotedFor
<2>2. CASE \E v \in Value : VoteFor(self, b, v)
<3>1. PICK v \in Value : VoteFor(self, b, v)
BY <2>2
<3>2. a = self
BY <3>1, <1>4 DEF VoteFor, VInv, TypeOK, VotedFor
<3>3. votes'[a] = votes[a] \cup {<<b, v>>}
BY <3>1, <3>2 DEF VoteFor, VInv, TypeOK
<3>4. c = b /\ v = w
BY <1>4, <3>3 DEF VotedFor
<3>5. QED
BY <3>1, <3>2, <3>4
<2>3. QED
BY <2>1, <2>2 DEF BallotAction

<1>5. ASSUME NEW a \in Acceptor
PROVE  /\ maxBal[a] \in Ballot \cup {-1}
/\ maxBal'[a] \in Ballot \cup {-1}
/\ maxBal'[a] >= maxBal[a]
BY DEF VInv, TypeOK, IncreaseMaxBal, VInv, VoteFor, BallotAction, DidNotVoteIn,
VotedFor, Ballot

<1>6. ASSUME NEW c \in Ballot, NEW w \in Value,
SafeAt(c, w)
PROVE  SafeAt(c, w)'
<2> USE DEF Ballot
<2> DEFINE P(i) == \A j \in 0..i : SafeAt(j, w) => SafeAt(j, w)'
<2>1. P(0)
BY SafeAtPropPrime, 0 .. 0 = {0}, Zenon
<2>2. ASSUME NEW d \in Ballot, P(d)
PROVE  P(d+1)
<3>1. SUFFICES ASSUME NEW e \in 0..(d+1), SafeAt(e, w)
PROVE  SafeAt(e, w)'
OBVIOUS
<3>2. CASE e \in 0..d
BY <2>2, <3>1, <3>2
<3>3. CASE e = d+1
<4>. e \in Ballot \ {0}
BY <3>3
<4>1. PICK Q \in Quorum : SafeAtProp!(e, w)!2!2!(Q)
BY <3>1, SafeAtProp, Zenon
<4>2. \A aa \in Q : maxBal'[aa] \geq e
BY <1>5, <4>1, QA
<4>3. \E cc \in -1..(e-1) :
/\ (cc # -1) => /\ SafeAt(cc, w)'
/\ \A ax \in Q :
\A z \in Value :
VotedFor(ax, cc, z)' => (z = w)
/\ \A dd \in (cc+1)..(e-1), ax \in Q : DidNotVoteIn(ax, dd)'
<5>1. ASSUME NEW cc \in 0..(e-1),
NEW ax \in Q, NEW z \in Value,
VotedFor(ax, cc, z)', ~ VotedFor(ax, cc, z)
PROVE  FALSE
<6>1. (ax = self) /\ (cc = b) /\ VoteFor(self, b, z)
BY <5>1, <1>4, QA
<6>2. /\ maxBal[ax] \geq e
/\ maxBal[self] \leq b
BY <4>1, <6>1 DEF VoteFor
<6>. QED  BY <3>3, <6>1, <6>2 DEF VInv, TypeOK
<5>2. PICK cc \in -1..(e-1) : SafeAtProp!(e, w)!2!2!(Q)!2!(cc)
BY <4>1
<5>3. ASSUME cc # -1
PROVE  /\ SafeAt(cc, w)'
/\ \A ax \in Q : \A z \in Value :
VotedFor(ax, cc, z)' => (z = w)
<6>1. /\ SafeAt(cc, w)
/\ \A ax \in Q :
\A z \in Value : VotedFor(ax, cc, z) => (z = w)
BY <5>2, <5>3
<6>2. SafeAt(cc, w)'
BY <6>1, <5>3, <3>3, <2>2
<6>3. ASSUME NEW ax \in Q, NEW z \in Value, VotedFor(ax, cc, z)'
PROVE  z = w
<7>1. CASE VotedFor(ax, cc, z)
BY <6>1, <7>1
<7>2. CASE ~ VotedFor(ax, cc, z)
BY <7>2, <6>3, <5>1, <5>3
<7>3. QED
BY <7>1, <7>2
<6>4. QED
BY <6>2, <6>3
<5>4. ASSUME NEW dd \in (cc+1)..(e-1), NEW ax \in Q,
~ DidNotVoteIn(ax, dd)'
PROVE  FALSE
BY <5>2, <5>1, <5>4 DEF DidNotVoteIn
<5>5. QED
BY <5>3, <5>4
<4>4.  \/ e = 0
\/ \E Q_1 \in Quorum :
/\ \A aa \in Q_1 : maxBal'[aa] \geq e
/\ \E c_1 \in -1..e - 1 :
/\ c_1 # -1
=> (/\ SafeAt(c_1, w)'
/\ \A aa \in Q_1 :
\A w_1 \in Value :
VotedFor(aa, c_1, w_1)' => w_1 = w)
/\ \A d_1 \in c_1 + 1..e - 1, aa \in Q_1 :
DidNotVoteIn(aa, d_1)'
BY <4>2, <4>3, <3>3
<4>6. SafeAt(e, w)' <=> <4>4
BY SafeAtPropPrime, <3>3, Zenon
<4>7. QED
BY <4>2, <4>3, <4>6
<3>4. QED
BY <3>2, <3>3
<2>3. \A d \in Ballot : P(d)
BY <2>1, <2>2, NatInduction, Isa
<2>4. QED
BY <2>3, <1>6

<1>7. VInv2'
<2>1. SUFFICES ASSUME NEW a \in Acceptor, NEW c \in Ballot, NEW v \in Value,
VotedFor(a, c, v)'
PROVE  SafeAt(c, v)'
BY DEF VInv2
<2>2. CASE VotedFor(a, c, v)
BY <1>6, <2>2 DEF VInv, VInv2
<2>3. CASE ~VotedFor(a, c, v)
BY <1>6, <2>1, <2>3, <1>4 DEF VoteFor
<2>4. QED
BY <2>2, <2>3

<1>8. VInv3'
<2>1. ASSUME NEW a1 \in Acceptor, NEW a2\in Acceptor,
NEW c \in Ballot,    NEW v1 \in Value, NEW v2 \in Value,
VotedFor(a1, c, v1)',
VotedFor(a2, c, v2)',
VotedFor(a1, c, v1),
VotedFor(a2, c, v2)
PROVE v1 = v2
BY <2>1 DEF VInv, VInv3
<2>2. ASSUME NEW a1 \in Acceptor, NEW a2\in Acceptor,
NEW c \in Ballot,    NEW v1 \in Value, NEW v2 \in Value,
VotedFor(a1, c, v1)',
VotedFor(a2, c, v2)',
~ VotedFor(a1, c, v1)
PROVE v1 = v2
<3>1. (a1 = self) /\ (c = b) /\ VoteFor(self, b, v1)
BY <2>2, <1>4
<3>2. CASE a2 = self
<4>1. ~VotedFor(self, b, v2)
BY <3>1 DEF VoteFor, DidNotVoteIn
<4>2. VoteFor(self, b, v2)
BY <2>2, <3>1, <3>2, <4>1,  <1>4
<4>. QED  BY <3>1, <4>2, <2>2 DEF VotedFor, VoteFor, VInv, TypeOK
<3>3. CASE a2 # self
BY <3>1, <3>3, <2>2 DEF VotedFor, VoteFor, VInv, TypeOK
<3>4. QED
BY <3>2, <3>3
<2>3. QED
BY <2>1, <2>2 DEF VInv3

<1>9. VInv4'
<2>1. SUFFICES ASSUME NEW a \in Acceptor, NEW c \in Ballot,
maxBal'[a] < c,
~ DidNotVoteIn(a, c)'
PROVE  FALSE
BY DEF VInv4
<2>2. maxBal[a] < c
BY <1>5, <2>1 DEF Ballot
<2>3. DidNotVoteIn(a, c)
BY <2>2 DEF VInv, VInv4
<2>4. PICK v \in Value : VotedFor(a, c, v)'
BY <2>1 DEF DidNotVoteIn
<2>5. (a = self) /\ (c = b) /\ VoteFor(self, b, v)
BY <1>4, <2>1, <2>3, <2>4 DEF DidNotVoteIn
<2>6. maxBal'[a] = c
BY <2>5 DEF VoteFor, VInv, TypeOK
<2>7. QED
BY <2>1, <2>6 DEF Ballot

<1>10. QED
BY <1>2, <1>7, <1>8, <1>9 DEF VInv

THEOREM InitImpliesInv == Init => VInv
BY DEF Init, VInv, TypeOK, ProcSet, VInv2, VInv3, VInv4, VotedFor, DidNotVoteIn

THEOREM VT2 == Spec => []VInv
BY InitImpliesInv, InductiveInvariance, PTL DEF Spec

-----------------------------------------------------------------------------

C == INSTANCE Consensus
Refines == C!Spec

THEOREM VT3 == Spec => C!Spec
<1>1. Init => C!Init
<2> SUFFICES ASSUME Init
PROVE  C!Init
OBVIOUS
<2>1. SUFFICES ASSUME NEW v \in chosen
PROVE  FALSE
BY DEF C!Init
<2>2. PICK b \in Ballot, Q \in Quorum : \A a \in Q : VotedFor(a, b, v)
BY <2>1 DEF chosen, ChosenIn
<2>3. PICK a \in Q : <<b, v>> \in votes[a]
BY QuorumNonEmpty, <2>2 DEF VotedFor
<2>4. QED
BY <2>3, QA DEF Init

<1>2. VInv /\ VInv'/\ [Next]_vars => [C!Next]_C!vars
<2>. SUFFICES ASSUME VInv, VInv', [Next]_vars
PROVE  [C!Next]_C!vars
OBVIOUS
<2>1. CASE vars' = vars
BY <2>1 DEF vars, C!vars, chosen, ChosenIn, VotedFor
<2>2. SUFFICES ASSUME NEW self \in Acceptor,
NEW b \in Ballot,
BallotAction(self, b)
PROVE  [C!Next]_C!vars
BY <2>1, NextDef DEF VInv
<2>3. ASSUME IncreaseMaxBal(self, b)
PROVE  C!vars' = C!vars
BY <2>3 DEF IncreaseMaxBal, C!vars, chosen, ChosenIn, VotedFor
<2>4. ASSUME NEW v \in Value,
VoteFor(self, b, v)
PROVE  [C!Next]_C!vars
<3>3. ASSUME NEW w \in chosen
PROVE  w \in chosen'
<4>1. PICK c \in Ballot, Q \in Quorum : \A a \in Q : <<c, w>> \in votes[a]
BY <3>3 DEF chosen, ChosenIn, VotedFor
<4>2. SUFFICES ASSUME NEW a \in Q
PROVE  <<c, w>> \in votes'[a]
BY DEF chosen, ChosenIn, VotedFor
<4>3. CASE a = self
BY <2>4, <4>1, <4>3 DEF VoteFor, VInv, TypeOK
<4>4. CASE a # self
BY <2>4, <4>1, <4>4, QA DEF VoteFor, VInv, TypeOK
<4>5. QED
BY <4>3, <4>4
<3>1. ASSUME NEW w \in chosen,
v \in chosen'
PROVE  w = v
BY <3>3, <3>1, VT1Prime DEF VInv, VInv1, VInv3
<3>2. ASSUME NEW w, w \notin chosen, w \in chosen'
PROVE  w = v
<4>2. PICK c \in Ballot, Q \in Quorum : \A a \in Q : <<c, w>> \in votes'[a]
BY <3>2 DEF chosen, ChosenIn, VotedFor
<4>3. PICK a \in Q : <<c, w>> \notin votes[a]
BY <3>2 DEF chosen, ChosenIn, VotedFor
<4>4. CASE a = self
BY <2>4, <4>4, <4>2, <4>3 DEF VoteFor, VInv, TypeOK
<4>5. CASE a # self
BY <2>4, <4>2, <4>3, <4>5, QA DEF VoteFor, VInv, TypeOK
<4>6. QED
BY <4>4, <4>5
<3>. QED
BY <3>3, <3>1, <3>2 DEF C!Next, C!vars
<2>5. QED
BY <2>2, <2>3, <2>4 DEF BallotAction
<1>3. QED
BY <1>1, <1>2, VT2, PTL DEF Spec, C!Spec

-----------------------------------------------------------------------------

ASSUME AcceptorFinite == IsFiniteSet(Acceptor)

ASSUME ValueNonempty == Value # {}
-----------------------------------------------------------------------------

LEMMA FiniteSetHasMax ==
ASSUME NEW S \in SUBSET Int, IsFiniteSet(S), S # {}
PROVE  \E max \in S : \A x \in S : max >= x
<1>. DEFINE P(T) == T \in SUBSET Int /\ T # {} => \E max \in T : \A x \in T : max >= x
<1>1. P({})
OBVIOUS
<1>2. ASSUME NEW T, NEW x, P(T), x \notin T
PROVE  P(T \cup {x})
BY <1>2
<1>3. \A T : IsFiniteSet(T) => P(T)
<2>. HIDE DEF P
<2>. QED  BY <1>1, <1>2, FS_Induction, IsaM("blast")
<1>. QED  BY <1>3, Zenon

-----------------------------------------------------------------------------

THEOREM VT4 == TypeOK /\ VInv2 /\ VInv3  =>
\A Q \in Quorum, b \in Ballot :
(\A a \in Q : (maxBal[a] >= b)) => \E v \in Value : SafeAt(b,v)

<1>. USE DEF Ballot
<1>1. SUFFICES ASSUME TypeOK, VInv2, VInv3,
NEW Q \in Quorum, NEW b \in Ballot,
(\A a \in Q : (maxBal[a] >= b))
PROVE  \E v \in Value : SafeAt(b, v)
OBVIOUS
<1>2. CASE b = 0
BY ValueNonempty, <1>1, SafeAtProp, <1>2, Zenon
<1>4. SUFFICES ASSUME b # 0
PROVE    \E v \in Value :
\E c \in -1..(b-1) :
/\ (c # -1) => /\ SafeAt(c, v)
/\ \A a \in Q :
\A w \in Value :
VotedFor(a, c, w) => (w = v)
/\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteIn(a, d)
BY <1>1, <1>2, SafeAtProp
<1>5. CASE \A a \in Q, c \in 0..(b-1) : DidNotVoteIn(a, c)
BY <1>5, ValueNonempty
<1>6. CASE \E a \in Q, c \in 0..(b-1) : ~DidNotVoteIn(a, c)
<2>1. PICK c \in 0..(b-1) :
/\ \E a \in Q : ~DidNotVoteIn(a, c)
/\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteIn(a, d)
<3> DEFINE S == {c \in 0..(b-1) : \E a \in Q : ~DidNotVoteIn(a, c)}
<3>1. S # {}
BY <1>6
<3>2. PICK c \in S : \A d \in S : c >= d
<4>2. IsFiniteSet(S)
BY FS_Interval, FS_Subset, 0 \in Int, b-1 \in Int, Zenon
<4>3. QED
BY <3>1, <4>2, FiniteSetHasMax
<3>. QED
BY <3>2 DEF Ballot
<2>4. PICK a0 \in Q, v \in Value : VotedFor(a0, c, v)
BY <2>1 DEF DidNotVoteIn
<2>5. \A a \in Q : \A w \in Value :
VotedFor(a, c, w) => (w = v)
BY <2>4, QA, <1>1 DEF VInv3
<2>6. SafeAt(c, v)
BY <1>1, <2>4, QA DEF VInv2
<2>7. QED
BY <2>1, <2>5, <2>6
<1>7. QED
BY <1>5, <1>6
-------------------------------------------------------------------------------

LiveAssumption ==
\E Q \in Quorum, b \in Ballot :
/\ \A self \in Q : WF_vars(BallotAction(self, b))
/\ [] [\A self \in Q : \A c \in Ballot :
(c > b) => ~ BallotAction(self, c)]_vars

LiveSpec == Spec /\ LiveAssumption

-----------------------------------------------------------------------------

THEOREM AlwaysForall ==
ASSUME NEW CONSTANT S, NEW TEMPORAL P(_)
PROVE  (\A s \in S : []P(s)) <=> [](\A s \in S : P(s))
OBVIOUS

LEMMA EventuallyAlwaysForall ==
ASSUME NEW CONSTANT S, IsFiniteSet(S),
NEW TEMPORAL P(_)
PROVE  (\A s \in S : <>[]P(s)) => <>[](\A s \in S : P(s))
<1>. DEFINE A(x) == <>[]P(x)
L(T) == \A s \in T : A(s)
R(T) == \A s \in T : P(s)
Q(T) == L(T) => <>[]R(T)
<1>1. Q({})
<2>1. R({})       OBVIOUS
<2>2. <>[]R({})   BY <2>1, PTL
<2>. QED          BY <2>2
<1>2. ASSUME NEW T, NEW x
PROVE  Q(T) => Q(T \cup {x})
<2>1. L(T \cup {x}) => A(x)
<3>. HIDE DEF A
<3>. QED  OBVIOUS
<2>2. L(T \cup {x}) /\ Q(T) => <>[]R(T)
OBVIOUS
<2>3. <>[]R(T) /\ A(x) => <>[](R(T) /\ P(x))
BY PTL
<2>4. R(T) /\ P(x) => R(T \cup {x})
OBVIOUS
<2>5. <>[](R(T) /\ P(x)) => <>[]R(T \cup {x})
BY <2>4, PTL
<2>. QED
BY <2>1, <2>2, <2>3, <2>5
<1>. HIDE DEF Q
<1>3. \A T : IsFiniteSet(T) => Q(T)
BY <1>1, <1>2, FS_Induction, IsaM("blast")
<1>4. Q(S)
BY <1>3
<1>. QED
BY <1>4 DEF Q
-----------------------------------------------------------------------------

THEOREM Liveness == LiveSpec => C!LiveSpec
<1> SUFFICES ASSUME NEW Q \in Quorum, NEW b \in Ballot
PROVE  Spec /\ LiveAssumption!(Q, b) => C!LiveSpec
BY Isa DEF LiveSpec, LiveAssumption

<1>a. IsFiniteSet(Q)
BY QA, AcceptorFinite, FS_Subset

<1>1. C!LiveSpec <=> C!Spec /\ ([]<><<C!Next>>_C!vars \/ []<>(chosen # {}))
BY ValueNonempty, C!LiveSpecEquals

<1> DEFINE LNext == \E self \in Acceptor, c \in Ballot :
/\ BallotAction(self, c)
/\ (self \in Q) => (c =< b)

<1>2. Spec /\ LiveAssumption!(Q, b) => [][LNext]_vars
<2>1. /\ TypeOK
/\ [Next]_vars
/\ [\A self \in Q : \A c \in Ballot : (c > b) => ~ BallotAction(self, c)]_vars
=> [LNext]_vars
BY NextDef DEF LNext, Ballot
<2>2. /\ []TypeOK
/\ [][Next]_vars
/\ [][\A self \in Q : \A c \in Ballot : (c > b) => ~ BallotAction(self, c)]_vars
=> [][LNext]_vars
BY <2>1, PTL
<2>3. QED
BY <2>2, VT2, Isa DEF Spec, VInv

<1> DEFINE LNInv1 == \A a \in Q : maxBal[a] =< b
LInv1  == VInv /\ LNInv1

<1>3. LInv1 /\ [LNext]_vars => LInv1'
<2>1. SUFFICES ASSUME LInv1, [LNext]_vars
PROVE  LInv1'
OBVIOUS
<2>2. VInv'
BY <2>1, NextDef, InductiveInvariance DEF LInv1, VInv
<2>3. LNInv1'
BY <2>1, QA DEF BallotAction, IncreaseMaxBal, VoteFor, VInv, TypeOK, vars
<2>. QED
BY <2>2, <2>3

<1>4. \A a \in Q :
VInv /\ (maxBal[a] = b) /\ [LNext]_vars => VInv' /\ (maxBal'[a] = b)
<2>1. SUFFICES ASSUME NEW a \in Q,
VInv, maxBal[a] = b, [LNext]_vars
PROVE  VInv' /\ (maxBal'[a] = b)
OBVIOUS
<2>2. VInv'
BY <2>1, NextDef, InductiveInvariance DEF VInv
<2>3. maxBal'[a] = b
BY <2>1, QA DEF BallotAction, IncreaseMaxBal, VoteFor, VInv, TypeOK, Ballot, vars
<2>. QED
BY <2>2, <2>3

<1>5. Spec /\ LiveAssumption!(Q, b) =>
<>[](\A self \in Q : maxBal[self] = b)
<2>1. SUFFICES ASSUME NEW self \in Q
PROVE  Spec /\ LiveAssumption!(Q, b) => <>[](maxBal[self] = b)

PROOF OMITTED
<2> DEFINE P ==  LInv1 /\ ~(maxBal[self] = b)
QQ == LInv1 /\ (maxBal[self] = b)
A == BallotAction(self, b)
<2>2. [][LNext]_vars /\ WF_vars(A) => (LInv1 ~> QQ)
<3>1. P /\ [LNext]_vars => (P' \/ QQ')
BY <1>3
<3>2. P /\ <<LNext /\ A>>_vars => QQ'
<4>1. SUFFICES ASSUME LInv1, LNext, A
PROVE  QQ'
OBVIOUS
<4>2. LInv1'
BY <4>1, <1>3
<4>3. CASE IncreaseMaxBal(self, b)
BY <4>1, <4>2, <4>3, QA DEF IncreaseMaxBal, VInv, TypeOK
<4>4. CASE \E v \in Value : VoteFor(self, b, v)
BY <4>1, <4>2, <4>4, QA DEF VoteFor, VInv, TypeOK
<4>5. QED
BY <4>1, <4>3, <4>4 DEF BallotAction
<3>3. P => ENABLED <<A>>_vars
<4>1. (ENABLED <<A>>_vars) <=>
\E votesp, maxBalp:
/\ \/ /\ b > maxBal[self]
/\ maxBalp = [maxBal EXCEPT ![self] = b]
/\ votesp = votes
\/ \E v \in Value :
/\ maxBal[self] \leq b
/\ DidNotVoteIn(self, b)
/\ \A p \in Acceptor \ {self} :
\A w \in Value : VotedFor(p, b, w) => (w = v)
/\ SafeAt(b, v)
/\ votesp = [votes EXCEPT ![self] = votes[self]
\cup {<<b, v>>}]
/\ maxBalp = [maxBal EXCEPT ![self] = b]
/\ <<votesp, maxBalp>> # <<votes, maxBal>>

PROOF OMITTED
<4>. SUFFICES ASSUME P
PROVE \E votesp, maxBalp:
/\ b > maxBal[self]
/\ maxBalp = [maxBal EXCEPT ![self] = b]
/\ votesp = votes
/\ <<votesp, maxBalp>> # <<votes, maxBal>>
BY <4>1
<4> WITNESS votes, [maxBal EXCEPT ![self] = b]
<4>. QED  BY QA DEF VInv, TypeOK, Ballot
<3>. QED  BY <3>1, <3>2, <3>3, PTL
<2>3. QQ /\ [][LNext]_vars => []QQ
<3>1. QQ /\ [LNext]_vars => QQ'
BY <1>3, <1>4
<3>. QED  BY <3>1, PTL
<2>4. []QQ => [](maxBal[self] = b)
BY PTL
<2>5. LiveAssumption!(Q,b) => WF_vars(A)
BY Isa
<2>6. Spec => LInv1
<3>1. Init => VInv
BY InitImpliesInv
<3>2. Init => LNInv1
BY QA DEF Init, Ballot
<3>. QED  BY <3>1, <3>2 DEF Spec
<2>. QED
BY <2>2, <2>3, <2>4, <2>5, <2>6, <1>2, PTL

<1> DEFINE LNInv2 == \A a \in Q : maxBal[a] = b
LInv2  == VInv /\ LNInv2

<1>6. LInv2 /\ [LNext]_vars => LInv2'
BY <1>4, QuorumNonEmpty

<1>7. Spec /\ LiveAssumption!(Q, b) => <>[](chosen # {})
<2> DEFINE Voted(a) == \E v \in Value : VotedFor(a, b, v)
<2>1. Spec /\ LiveAssumption!(Q, b) => <>[]LInv2
<3>1. Spec /\ LiveAssumption!(Q,b) => <>[]LNInv2

PROOF OMITTED
<3>. QED  BY <3>1, VT2, PTL
<2>2. LInv2 /\ (\A a \in Q : Voted(a)) => (chosen # {})
<3>1. SUFFICES ASSUME LInv2,
\A a \in Q : Voted(a)
PROVE  chosen # {}
OBVIOUS
<3>2. \E v \in Value : \A a \in Q :  VotedFor(a, b, v)
<4>2. PICK a0 \in Q, v \in Value : VotedFor(a0, b, v)
BY <3>1, QuorumNonEmpty
<4>3. ASSUME NEW a \in Q
PROVE  VotedFor(a, b, v)
BY <3>1, <4>2, QA DEF VInv, VInv3
<4>4. QED
BY <4>3
<3>3. QED
BY <3>2 DEF chosen, ChosenIn
<2>3. Spec /\ LiveAssumption!(Q, b) => (\A a \in Q : <>[]Voted(a))
<3>1. SUFFICES ASSUME NEW self \in Q
PROVE  Spec /\ LiveAssumption!(Q, b) => <>[]Voted(self)

PROOF OMITTED
<3>2. Spec /\ LiveAssumption!(Q, b) => <>Voted(self)
<4>2. [][LNext]_vars /\ WF_vars(BallotAction(self, b))
=> ((LInv2 /\ ~Voted(self)) ~> LInv2 /\ Voted(self))
<5> DEFINE P == LInv2 /\ ~Voted(self)
QQ == LInv2 /\ Voted(self)
A == BallotAction(self, b)
<5>1. P /\ [LNext]_vars => (P' \/ QQ')
BY <1>6
<5>2. P /\ <<LNext /\ A>>_vars => QQ'
<6>1. SUFFICES ASSUME P,
LNext,
A
PROVE QQ'
OBVIOUS
<6>2. CASE \E v \in Value : VoteFor(self, b, v)
BY <6>1, <6>2, <5>1, QA, Zenon DEF VoteFor, Voted, VotedFor, LInv2, VInv, TypeOK
<6>3. CASE IncreaseMaxBal(self, b)
BY <6>1, <6>3 DEF IncreaseMaxBal, Ballot
<6>4. QED
BY <6>1, <6>2, <6>3 DEF BallotAction
<5>3. P => ENABLED <<A>>_vars
<6>1. SUFFICES ASSUME P
PROVE  ENABLED <<A>>_vars
OBVIOUS
<6>2. (ENABLED <<A>>_vars) <=>
\E votesp, maxBalp :
/\ \/ /\ b > maxBal[self]
/\ maxBalp = [maxBal EXCEPT ![self] = b]
/\ votesp = votes
\/ \E v \in Value :
/\ maxBal[self] \leq b
/\ DidNotVoteIn(self, b)
/\ \A p \in Acceptor \ {self} :
\A w \in Value : VotedFor(p, b, w) => (w = v)
/\ SafeAt(b, v)
/\ votesp = [votes EXCEPT ![self] = votes[self]
\cup {<<b, v>>}]
/\ maxBalp = [maxBal EXCEPT ![self] = b]
/\ <<votesp, maxBalp>> #  <<votes, maxBal>>

PROOF OMITTED
<6> SUFFICES
\E votesp, maxBalp:
/\ \E v \in Value :
/\ maxBal[self] \leq b
/\ DidNotVoteIn(self, b)
/\ \A p \in Acceptor \ {self} :
\A w \in Value : VotedFor(p, b, w) => (w = v)
/\ SafeAt(b, v)
/\ votesp = [votes EXCEPT ![self] = votes[self]
\cup {<<b, v>>}]
/\ maxBalp = [maxBal EXCEPT ![self] = b]
/\ <<votesp, maxBalp>> #  <<votes, maxBal>>
BY <6>2
<6> DEFINE someVoted == \E p \in Acceptor \ {self} :
\E w \in Value : VotedFor(p, b, w)
vp == CHOOSE p \in Acceptor \ {self} :
\E w \in Value : VotedFor(p, b, w)
vpval == CHOOSE w \in Value : VotedFor(vp, b, w)
<6>3. someVoted => /\ vp \in Acceptor
/\ vpval \in Value
/\ VotedFor(vp, b, vpval)
BY Zenon
<6> DEFINE v == IF someVoted THEN vpval
ELSE CHOOSE v \in Value : SafeAt(b, v)
<6>4. (v \in Value) /\ SafeAt(b, v)
BY <6>1, <6>3, VT4 DEF VInv, VInv2, Ballot
<6> DEFINE votesp == [votes EXCEPT ![self] = votes[self] \cup {<<b, v>>}]
maxBalp == [maxBal EXCEPT ![self] = b]
<6> WITNESS votesp, maxBalp
<6> SUFFICES /\ maxBal[self] \leq b
/\ DidNotVoteIn(self, b)
/\ \A p \in Acceptor \ {self} :
\A w \in Value : VotedFor(p, b, w) => (w = v)
/\ votesp # votes
BY <6>4, Zenon
<6>5. maxBal[self] \leq b
BY <6>1 DEF Ballot
<6>6. DidNotVoteIn(self, b)
BY <6>1 DEF Voted, DidNotVoteIn
<6>7. ASSUME NEW p \in Acceptor \ {self},
NEW w \in Value,
VotedFor(p, b, w)
PROVE  w = v
BY <6>7, <6>3, <6>1 DEF VInv, VInv3
<6>8. votesp # votes
<7>1. votesp[self] = votes[self] \cup {<<b, v>>}
BY <6>1, QA DEF LInv2, VInv, TypeOK
<7>2. \A w \in Value : <<b, w>> \notin votes[self]
BY <6>6 DEF DidNotVoteIn, VotedFor
<7>3. QED
BY <7>1, <7>2, <6>4, Zenon
<6>9. QED
BY <6>5, <6>6, <6>7, <6>8, Zenon
<5>4. QED
BY <5>1, <5>2, <5>3, PTL
<4>3. []LInv2 /\ ((LInv2 /\ ~Voted(self)) ~> LInv2 /\ Voted(self))
=> <>Voted(self)
BY PTL
<4>4. LiveAssumption!(Q, b) => WF_vars(BallotAction(self,b))
BY Isa
<4>. QED
BY <1>2, <2>1, <4>2, <4>3, <4>4, PTL
<3>3. Spec => [](Voted(self) => []Voted(self))
<4>1. (VInv /\ Voted(self)) /\ [Next]_vars => (VInv /\ Voted(self))'
<5> SUFFICES ASSUME VInv, Voted(self), [Next]_vars
PROVE  VInv' /\ Voted(self)'
OBVIOUS
<5>1. VInv'
BY InductiveInvariance
<5>2. Voted(self)'
<6> CASE vars' = vars
BY DEF vars, Voted, VotedFor
<6> CASE Next
<7>2. PICK a \in Acceptor, c \in Ballot : BallotAction(a, c)
BY NextDef DEF VInv
<7>3. CASE IncreaseMaxBal(a, c)
BY <7>3 DEF IncreaseMaxBal, Voted, VotedFor
<7>4. CASE \E v \in Value : VoteFor(a, c, v)
BY <7>4, QA DEF VInv, TypeOK, VoteFor, Voted, VotedFor
<7>5. QED
BY <7>2, <7>3, <7>4 DEF BallotAction
<6> QED
OBVIOUS
<5>3. QED
BY <5>1, <5>2
<4>3. QED
BY <4>1, VT2, PTL DEF Spec
<3>4. QED
BY <3>2, <3>3, PTL
<2>4. (\A a \in Q : <>[]Voted(a)) => <>[](\A a \in Q : Voted(a))

PROOF OMITTED
<2>. QED
BY <2>1, VT2, <2>2, <2>3, <2>4, PTL

<1>. QED
<2>1. Spec /\ LiveAssumption!(Q, b) => C!Spec /\ <>[](chosen # {})
BY VT3, <1>7, Isa
<2>2. Spec /\ LiveAssumption!(Q, b) => C!Spec /\ []<>(chosen # {})
BY <2>1, PTL
<2>. QED
BY <2>2, <1>1, Isa

===============================================================================
