---------------------------- MODULE BPConProof ------------------------------

EXTENDS Integers, FiniteSets, FiniteSetTheorems, TLAPS

----------------------------------------------------------------------------

CONSTANT Value

Ballot == Nat

None == CHOOSE v : v \notin Value
-----------------------------------------------------------------------------

CONSTANTS Acceptor,
FakeAcceptor,
ByzQuorum,

WeakQuorum

ByzAcceptor == Acceptor \cup FakeAcceptor

ASSUME BallotAssump == (Ballot \cup {-1}) \cap ByzAcceptor = {}

ASSUME BQA ==
/\ Acceptor \cap FakeAcceptor = {}
/\ \A Q \in ByzQuorum : Q \subseteq ByzAcceptor
/\ \A Q1, Q2 \in ByzQuorum : Q1 \cap Q2 \cap Acceptor # {}
/\ \A Q \in WeakQuorum : /\ Q \subseteq ByzAcceptor
/\ Q \cap Acceptor # {}

ASSUME BQLA ==
/\ \E Q \in ByzQuorum : Q \subseteq Acceptor
/\ \E Q \in WeakQuorum : Q \subseteq Acceptor
-----------------------------------------------------------------------------

1aMessage == [type : {"1a"},  bal : Ballot]

1bMessage ==

[type : {"1b"}, bal : Ballot,
mbal : Ballot \cup {-1}, mval : Value \cup {None},
m2av : SUBSET [val : Value, bal : Ballot],
acc : ByzAcceptor]

1cMessage ==

[type : {"1c"}, bal : Ballot, val : Value]

2avMessage ==

[type : {"2av"}, bal : Ballot, val : Value, acc : ByzAcceptor]

2bMessage == [type : {"2b"}, acc : ByzAcceptor, bal : Ballot, val : Value]

BMessage ==
1aMessage \cup 1bMessage \cup 1cMessage \cup 2avMessage \cup 2bMessage

LEMMA BMessageLemma ==
\A m \in BMessage :
/\ (m \in 1aMessage) <=>  (m.type = "1a")
/\ (m \in 1bMessage) <=>  (m.type = "1b")
/\ (m \in 1cMessage) <=>  (m.type = "1c")
/\ (m \in 2avMessage) <=>  (m.type = "2av")
/\ (m \in 2bMessage) <=>  (m.type = "2b")
<1>1. /\ \A m \in 1aMessage : m.type = "1a"
/\ \A m \in 1bMessage : m.type = "1b"
/\ \A m \in 1cMessage : m.type = "1c"
/\ \A m \in 2avMessage : m.type = "2av"
/\ \A m \in 2bMessage : m.type = "2b"
BY DEF 1aMessage, 1bMessage, 1cMessage, 2avMessage, 2bMessage
<1>2. QED
BY <1>1 DEF BMessage
-----------------------------------------------------------------------------

variables maxBal  = [a \in Acceptor |-> -1],
maxVBal = [a \in Acceptor |-> -1] ,
maxVVal = [a \in Acceptor |-> None] ,
2avSent = [a \in Acceptor |-> {}],
knowsSent = [a \in Acceptor |-> {}],
bmsgs = {}
define {
sentMsgs(type, bal) == {m \in bmsgs: m.type = type /\ m.bal = bal}

KnowsSafeAt(ac, b, v) ==

LET S == {m \in knowsSent[ac] : m.bal = b}
IN  \/ \E BQ \in ByzQuorum :
\A a \in BQ : \E m \in S : /\ m.acc = a
/\ m.mbal = -1
\/ \E c \in 0..(b-1):
/\ \E BQ \in ByzQuorum :
\A a \in BQ : \E m \in S : /\ m.acc = a
/\ m.mbal =< c
/\ (m.mbal = c) => (m.mval = v)
/\ \E WQ \in WeakQuorum :
\A a \in WQ :
\E m \in S : /\ m.acc = a
/\ \E r \in m.m2av : /\ r.bal >= c
/\ r.val = v
}

macro SendMessage(m) { bmsgs := bmsgs \cup {m} }
macro SendSetOfMessages(S) { bmsgs := bmsgs \cup S }

macro Phase1a() { SendMessage([type |-> "1a", bal |-> self]) }

macro Phase1b(b) {
when (b > maxBal[self]) /\ (sentMsgs("1a", b) # {}) ;
maxBal[self] := b ;
SendMessage([type |-> "1b", bal |-> b, acc |-> self, m2av |-> 2avSent[self],
mbal |-> maxVBal[self], mval |-> maxVVal[self]])
}

macro Phase1c() {
with (S \in SUBSET [type : {"1c"}, bal : {self}, val : Value]) {
SendSetOfMessages(S) }
}

macro Phase2av(b) {
when /\ maxBal[self] =< b
/\ \A r \in 2avSent[self] : r.bal < b ;

with (m \in {ms \in sentMsgs("1c", b) : KnowsSafeAt(self, b, ms.val)}) {
SendMessage([type |-> "2av", bal |-> b, val |-> m.val, acc |-> self]) ;
2avSent[self] :=  {r \in 2avSent[self] : r.val # m.val}
\cup {[val |-> m.val, bal |-> b]}
} ;
maxBal[self]  := b ;
}

macro Phase2b(b) {
when maxBal[self] =< b ;
with (v \in {vv \in Value :
\E Q \in ByzQuorum :
\A aa \in Q :
\E m \in sentMsgs("2av", b) : /\ m.val = vv
/\ m.acc = aa} ) {
SendMessage([type |-> "2b", acc |-> self, bal |-> b, val |-> v]) ;
maxVVal[self] := v ;
} ;
maxBal[self] := b ;
maxVBal[self] := b
}

macro LearnsSent(b) {
with (S \in SUBSET sentMsgs("1b", b)) {
knowsSent[self] := knowsSent[self] \cup S
}
}

macro FakingAcceptor() {
with ( m \in { mm \in 1bMessage \cup 2avMessage \cup 2bMessage :
mm.acc = self} ) {
SendMessage(m)
}
}

process (acceptor \in Acceptor) {
acc: while (TRUE) {
with (b \in Ballot) {either Phase1b(b) or Phase2av(b)
or Phase2b(b) or LearnsSent(b)}
}
}

process (leader \in Ballot) {
ldr: while (TRUE) {
either Phase1a() or Phase1c()
}
}

process (facceptor \in FakeAcceptor) {
facc : while (TRUE) { FakingAcceptor() }
}
}

Below is the TLA+ translation, as produced by the translator.  (Some
blank lines have been removed.)
**************************************************************************)

VARIABLES maxBal, maxVBal, maxVVal, 2avSent, knowsSent, bmsgs

sentMsgs(type, bal) == {m \in bmsgs: m.type = type /\ m.bal = bal}

KnowsSafeAt(ac, b, v) ==
LET S == {m \in knowsSent[ac] : m.bal = b}
IN  \/ \E BQ \in ByzQuorum :
\A a \in BQ : \E m \in S : /\ m.acc = a
/\ m.mbal = -1
\/ \E c \in 0..(b-1):
/\ \E BQ \in ByzQuorum :
\A a \in BQ : \E m \in S : /\ m.acc = a
/\ m.mbal =< c
/\ (m.mbal = c) => (m.mval = v)
/\ \E WQ \in WeakQuorum :
\A a \in WQ :
\E m \in S : /\ m.acc = a
/\ \E r \in m.m2av : /\ r.bal >= c
/\ r.val = v

vars == << maxBal, maxVBal, maxVVal, 2avSent, knowsSent, bmsgs >>

ProcSet == (Acceptor) \cup (Ballot) \cup (FakeAcceptor)

Init ==
/\ maxBal = [a \in Acceptor |-> -1]
/\ maxVBal = [a \in Acceptor |-> -1]
/\ maxVVal = [a \in Acceptor |-> None]
/\ 2avSent = [a \in Acceptor |-> {}]
/\ knowsSent = [a \in Acceptor |-> {}]
/\ bmsgs = {}

acceptor(self) == \E b \in Ballot:
\/ /\ (b > maxBal[self]) /\ (sentMsgs("1a", b) # {})
/\ maxBal' = [maxBal EXCEPT ![self] = b]
/\ bmsgs' = (bmsgs \cup {([type |-> "1b", bal |-> b, acc |-> self, m2av |-> 2avSent[self],
mbal |-> maxVBal[self], mval |-> maxVVal[self]])})
/\ UNCHANGED <<maxVBal, maxVVal, 2avSent, knowsSent>>
\/ /\ /\ maxBal[self] =< b
/\ \A r \in 2avSent[self] : r.bal < b
/\ \E m \in {ms \in sentMsgs("1c", b) : KnowsSafeAt(self, b, ms.val)}:
/\ bmsgs' = (bmsgs \cup {([type |-> "2av", bal |-> b, val |-> m.val, acc |-> self])})
/\ 2avSent' = [2avSent EXCEPT ![self] = {r \in 2avSent[self] : r.val # m.val}
\cup {[val |-> m.val, bal |-> b]}]
/\ maxBal' = [maxBal EXCEPT ![self] = b]
/\ UNCHANGED <<maxVBal, maxVVal, knowsSent>>
\/ /\ maxBal[self] =< b
/\ \E v \in {vv \in Value :
\E Q \in ByzQuorum :
\A aa \in Q :
\E m \in sentMsgs("2av", b) : /\ m.val = vv
/\ m.acc = aa}:
/\ bmsgs' = (bmsgs \cup {([type |-> "2b", acc |-> self, bal |-> b, val |-> v])})
/\ maxVVal' = [maxVVal EXCEPT ![self] = v]
/\ maxBal' = [maxBal EXCEPT ![self] = b]
/\ maxVBal' = [maxVBal EXCEPT ![self] = b]
/\ UNCHANGED <<2avSent, knowsSent>>
\/ /\ \E S \in SUBSET sentMsgs("1b", b):
knowsSent' = [knowsSent EXCEPT ![self] = knowsSent[self] \cup S]
/\ UNCHANGED <<maxBal, maxVBal, maxVVal, 2avSent, bmsgs>>

leader(self) == /\ \/ /\ bmsgs' = (bmsgs \cup {([type |-> "1a", bal |-> self])})
\/ /\ \E S \in SUBSET [type : {"1c"}, bal : {self}, val : Value]:
bmsgs' = (bmsgs \cup S)
/\ UNCHANGED << maxBal, maxVBal, maxVVal, 2avSent, knowsSent >>

facceptor(self) == /\ \E m \in { mm \in 1bMessage \cup 2avMessage \cup 2bMessage :
mm.acc = self}:
bmsgs' = (bmsgs \cup {m})
/\ UNCHANGED << maxBal, maxVBal, maxVVal, 2avSent,
knowsSent >>

Next == (\E self \in Acceptor: acceptor(self))
\/ (\E self \in Ballot: leader(self))
\/ (\E self \in FakeAcceptor: facceptor(self))

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

Phase1b(self, b) ==
/\ (b > maxBal[self]) /\ (sentMsgs("1a", b) # {})
/\ maxBal' = [maxBal EXCEPT ![self] = b]
/\ bmsgs' = bmsgs \cup {[type  |-> "1b", bal |-> b, acc |-> self,
m2av |-> 2avSent[self],
mbal |-> maxVBal[self], mval |-> maxVVal[self]]}
/\ UNCHANGED <<maxVBal, maxVVal, 2avSent, knowsSent>>

Phase2av(self, b) ==
/\ maxBal[self] =< b
/\ \A r \in 2avSent[self] : r.bal < b
/\ \E m \in {ms \in sentMsgs("1c", b) : KnowsSafeAt(self, b, ms.val)}:
/\ bmsgs' = bmsgs \cup
{[type |-> "2av", bal |-> b, val |-> m.val, acc |-> self]}
/\ 2avSent' = [2avSent EXCEPT
![self] = {r \in 2avSent[self] : r.val # m.val}
\cup {[val |-> m.val, bal |-> b]}]
/\ maxBal' = [maxBal EXCEPT ![self] = b]
/\ UNCHANGED <<maxVBal, maxVVal, knowsSent>>

Phase2b(self, b) ==
/\ maxBal[self] =< b
/\ \E v \in {vv \in Value :
\E Q \in ByzQuorum :
\A a \in Q :
\E m \in sentMsgs("2av", b) : /\ m.val = vv
/\ m.acc = a }:
/\ bmsgs' = (bmsgs \cup
{[type |-> "2b", acc |-> self, bal |-> b, val |-> v]})
/\ maxVVal' = [maxVVal EXCEPT ![self] = v]
/\ maxBal' = [maxBal EXCEPT ![self] = b]
/\ maxVBal' = [maxVBal EXCEPT ![self] = b]
/\ UNCHANGED <<2avSent, knowsSent>>

LearnsSent(self, b) ==
/\ \E S \in SUBSET sentMsgs("1b", b):
knowsSent' = [knowsSent EXCEPT ![self] = knowsSent[self] \cup S]
/\ UNCHANGED <<maxBal, maxVBal, maxVVal, 2avSent, bmsgs>>

Phase1a(self) ==
/\ bmsgs' = (bmsgs \cup {[type |-> "1a", bal |-> self]})
/\ UNCHANGED << maxBal, maxVBal, maxVVal, 2avSent, knowsSent >>

Phase1c(self) ==
/\ \E S \in SUBSET [type : {"1c"}, bal : {self}, val : Value]:
bmsgs' = (bmsgs \cup S)
/\ UNCHANGED << maxBal, maxVBal, maxVVal, 2avSent, knowsSent >>

FakingAcceptor(self) ==
/\ \E m \in { mm \in 1bMessage \cup 2avMessage \cup 2bMessage : mm.acc = self} :
bmsgs' = (bmsgs \cup {m})
/\ UNCHANGED << maxBal, maxVBal, maxVVal, 2avSent, knowsSent >>
-----------------------------------------------------------------------------

LEMMA NextDef ==
Next <=> \/ \E self \in Acceptor :
\E b \in Ballot : \/ Phase1b(self, b)
\/ Phase2av(self, b)
\/ Phase2b(self,b)
\/ LearnsSent(self, b)
\/ \E self \in Ballot : \/ Phase1a(self)
\/ Phase1c(self)
\/ \E self \in FakeAcceptor : FakingAcceptor(self)
<1>1. \A self : acceptor(self) <=> NextDef!2!1!(self)
BY  DEF acceptor, Phase1b,  Phase2av, Phase2b, LearnsSent
<1>2. \A self : leader(self) <=> NextDef!2!2!(self)
BY DEF leader, Phase1a, Phase1c
<1>3. \A self : facceptor(self) <=> NextDef!2!3!(self)
BY DEF facceptor, FakingAcceptor
<1>4. QED
BY <1>1, <1>2, <1>3, Zenon
DEF Next, acceptor, leader, facceptor
-----------------------------------------------------------------------------

Quorum == {S \cap Acceptor : S \in ByzQuorum}

THEOREM QuorumTheorem ==
/\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}
/\ \A Q \in Quorum : Q \subseteq Acceptor
BY BQA DEF Quorum

msgsOfType(t) == {m \in bmsgs : m.type = t }

acceptorMsgsOfType(t) == {m \in msgsOfType(t) : m.acc \in  Acceptor}

1bRestrict(m) == [type |-> "1b", acc |-> m.acc, bal |-> m.bal,
mbal |-> m.mbal, mval |-> m.mval]

1bmsgs == { 1bRestrict(m) : m \in acceptorMsgsOfType("1b") }

1cmsgs == {m \in msgsOfType("1c") :
\E a \in Acceptor : KnowsSafeAt(a, m.bal, m.val)}

2amsgs == {m \in [type : {"2a"}, bal : Ballot, val : Value] :
\E Q \in Quorum :
\A a \in Q :
\E m2av \in acceptorMsgsOfType("2av") :
/\ m2av.acc = a
/\ m2av.bal = m.bal
/\ m2av.val = m.val }

msgs == msgsOfType("1a") \cup 1bmsgs \cup 1cmsgs \cup 2amsgs
\cup acceptorMsgsOfType("2b")

MaxBallot(S) ==
IF S = {} THEN -1
ELSE CHOOSE mb \in S : \A x \in S : mb  >= x

LEMMA FiniteSetHasMax ==
\A S \in SUBSET Int :
IsFiniteSet(S) /\ (S # {}) => \E max \in S : \A x \in S : max >= x
<1>. DEFINE P(S) == S \subseteq Int /\ S # {} =>
\E max \in S : \A x \in S : max >= x
<1>1. P({})
OBVIOUS
<1>2. ASSUME NEW T, NEW x, P(T)
PROVE  P(T \cup {x})
BY <1>2
<1>3. \A S : IsFiniteSet(S) => P(S)
<2>. HIDE DEF P
<2>. QED  BY <1>1, <1>2, FS_Induction, IsaM("blast")
<1>. QED  BY <1>3, Zenon

THEOREM MaxBallotProp  ==
ASSUME NEW S \in SUBSET (Ballot \cup {-1}),
IsFiniteSet(S)
PROVE  IF S = {} THEN MaxBallot(S) = -1
ELSE /\ MaxBallot(S) \in S
/\ \A x \in S : MaxBallot(S) >= x
<1>1. CASE S = {}
BY <1>1 DEF MaxBallot
<1>2. CASE S # {}
<2>. PICK mb \in S : \A x \in S : mb >= x
BY <1>2,  FiniteSetHasMax DEF Ballot
<2>. QED  BY <1>2 DEF MaxBallot
<1>. QED  BY <1>1, <1>2

LEMMA MaxBallotLemma1 ==
ASSUME NEW S \in SUBSET (Ballot \cup {-1}),
IsFiniteSet(S),
NEW y \in S, \A x \in S : y >= x
PROVE  y = MaxBallot(S)
<1>1. /\ MaxBallot(S) \in S
/\ MaxBallot(S) >= y
BY MaxBallotProp
<1>2 /\ y \in Ballot \cup {-1}
/\ y >= MaxBallot(S)
BY MaxBallotProp
<1>3. MaxBallot(S) \in Int /\ y \in Int
BY <1>1, <1>2, Isa DEF Ballot
<1>. QED  BY <1>1, <1>2, <1>3

LEMMA MaxBallotLemma2 ==
ASSUME NEW S \in SUBSET (Ballot \cup {-1}),
NEW T \in SUBSET (Ballot \cup {-1}),
IsFiniteSet(S), IsFiniteSet(T)
PROVE  MaxBallot(S \cup T) = IF MaxBallot(S) >= MaxBallot(T)
THEN MaxBallot(S) ELSE MaxBallot(T)
<1>1. /\ MaxBallot(S) \in Ballot \cup {-1}
/\ MaxBallot(T) \in Ballot \cup {-1}
BY MaxBallotProp
<1>. S \cup T \subseteq Int
BY DEF Ballot
<1>2. CASE MaxBallot(S) >= MaxBallot(T)
<2>. SUFFICES ASSUME T # {}
PROVE  MaxBallot(S \cup T) = MaxBallot(S)
BY <1>2, Zenon
<2>1. /\ MaxBallot(T) \in T
/\ \A x \in T : MaxBallot(T) >= x
BY MaxBallotProp
<2>2. CASE S = {}
<3>1. MaxBallot(S) = -1
BY <2>2 DEF MaxBallot
<3>2. MaxBallot(T) = -1
BY <3>1, <1>2, <1>1 DEF Ballot
<3>. QED  BY <2>2, <3>1, <3>2, <2>1, MaxBallotLemma1, FS_Union
<2>3. CASE S # {}
<3>1. /\ MaxBallot(S) \in S
/\ \A x \in S : MaxBallot(S) >= x
BY <2>3, MaxBallotProp
<3>2. /\ MaxBallot(S) \in S \cup T
/\ \A x \in S \cup T : MaxBallot(S) >= x
BY <3>1, <2>1, <1>2
<3>. QED  BY <3>2, MaxBallotLemma1, FS_Union, Zenon
<2>. QED  BY <2>2, <2>3
<1>3. CASE ~(MaxBallot(S) >= MaxBallot(T))
<2>. SUFFICES ASSUME S # {}
PROVE  MaxBallot(S \cup T) = MaxBallot(T)
BY <1>3
<2>1. /\ MaxBallot(S) \in S
/\ \A x \in S : MaxBallot(S) >= x
BY MaxBallotProp
<2>2. /\ MaxBallot(S) < MaxBallot(T)
/\ MaxBallot(T) # -1
BY <1>3, <1>1 DEF Ballot
<2>3. /\ MaxBallot(T) \in T
/\ \A x \in T : MaxBallot(T) >= x
BY <2>2, MaxBallotProp
<2>4. /\ MaxBallot(T) \in S \cup T
/\ \A x \in S \cup T : MaxBallot(T) >= x
BY <2>3, <2>2, <2>1
<2>. QED  BY <2>4, MaxBallotLemma1, FS_Union, Zenon
<1>. QED  BY <1>2, <1>3

1bOr2bMsgs == {m \in bmsgs : m.type \in {"1b", "2b"}}

PmaxBal == [a \in Acceptor |->
MaxBallot({m.bal : m \in {ma \in 1bOr2bMsgs :
ma.acc = a}})]

LEMMA PmaxBalLemma1 ==
ASSUME NEW m ,
bmsgs' = bmsgs \cup {m},
m.type # "1b" /\ m.type # "2b"
PROVE  PmaxBal' = PmaxBal
BY Zenon DEF PmaxBal, 1bOr2bMsgs

LEMMA PmaxBalLemma2 ==
ASSUME NEW m,
bmsgs' = bmsgs \cup {m},
NEW a \in Acceptor,
m.acc # a
PROVE  PmaxBal'[a] = PmaxBal[a]
BY DEF PmaxBal, 1bOr2bMsgs

P == INSTANCE PConProof WITH maxBal <- PmaxBal
-----------------------------------------------------------------------------

TypeOK == /\ maxBal  \in [Acceptor -> Ballot \cup {-1}]
/\ 2avSent \in [Acceptor -> SUBSET [val : Value, bal : Ballot]]
/\ maxVBal \in [Acceptor -> Ballot \cup {-1}]
/\ maxVVal \in [Acceptor -> Value \cup {None}]
/\ knowsSent \in [Acceptor -> SUBSET 1bMessage]
/\ bmsgs \subseteq BMessage

bmsgsFinite == IsFiniteSet(1bOr2bMsgs)

LEMMA FiniteMsgsLemma ==
ASSUME NEW m, bmsgsFinite, bmsgs' = bmsgs \cup {m}
PROVE  bmsgsFinite'
BY FS_AddElement DEF bmsgsFinite, 1bOr2bMsgs

1bInv1 == \A m \in bmsgs  :
/\ m.type = "1b"
/\ m.acc \in Acceptor
=> \A r \in m.m2av :
[type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs

1bInv2 == \A m1, m2 \in bmsgs  :
/\ m1.type = "1b"
/\ m2.type = "1b"
/\ m1.acc \in Acceptor
/\ m1.acc = m2.acc
/\ m1.bal = m2.bal
=> m1 = m2

2avInv1 == \A m1, m2 \in bmsgs :
/\ m1.type = "2av"
/\ m2.type = "2av"
/\ m1.acc \in Acceptor
/\ m1.acc = m2.acc
/\ m1.bal = m2.bal
=> m1 = m2

2avInv2 == \A m \in bmsgs :
/\ m.type = "2av"
/\ m.acc \in Acceptor
=> \E r \in 2avSent[m.acc] : /\ r.val = m.val
/\ r.bal >= m.bal

2avInv3 == \A m \in bmsgs :
/\ m.type = "2av"
/\ m.acc \in Acceptor
=> [type |-> "1c", bal |-> m.bal, val |-> m.val] \in msgs

maxBalInv == \A m \in bmsgs :
/\ m.type \in {"1b", "2av", "2b"}
/\ m.acc \in Acceptor
=> m.bal =< maxBal[m.acc]

accInv == \A a \in Acceptor :
\A r \in 2avSent[a] :
/\ r.bal =< maxBal[a]
/\ [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs

knowsSentInv == \A a \in Acceptor : knowsSent[a] \subseteq msgsOfType("1b")

Inv ==
TypeOK /\ bmsgsFinite /\ 1bInv1 /\ 1bInv2 /\ maxBalInv  /\ 2avInv1 /\ 2avInv2
/\ 2avInv3 /\ accInv /\ knowsSentInv
-----------------------------------------------------------------------------

LEMMA PMaxBalLemma3 ==
ASSUME TypeOK,
bmsgsFinite,
NEW a \in Acceptor
PROVE  LET S == {m.bal : m \in {ma \in bmsgs :
/\ ma.type \in {"1b", "2b"}
/\ ma.acc = a}}
IN  /\ IsFiniteSet(S)
/\ S \in SUBSET Ballot
<1> DEFINE T == {ma \in bmsgs : /\ ma.type \in {"1b", "2b"}
/\ ma.acc = a}
S == {m.bal : m \in T}
<1>1. IsFiniteSet(S)
<2>1. IsFiniteSet(T)
BY FS_Subset DEF bmsgsFinite, 1bOr2bMsgs
<2>. QED
BY <2>1, FS_Image, Isa
<1>. QED  BY <1>1, BMessageLemma DEF 1bMessage, 2bMessage, TypeOK

LEMMA PmaxBalLemma4 ==
ASSUME TypeOK,
maxBalInv,
bmsgsFinite,
NEW a \in Acceptor
PROVE  PmaxBal[a] =< maxBal[a]
<1> DEFINE SM == {ma \in bmsgs : /\ ma.type \in {"1b", "2b"}
/\ ma.acc = a}
S  == {ma.bal : ma \in SM}
<1>1. PmaxBal[a] = MaxBallot(S)
BY DEF PmaxBal, 1bOr2bMsgs
<1>2. /\ IsFiniteSet(S)
/\ S \in SUBSET Ballot
BY PMaxBalLemma3
<1>3. \A b \in S : b =< maxBal[a]
BY DEF maxBalInv
<1>4. CASE S = {}
<2>1. PmaxBal[a] = -1
BY <1>2,  <1>1, <1>4, MaxBallotProp
<2>. QED
BY <2>1 DEF Ballot, TypeOK
<1>5. CASE S # {}
<2>1. MaxBallot(S) \in S
BY <1>2,  <1>5,  MaxBallotProp, Zenon
<2>2. QED
BY <1>1, <1>3, <2>1
<1>6. QED
BY <1>4, <1>5

LEMMA PmaxBalLemma5 ==
ASSUME TypeOK, bmsgsFinite, NEW a \in Acceptor
PROVE  PmaxBal[a] \in Ballot \cup {-1}
BY PMaxBalLemma3, MaxBallotProp DEF PmaxBal, 1bOr2bMsgs

-----------------------------------------------------------------------------

LEMMA PNextDef == P!NextDef!:
<1>1. P!QA
BY QuorumTheorem
<1>2. P!BallotAssump
BY BallotAssump DEF Ballot, P!Ballot, ByzAcceptor
<1>3. QED
BY P!NextDef, <1>1, <1>2, NoSetContainsEverything

KSet(a, b) == {m \in knowsSent[a] : m.bal = b}
KS1(S) == \E BQ \in ByzQuorum : \A a \in BQ :
\E m \in S : m.acc = a /\ m.mbal = -1
KS2(v,b,S) == \E c \in 0 .. (b-1) :
/\ \E BQ \in ByzQuorum : \A a \in BQ :
\E m \in S : /\ m.acc = a
/\ m.mbal =< c
/\ (m.mbal = c) => (m.mval = v)
/\ \E WQ \in WeakQuorum : \A a \in WQ :
\E m \in S : /\ m.acc = a
/\ \E r \in m.m2av : /\ r.bal >= c
/\ r.val = v

LEMMA KnowsSafeAtDef ==
\A a, b, v :
/\ KnowsSafeAt(a, b, v) <=> KS1(KSet(a,b)) \/ KS2(v, b, KSet(a, b))
/\ KnowsSafeAt(a, b, v)' <=> KS1(KSet(a,b)') \/ KS2(v, b, KSet(a, b)')
BY DEF KnowsSafeAt, KSet, KS1, KS2

LEMMA MsgsTypeLemma ==
\A m \in msgs : /\ (m.type = "1a") <=> (m \in msgsOfType("1a"))
/\ (m.type = "1b") <=> (m \in 1bmsgs)
/\ (m.type = "1c") <=> (m \in 1cmsgs)
/\ (m.type = "2a") <=> (m \in 2amsgs)
/\ (m.type = "2b") <=> (m \in acceptorMsgsOfType("2b"))
BY DEF msgsOfType, 1bmsgs, 1bRestrict, 1cmsgs, 2amsgs, acceptorMsgsOfType, msgs

LEMMA MsgsTypeLemmaPrime ==
\A m \in msgs' : /\ (m.type = "1a") <=> (m \in msgsOfType("1a")')
/\ (m.type = "1b") <=> (m \in 1bmsgs')
/\ (m.type = "1c") <=> (m \in 1cmsgs')
/\ (m.type = "2a") <=> (m \in 2amsgs')
/\ (m.type = "2b") <=> (m \in acceptorMsgsOfType("2b")')
<1>1. MsgsTypeLemma'
BY MsgsTypeLemma, PTL
<1>. QED
BY <1>1

LEMMA MsgsLemma ==
TypeOK =>
/\ \A self \in Acceptor, b \in Ballot :
Phase1b(self, b) =>
msgs' = msgs \cup
{[type |-> "1b", acc |-> self, bal |-> b,
mbal |-> maxVBal[self], mval |-> maxVVal[self]]}
/\ \A self \in Acceptor, b \in Ballot :
Phase2av(self, b) =>
\/ msgs' = msgs
\/ \E v \in Value :
/\ [type |-> "1c", bal |-> b, val |-> v] \in msgs
/\ msgs' = msgs \cup {[type |-> "2a", bal |-> b, val |-> v]}
/\ \A self \in Acceptor, b \in Ballot :
Phase2b(self, b) =>
\E v \in Value :
/\ \E Q \in ByzQuorum :
\A a \in Q :
\E m \in sentMsgs("2av", b) : /\ m.val = v
/\ m.acc = a
/\ msgs' = msgs \cup
{[type |-> "2b", acc |-> self, bal |-> b, val |-> v]}
/\ bmsgs' = bmsgs \cup
{[type |-> "2b", acc |-> self, bal |-> b, val |-> v]}
/\ maxVVal' = [maxVVal EXCEPT ![self] = v]
/\ \A self \in Acceptor, b \in Ballot :
LearnsSent(self, b) =>
\E S \in SUBSET {m \in msgsOfType("1c") : m.bal = b} :
msgs' = msgs \cup S
/\ \A self \in Ballot :
Phase1a(self) =>
msgs' = msgs \cup {[type |-> "1a", bal |-> self]}
/\ \A self \in Ballot :
Phase1c(self) =>
\E S \in SUBSET [type : {"1c"}, bal : {self}, val : Value]:
/\ \A m \in S :
\E a \in Acceptor : KnowsSafeAt(a, m.bal, m.val)
/\ msgs' = msgs \cup S
/\ \A self \in FakeAcceptor : FakingAcceptor(self) => msgs' = msgs
<1> HAVE TypeOK

<1>1. ASSUME NEW self \in Acceptor, NEW b \in Ballot, Phase1b(self,b)
PROVE  msgs' = msgs \cup
{[type |-> "1b", acc |-> self, bal |-> b,
mbal |-> maxVBal[self], mval |-> maxVVal[self]]}
<2> DEFINE m == [type |-> "1b", acc |-> self, bal |-> b,
m2av |-> 2avSent[self],
mbal |-> maxVBal[self], mval |-> maxVVal[self]]
<2>1. bmsgs' = bmsgs \cup {m} /\ knowsSent' = knowsSent
BY <1>1 DEF Phase1b
<2>a. /\ msgsOfType("1a")' =  msgsOfType("1a")
/\ 1bmsgs' = 1bmsgs \cup {1bRestrict(m)}
/\ 1cmsgs' = 1cmsgs
/\ 2amsgs' = 2amsgs
/\ acceptorMsgsOfType("2b")' = acceptorMsgsOfType("2b")
BY <2>1 DEF msgsOfType, 1bmsgs, acceptorMsgsOfType, KnowsSafeAt, 1cmsgs, 2amsgs
<2>. QED
BY <2>a DEF msgs, 1bRestrict

<1>2. ASSUME NEW self \in Acceptor, NEW b \in Ballot, Phase2av(self,b)
PROVE  \/ msgs' = msgs
\/ \E v \in Value :
/\ [type |-> "1c", bal |-> b, val |-> v] \in msgs
/\ msgs' = msgs \cup {[type |-> "2a", bal |-> b, val |-> v]}
<2>1. PICK m \in sentMsgs("1c", b) :
/\ KnowsSafeAt(self, b, m.val)
/\ bmsgs' = bmsgs \cup
{[type |-> "2av", bal |-> b, val |-> m.val, acc |-> self]}
BY <1>2 DEF Phase2av
<2>2. m = [type |-> "1c", bal |-> b, val |-> m.val]
BY BMessageLemma DEF sentMsgs, TypeOK, 1cMessage
<2> DEFINE ma == [type |-> "2a", bal |-> b, val |-> m.val]
mb == [type |-> "2av", bal |-> b, val |-> m.val, acc |-> self]
<2>3. SUFFICES ASSUME msgs' # msgs
PROVE  /\ m \in msgs
/\ msgs' = msgs \cup {ma}
BY <2>2, BMessageLemma DEF sentMsgs, TypeOK, 1cMessage
<2>4. m \in msgs
BY <2>1, <2>2 DEF sentMsgs, 1cmsgs, msgsOfType, msgs
<2>5. msgs' = msgs \cup {ma}
<3>1. knowsSent' = knowsSent
BY <1>2 DEF Phase2av
<3>2. /\ msgsOfType("1a")' = msgsOfType("1a")
/\ 1bmsgs' = 1bmsgs
/\ 1cmsgs' = 1cmsgs
/\ acceptorMsgsOfType("2b")' = acceptorMsgsOfType("2b")
BY <2>1, <3>1 DEF msgsOfType, 1bmsgs, 1bRestrict, acceptorMsgsOfType, KnowsSafeAt, 1cmsgs
<3>. QED
BY <3>1, <3>2, <2>1, <2>3 DEF msgs, 2amsgs, msgsOfType, acceptorMsgsOfType
<2>6. QED
BY <2>4, <2>5

<1>3. ASSUME NEW self \in Acceptor, NEW b \in Ballot, Phase2b(self, b)
PROVE  \E v \in Value :
/\ \E Q \in ByzQuorum :
\A a \in Q :
\E m \in sentMsgs("2av", b) : /\ m.val = v
/\ m.acc = a
/\ msgs' = msgs \cup
{[type |-> "2b", acc |-> self, bal |-> b, val |-> v]}
/\ bmsgs' = bmsgs \cup
{[type |-> "2b", acc |-> self, bal |-> b, val |-> v]}
/\ maxVVal' = [maxVVal EXCEPT ![self] = v]
<2>1. PICK v \in Value :
/\ \E Q \in ByzQuorum :
\A a \in Q :
\E m \in sentMsgs("2av", b) : /\ m.val = v
/\ m.acc = a
/\ bmsgs' = bmsgs \cup
{[type |-> "2b", acc |-> self, bal |-> b, val |-> v]}
/\ maxVVal' = [maxVVal EXCEPT ![self] = v]
/\ knowsSent' = knowsSent
BY <1>3, Zenon DEF Phase2b
<2> DEFINE bm == [type |-> "2b", acc |-> self, bal |-> b, val |-> v]
<2>2. /\ msgsOfType("1a")' = msgsOfType("1a")
/\ 1bmsgs' = 1bmsgs
/\ 1cmsgs' = 1cmsgs
/\ 2amsgs' = 2amsgs
/\ acceptorMsgsOfType("2b")' = acceptorMsgsOfType("2b") \cup {bm}
BY <2>1 DEF msgsOfType, 1bmsgs, 1bRestrict, 1cmsgs, KnowsSafeAt, 2amsgs, acceptorMsgsOfType
<2>4. msgs' = msgs \cup {bm}
BY <2>2 DEF msgs
<2>. QED
BY <2>1, <2>4, Zenon

<1>4. ASSUME NEW self \in Acceptor, NEW b \in Ballot, LearnsSent(self, b)
PROVE  \E S \in SUBSET {m \in msgsOfType("1c") : m.bal = b} : msgs' = msgs \cup S
<2>1. /\ msgsOfType("1a")' = msgsOfType("1a")
/\ 1bmsgs' = 1bmsgs
/\ 2amsgs' = 2amsgs
/\ acceptorMsgsOfType("2b")' = acceptorMsgsOfType("2b")
BY <1>4 DEF LearnsSent, msgsOfType, 1bmsgs, 1bRestrict, 2amsgs, acceptorMsgsOfType
<2>. /\ 1cmsgs \subseteq 1cmsgs'
/\ 1cmsgs' \ 1cmsgs \in SUBSET {m \in msgsOfType("1c") : m.bal = b}
<3>1. bmsgs' = bmsgs
BY <1>4 DEF LearnsSent
<3>2. PICK S \in SUBSET sentMsgs("1b", b):
knowsSent' = [knowsSent EXCEPT ![self] = knowsSent[self] \cup S]
BY <1>4, Zenon DEF LearnsSent
<3>3. ASSUME NEW m \in 1cmsgs
PROVE  m \in 1cmsgs'
BY <3>1, <3>2 DEF TypeOK, KnowsSafeAt, 1cmsgs, msgsOfType
<3>4. ASSUME NEW m \in 1cmsgs', m \notin 1cmsgs
PROVE  m \in msgsOfType("1c") /\ m.bal = b
<4>1. m \in msgsOfType("1c")
BY <3>1 DEF 1cmsgs, msgsOfType
<4>2. PICK a \in Acceptor : KnowsSafeAt(a, m.bal, m.val)'
BY DEF 1cmsgs
<4>3. ~KnowsSafeAt(a, m.bal, m.val)
BY <3>4, <4>1 DEF 1cmsgs
<4>4. \A aa \in Acceptor, bb \in Ballot :
\A mm \in KSet(aa, bb)' :
mm \notin KSet(aa, bb) => bb = b
BY <1>4, <3>2 DEF TypeOK, LearnsSent, TypeOK, sentMsgs, KSet
<4>5. m.bal \in Ballot
BY <4>1, BMessageLemma DEF 1cMessage, msgsOfType, TypeOK
<4>6. CASE KS1(KSet(a,m.bal)') /\ ~KS1(KSet(a,m.bal))
BY <4>6, <4>1, <4>4, <4>5 DEF KS1
<4>7. CASE KS2(m.val, m.bal, KSet(a, m.bal)') /\ ~KS2(m.val, m.bal, KSet(a, m.bal))
BY <4>7, <4>1, <4>4, <4>5 DEF KS2
<4> QED
BY <4>6, <4>7, <4>2, <4>3, KnowsSafeAtDef
<3>5. QED
BY <3>3, <3>4
<2>. WITNESS 1cmsgs' \ 1cmsgs \in SUBSET {m \in msgsOfType("1c") : m.bal = b}
<2>. QED
BY <2>1 DEF msgs

<1>5. ASSUME NEW self \in Ballot, Phase1a(self)
PROVE  msgs' = msgs \cup {[type |-> "1a", bal |-> self]}
BY <1>5 DEF Phase1a, msgs, msgsOfType, 1bmsgs, 1bRestrict, 1cmsgs, KnowsSafeAt,
2amsgs, acceptorMsgsOfType

<1>6. ASSUME NEW  self \in Ballot, Phase1c(self)
PROVE  \E S \in SUBSET [type : {"1c"}, bal : {self}, val : Value]:
/\ \A m \in S :
\E a \in Acceptor : KnowsSafeAt(a, m.bal, m.val)
/\ msgs' = msgs \cup S
<2>1. PICK S \in SUBSET [type : {"1c"}, bal : {self}, val : Value] :
/\ bmsgs' = bmsgs \cup S
/\ knowsSent' = knowsSent
BY <1>6 DEF Phase1c
<2> DEFINE SS == {m \in S : \E a \in Acceptor : KnowsSafeAt(a, m.bal, m.val)}
<2> SUFFICES msgs' = msgs \cup SS
BY <2>1, Zenon
<2>2. /\ msgsOfType("1a")' = msgsOfType("1a")
/\ 1bmsgs' = 1bmsgs
/\ 1cmsgs' = 1cmsgs \cup SS
/\ 2amsgs' = 2amsgs
/\ acceptorMsgsOfType("2b")' = acceptorMsgsOfType("2b")
BY <2>1 DEF msgsOfType, 1bmsgs, 1bRestrict, 1cmsgs, KnowsSafeAt, 2amsgs, acceptorMsgsOfType
<2>3. QED
BY <2>2 DEF msgs

<1>7. ASSUME NEW  self \in FakeAcceptor, FakingAcceptor(self)
PROVE  msgs' = msgs
BY <1>7, BQA DEF FakingAcceptor, msgs, 1bMessage, 2avMessage, 2bMessage,
msgsOfType, 1cmsgs, KnowsSafeAt, 1bmsgs, 2amsgs, acceptorMsgsOfType, msgsOfType

<1>9. QED
BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, Zenon

-----------------------------------------------------------------------------

THEOREM Invariance == Spec => []Inv
<1>1. Init => Inv
BY FS_EmptySet DEF Init, Inv, TypeOK, bmsgsFinite, 1bOr2bMsgs, 1bInv1, 1bInv2,
maxBalInv, 2avInv1, 2avInv2, 2avInv3, accInv, knowsSentInv

<1>2. Inv /\ [Next]_vars => Inv'
<2> SUFFICES ASSUME Inv, [Next]_vars
PROVE Inv'
OBVIOUS
<2>1. ASSUME NEW self \in Acceptor,
NEW b \in Ballot,
\/ Phase1b(self, b)
\/ Phase2av(self, b)
\/ Phase2b(self,b)
\/ LearnsSent(self, b)
PROVE  Inv'
<3>1. CASE Phase1b(self, b)
<4> DEFINE mb == [type  |-> "1b", bal |-> b, acc |-> self,
m2av |-> 2avSent[self],
mbal |-> maxVBal[self], mval |-> maxVVal[self]]
mc == [type |-> "1b", acc |-> self, bal |-> b,
mbal |-> maxVBal[self], mval |-> maxVVal[self]]
<4>1. msgs' = msgs \cup {mc}
BY <3>1, MsgsLemma DEF Inv
<4>2. TypeOK'
BY <3>1 DEF Inv, TypeOK, BMessage, 1bMessage, ByzAcceptor, Phase1b
<4>3. bmsgsFinite'
BY <3>1, FiniteMsgsLemma, Zenon DEF Inv, bmsgsFinite, Phase1b
<4>4. 1bInv1'
BY <3>1, <4>1, IsaT(100) DEF Phase1b, 1bInv1, Inv, accInv
<4>5. 1bInv2'
BY <3>1 DEF Phase1b, 1bInv2, Inv, maxBalInv, TypeOK, 1bMessage, Ballot
<4>6. maxBalInv'
BY <3>1, BMessageLemma DEF Phase1b, maxBalInv, Ballot, Inv, TypeOK,
1bMessage, 2avMessage, 2bMessage
<4>7. 2avInv1'
BY <3>1 DEF Phase1b, Inv, 2avInv1
<4>8. 2avInv2'
BY <3>1 DEF Phase1b, Inv, 2avInv2
<4>9. 2avInv3'
BY <3>1, <4>1 DEF Phase1b, Inv, 2avInv3
<4>10. accInv'
<5> SUFFICES ASSUME NEW a \in Acceptor,
NEW r \in 2avSent[a]
PROVE  /\ r.bal =< maxBal'[a]
/\ [type |-> "1c", bal |-> r.bal, val |-> r.val]
\in msgs'
BY <3>1, Zenon DEF accInv, Phase1b
<5> [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs'
BY <3>1, MsgsLemma DEF Inv, accInv
<5> QED
BY <3>1 DEF Phase1b, Inv, Ballot, TypeOK, accInv
<4>11. knowsSentInv'
BY <3>1 DEF Phase1b, Inv, knowsSentInv, msgsOfType
<4>12. QED
BY <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10, <4>11 DEF Inv
<3>2. CASE Phase2av(self, b)
<4>1. PICK mc \in sentMsgs("1c", b) :
/\ KnowsSafeAt(self, b, mc.val)
/\ bmsgs' = bmsgs \cup
{[type |-> "2av", bal |-> b,
val |-> mc.val, acc |-> self]}
/\ 2avSent' = [2avSent EXCEPT
![self] = {r \in 2avSent[self] : r.val # mc.val}
\cup {[val |-> mc.val, bal |-> b]}]
BY <3>2, Zenon DEF Phase2av
<4>2. mc = [type |-> "1c", bal |-> mc.bal, val |-> mc.val]
BY <4>1, BMessageLemma DEF sentMsgs, Inv, TypeOK, 1cMessage
<4> DEFINE mb == [type |-> "2av", bal |-> b,
val |-> mc.val, acc |-> self]
mmc(v) == [type |-> "1c", bal |-> b, val |-> v]
ma(v) == [type |-> "2a", bal |-> b, val |-> v]
<4>3. \/ msgs' = msgs
\/ \E v \in Value :
/\ mmc(v) \in msgs
/\ msgs' = msgs \cup {ma(v)}
BY <3>2, MsgsLemma, Zenon DEF Inv
<4>4. msgs \subseteq msgs'
BY <4>3, Zenon
<4>5. TypeOK'
BY <3>2, <4>1, BMessageLemma
DEF sentMsgs, Inv, TypeOK, 1cMessage, Phase2av, 2avMessage, ByzAcceptor, BMessage
<4>6. bmsgsFinite'
BY <4>1, FiniteMsgsLemma, Zenon DEF Inv, bmsgsFinite
<4>7. 1bInv1'
BY <3>2, <4>1, <4>3, IsaT(100) DEF Phase2av, 1bInv1, Inv
<4>8. 1bInv2'
BY <4>1 DEF Inv, 1bInv2
<4>9. maxBalInv'
BY <3>2, <4>1, BMessageLemma
DEF Phase2av, maxBalInv, Ballot, Inv, TypeOK, 1bMessage, 2avMessage, 2bMessage
<4>10. 2avInv1'
BY <3>2, <4>1 DEF Phase2av, Inv, 2avInv1, 2avInv2, TypeOK, 1bMessage, Ballot
<4>11. 2avInv2'
<5>1. SUFFICES ASSUME NEW m \in bmsgs',
2avInv2!(m)!1
PROVE  \E r \in 2avSent'[m.acc] : /\ r.val = m.val
/\ r.bal >= m.bal
BY DEF 2avInv2
<5>2. CASE m.acc = self
<6>1. CASE m = mb
BY <4>1, <6>1, Isa DEF Inv, TypeOK, Ballot
<6>2. CASE m # mb
<7>1. m \in bmsgs
BY <4>1, <6>2
<7>2. PICK r \in 2avSent[m.acc] : /\ r.val = m.val
/\ r.bal >= m.bal
BY <5>1, <7>1 DEF Inv, 2avInv2
<7>3. CASE r.val = mc.val
<8>. DEFINE rr == [val |-> mc.val, bal |-> b]
<8>. rr \in 2avSent'[m.acc]
BY <4>1, <5>2 DEF Inv, TypeOK
<8>. WITNESS rr \in 2avSent'[m.acc]
<8>. QED
BY <7>2, <7>3, <5>2, <5>1, <3>2, BMessageLemma
DEF Phase2av, Inv, TypeOK, accInv, Ballot, 2avMessage
<7>4. CASE r.val # mc.val
BY <7>2, <4>1, <5>2, <7>4 DEF Inv, TypeOK
<7>5. QED
BY <7>3, <7>4
<6>3. QED
BY <6>1, <6>2
<5>3. CASE m.acc # self
BY <5>3, <5>1, <4>1, BMessageLemma DEF Inv, TypeOK, 2avInv2, 2avMessage
<5>4. QED
BY <5>2, <5>3
<4>12. 2avInv3'
BY <4>1, <4>2, <4>4 DEF Inv, 2avInv3, sentMsgs, msgs, 1cmsgs, msgsOfType
<4>13. accInv'
<5>1. SUFFICES ASSUME NEW a \in Acceptor,
NEW r \in 2avSent'[a]
PROVE  /\ r.bal =< maxBal'[a]
/\ [type |-> "1c", bal |-> r.bal, val |-> r.val]
\in msgs'
BY Zenon DEF accInv
<5>2. CASE r \in 2avSent[a]
BY <5>2, <4>4, <4>5, <3>2 DEF Phase2av, Inv, TypeOK, accInv, Ballot
<5>3. CASE r \notin 2avSent[a]
BY <5>3, <3>2, <4>1, <4>2, <4>4
DEF Phase2av, Inv, TypeOK, sentMsgs, msgsOfType, msgs, 1cmsgs, Ballot
<5>4. QED
BY <5>2, <5>3
<4>14. knowsSentInv'
BY <3>2, <4>1 DEF Phase2av, Inv, knowsSentInv, msgsOfType
<4>15. QED
BY <4>5, <4>6, <4>7, <4>8, <4>9, <4>10, <4>11, <4>12, <4>13, <4>14 DEF Inv
<3>3. CASE Phase2b(self, b)
<4>1. PICK v \in Value :
/\ \E Q \in ByzQuorum :
\A a \in Q :
\E m \in sentMsgs("2av", b) : /\ m.val = v
/\ m.acc = a
/\ msgs' = msgs \cup
{[type |-> "2b", acc |-> self, bal |-> b, val |-> v]}
/\ bmsgs' = (bmsgs \cup
{[type |-> "2b", acc |-> self, bal |-> b, val |-> v]})
/\ maxVVal' = [maxVVal EXCEPT ![self] = v]
BY <3>3, MsgsLemma DEF Inv
<4> DEFINE mb == [type |-> "2b", acc |-> self, bal |-> b, val |-> v]
<4>2. TypeOK'
BY <3>3, <4>1 DEF Phase2b, Inv, TypeOK, BMessage, 2bMessage, ByzAcceptor
<4>3. bmsgsFinite'
BY <4>1, FiniteMsgsLemma, Zenon DEF Inv, bmsgsFinite
<4>4. 1bInv1'
BY <4>1, Isa DEF Inv, 1bInv1
<4>5. 1bInv2'
BY <4>1 DEF Inv, 1bInv2
<4>6. maxBalInv'
BY <3>3, <4>1, <4>2, BMessageLemma
DEF Phase2b, Inv, maxBalInv, TypeOK, Ballot, 1bMessage, 2avMessage, 2bMessage
<4>7. 2avInv1'
BY <4>1 DEF Inv, 2avInv1
<4>8. 2avInv2'
BY <3>3, <4>1 DEF Phase2b, Inv, TypeOK, 2avInv2
<4>9. 2avInv3'
BY <4>1 DEF Inv, 2avInv3
<4>10. accInv'
<5> SUFFICES ASSUME NEW a \in Acceptor,
NEW r \in 2avSent[a]
PROVE  /\ r.bal =< maxBal'[a]
/\ [type |-> "1c", bal |-> r.bal, val |-> r.val]
\in msgs'
BY <3>3, Zenon DEF accInv, Phase2b
<5> [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs'
BY <3>3, MsgsLemma DEF Inv, accInv
<5> QED
BY <3>3 DEF Phase2b, Inv, Ballot, TypeOK, accInv
<4>11. knowsSentInv'
BY <3>3, <4>1 DEF Phase2b, Inv, knowsSentInv, msgsOfType
<4>12. QED
BY <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10, <4>11 DEF Inv
<3>4. CASE LearnsSent(self, b)
<4>1. PICK MS : /\ MS \subseteq {m \in msgsOfType("1c") : m.bal = b}
/\ msgs' = msgs \cup MS
BY <3>4, MsgsLemma, Zenon DEF Inv
<4>2. PICK S :
/\ S \subseteq sentMsgs("1b", b)
/\ knowsSent' =
[knowsSent EXCEPT ![self] = knowsSent[self] \cup S]
BY <3>4, Zenon DEF LearnsSent
<4>3. TypeOK'
BY <3>4, <4>2, BMessageLemma DEF Inv, TypeOK, sentMsgs, LearnsSent
<4>4. bmsgsFinite'
BY <3>4 DEF LearnsSent, Inv, bmsgsFinite, 1bOr2bMsgs
<4>5. 1bInv1'
BY <3>4, <4>1, Zenon DEF LearnsSent, Inv, 1bInv1
<4>6. 1bInv2'
BY <3>4 DEF LearnsSent, Inv, 1bInv2
<4>7. maxBalInv'
BY <3>4 DEF LearnsSent, Inv, maxBalInv
<4>8. 2avInv1'
BY <3>4 DEF LearnsSent, Inv, 2avInv1
<4>9. 2avInv2'
BY <3>4 DEF LearnsSent, Inv, 2avInv2
<4>10. 2avInv3'
BY <3>4, <4>1 DEF LearnsSent, Inv, 2avInv3
<4>11. accInv'
BY <3>4, <4>1, Zenon DEF LearnsSent, Inv, accInv
<4>12. knowsSentInv'
BY <3>4, <4>2 DEF LearnsSent, Inv, TypeOK, knowsSentInv, sentMsgs, msgsOfType
<4>13. QED
BY <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10, <4>11, <4>12 DEF Inv
<3>5. QED
BY <2>1, <3>1, <3>2, <3>3, <3>4
<2>2. ASSUME NEW self \in Ballot,
\/ Phase1a(self)
\/ Phase1c(self)
PROVE  Inv'
<3>1. CASE Phase1a(self)
<4> DEFINE ma == [type |-> "1a", bal |-> self]
<4>1. msgs' = msgs \cup {ma}
BY <3>1, MsgsLemma DEF Inv
<4>2. TypeOK'
BY <3>1 DEF Phase1a, Inv, TypeOK, BMessage, 1aMessage
<4>3. bmsgsFinite'
BY <3>1, FiniteMsgsLemma, Zenon DEF Inv, bmsgsFinite, Phase1a
<4>4. 1bInv1'
BY <3>1, <4>1, Isa DEF Phase1a, Inv, 1bInv1
<4>5. 1bInv2'
BY <3>1 DEF Phase1a, Inv, 1bInv2
<4>6. maxBalInv'
BY <3>1 DEF Phase1a, Inv, maxBalInv
<4>7. 2avInv1'
BY <3>1 DEF Phase1a, Inv, 2avInv1
<4>8. 2avInv2'
BY <3>1 DEF Phase1a, Inv, 2avInv2
<4>9. 2avInv3'
BY <3>1, <4>1 DEF Phase1a, Inv, 2avInv3
<4>10. accInv'
BY <3>1, <4>1, Zenon DEF Phase1a, Inv, accInv
<4>11. knowsSentInv'
BY <3>1 DEF Inv, knowsSentInv, msgsOfType, Phase1a
<4>12. QED
BY <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10, <4>11 DEF Inv
<3>2. CASE Phase1c(self)
<4>1. PICK S : /\ S \in SUBSET [type : {"1c"}, bal : {self}, val : Value]
/\ bmsgs' = bmsgs \cup S
BY <3>2 DEF Phase1c
<4>2. PICK MS :
/\ MS \in SUBSET [type : {"1c"}, bal : {self}, val : Value]
/\ \A m \in MS :
\E a \in Acceptor : KnowsSafeAt(a, m.bal, m.val)
/\ msgs' = msgs \cup MS
BY <3>2, MsgsLemma DEF Inv
<4>3. TypeOK'
BY <3>2, <4>1 DEF Phase1c, Inv, TypeOK, BMessage, 1cMessage
<4>4. bmsgsFinite'
BY <4>1 DEF Inv, bmsgsFinite, 1bOr2bMsgs
<4>5. 1bInv1'
BY <3>2, <4>2, Zenon DEF Phase1c, Inv, 1bInv1
<4>6. 1bInv2'
BY <4>1 DEF Inv, 1bInv2
<4>7. maxBalInv'
BY <3>2 DEF Phase1c, Inv, maxBalInv
<4>8. 2avInv1'
BY <4>1 DEF Inv, 2avInv1
<4>9. 2avInv2'
BY <3>2 DEF Phase1c, Inv, 2avInv2
<4>10. 2avInv3'
BY <3>2, <4>2 DEF Phase1c, Inv, 2avInv3
<4>11. accInv'
BY <3>2, <4>2, Zenon DEF Phase1c, Inv, accInv
<4>12. knowsSentInv'
BY <3>2 DEF Inv, knowsSentInv, msgsOfType, Phase1c
<4>13. QED
BY <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10, <4>11, <4>12 DEF Inv
<3>3. QED
BY <3>1, <3>2, <2>2
<2>3. ASSUME NEW self \in FakeAcceptor,
FakingAcceptor(self)
PROVE  Inv'
<3>1. PICK m \in 1bMessage \cup 2avMessage \cup 2bMessage :
/\ m.acc \notin Acceptor
/\ bmsgs' = bmsgs \cup {m}
BY <2>3, BQA DEF FakingAcceptor
<3>2. msgs' = msgs
BY <2>3, MsgsLemma DEF Inv
<3>3. TypeOK'
BY <2>3, <3>1 DEF Inv, TypeOK, BMessage, FakingAcceptor
<3>4. bmsgsFinite'
BY <3>1, FiniteMsgsLemma DEF Inv, TypeOK
<3>5. 1bInv1'
BY <3>1, <3>2, Zenon DEF Inv, 1bInv1
<3>6. 1bInv2'
BY <3>1 DEF Inv, 1bInv2
<3>7. maxBalInv'
BY <2>3, <3>1 DEF Inv, maxBalInv, FakingAcceptor
<3>8. 2avInv1'
BY <3>1 DEF Inv, 2avInv1
<3>9. 2avInv2'
BY <2>3, <3>1 DEF Inv, 2avInv2, FakingAcceptor
<3>10. 2avInv3'
BY <3>1, <3>2 DEF Inv, 2avInv3
<3>11. accInv'
BY <2>3, <3>2, Zenon DEF Inv, accInv, FakingAcceptor
<3>12. knowsSentInv'
BY <2>3, <3>1 DEF Inv, knowsSentInv, msgsOfType, FakingAcceptor
<3>13. QED
BY <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10, <3>11, <3>12 DEF Inv
<2>4. ASSUME UNCHANGED vars
PROVE  Inv'
<3> USE UNCHANGED vars DEF Inv, vars
<3> msgs = msgs'
BY DEF msgs, msgsOfType, 1bmsgs, 1bRestrict, acceptorMsgsOfType, 1cmsgs,
KnowsSafeAt, 2amsgs
<3> QED
BY DEF TypeOK, bmsgsFinite, 1bOr2bMsgs, 1bInv1, 1bInv2,
maxBalInv, 2avInv1, 2avInv2, 2avInv3, accInv, knowsSentInv, msgsOfType
<2>5. QED
BY <2>1, <2>2, <2>3, <2>4, NextDef

<1>3. QED
BY <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------

AbstractSpec == P!Spec
THEOREM Spec => P!Spec
<1>1. Init => P!Init
<2>. HAVE Init
<2>1. MaxBallot({}) = -1
BY MaxBallotProp, FS_EmptySet
<2>2. P!Init!1 /\ P!Init!2 /\ P!Init!3
BY <2>1 DEF Init, PmaxBal, 1bOr2bMsgs, None, P!None
<2>3. msgs = {}
BY BQA DEF Init, msgsOfType, acceptorMsgsOfType, 1bmsgs, 1cmsgs, 2amsgs, Quorum, msgs
<2>4. QED
BY <2>2, <2>3 DEF  P!Init

<1>2. Inv /\ Inv' /\ [Next]_vars => [P!Next]_P!vars
<2> InvP == Inv'
<2> SUFFICES ASSUME Inv, InvP, Next
PROVE  P!TLANext \/ P!vars' = P!vars
<3> UNCHANGED vars => UNCHANGED P!vars
BY DEF vars, P!vars, PmaxBal, 1bOr2bMsgs, msgs, msgsOfType, acceptorMsgsOfType,
1bmsgs, 2amsgs, 1cmsgs, KnowsSafeAt
<3> QED
BY PNextDef DEF Inv, P!ProcSet, P!Init, Ballot, P!Ballot
<2> HIDE DEF InvP
<2>2. \A a \in Acceptor : PmaxBal[a] \in Ballot \cup {-1}
BY PMaxBalLemma3, MaxBallotProp DEF Inv, PmaxBal, 1bOr2bMsgs
<2>3. ASSUME NEW self \in Acceptor, NEW b \in Ballot,
Phase1b(self, b)
PROVE  P!TLANext \/ P!vars' = P!vars
<3>1. msgs' = msgs \cup {[type |-> "1b", acc |-> self, bal |-> b,
mbal |-> maxVBal[self], mval |-> maxVVal[self]]}
BY <2>3, MsgsLemma DEF Inv
<3>2. P!sentMsgs("1a", b) # {}
BY <2>3 DEF Phase1b, sentMsgs, msgsOfType, msgs, P!sentMsgs
<3>3. UNCHANGED <<maxVBal, maxVVal>>
BY <2>3 DEF Phase1b
<3>4. b > PmaxBal[self]
BY <2>2, <2>3, PmaxBalLemma4 DEF Phase1b, Inv, TypeOK, Ballot
<3>5. PmaxBal' = [PmaxBal EXCEPT ![self] = b]
<4> DEFINE m == [type  |-> "1b", bal |-> b, acc |-> self,
m2av |-> 2avSent[self],
mbal |-> maxVBal[self], mval |-> maxVVal[self]]
mA(a) == {ma \in bmsgs : /\ ma.type \in {"1b", "2b"}
/\ ma.acc = a}
S(a) == {ma.bal : ma \in mA(a)}
<4>1. bmsgs' = bmsgs \cup {m}
BY <2>3 DEF Phase1b
<4>2. mA(self)' = mA(self) \cup {m}
BY <4>1
<4>3. /\ PmaxBal = [a \in Acceptor |-> MaxBallot(S(a))]
/\ PmaxBal' = [a \in Acceptor |-> MaxBallot(S(a))']
BY DEF PmaxBal, 1bOr2bMsgs
<4> HIDE DEF mA
<4>4. S(self)' = S(self) \cup {b}
BY <4>2, Isa
<4>5. MaxBallot(S(self) \cup {b}) = b
<5> DEFINE SS == S(self) \cup {b}
<5>1. IsFiniteSet(S(self))
<6>. IsFiniteSet(mA(self))
BY FS_Subset DEF Inv, bmsgsFinite, mA, 1bOr2bMsgs
<6>. QED
BY FS_Image, Isa
<5>2. IsFiniteSet(SS)
BY <5>1, FS_AddElement
<5>3. S(self) \subseteq Ballot \cup {-1}
BY BMessageLemma DEF mA, Inv, TypeOK, 1bMessage, 2bMessage
<5>4. \A x \in SS : b >= x
BY <3>4, <4>3, <5>1, <5>3, MaxBallotProp, Z3T(10) DEF Ballot
<5>5. QED
BY <5>2, <5>3, <5>4, MaxBallotLemma1
<4>6. \A a \in Acceptor : a # self => S(a)' = S(a)
BY <4>1 DEF mA
<4>7. QED
BY <4>3, <4>4, <4>5, <4>6, Zenon DEF PmaxBal, 1bOr2bMsgs
<3>6. QED
BY <3>1, <3>2, <3>3, <3>4, <3>5, Zenon DEF P!TLANext, P!Ballot, Ballot, P!Phase1b
<2>4. ASSUME NEW self \in Acceptor, NEW b \in Ballot,
Phase2av(self, b)
PROVE  P!TLANext \/ P!vars' = P!vars
<3>1. PmaxBal' = PmaxBal
<4> DEFINE mm(m) == [type |-> "2av", bal |-> b,
val |-> m.val, acc |-> self]
<4>1. PICK m : bmsgs' = bmsgs \cup {mm(m)}
BY <2>4  DEF Phase2av
<4>2. mm(m).type = "2av"
OBVIOUS
<4> QED
BY <4>1, <4>2, PmaxBalLemma1, Zenon
<3>2. CASE msgs' = msgs
BY <3>1, <3>2, <2>4 DEF Phase2av, P!vars
<3>3. CASE /\ msgs' # msgs
/\ \E v \in Value :
/\ [type |-> "1c", bal |-> b, val |-> v] \in msgs
/\ msgs' = msgs \cup {[type |-> "2a", bal |-> b, val |-> v]}
<4>1. PICK v \in Value :
/\ [type |-> "1c", bal |-> b, val |-> v] \in msgs
/\ msgs' = msgs \cup {[type |-> "2a", bal |-> b, val |-> v]}
BY <3>3
<4>2. P!sentMsgs("2a", b) = {}
<5>1. SUFFICES ASSUME NEW m \in P!sentMsgs("2a", b)
PROVE  m = [type |-> "2a", bal |-> b, val |-> v]
BY <3>3, <4>1 DEF P!sentMsgs
<5>2. /\ m \in 2amsgs
/\ m.type = "2a"
/\ m.bal = b
BY MsgsTypeLemma DEF P!sentMsgs
<5>3. PICK Q \in Quorum :
\A a \in Q :
\E mav \in acceptorMsgsOfType("2av") :
/\ mav.acc = a
/\ mav.bal = b
/\ mav.val = m.val
BY <5>2 DEF 2amsgs
<5>4. PICK Q2 \in Quorum :
\A a \in Q2 :
\E m2av \in acceptorMsgsOfType("2av")' :
/\ m2av.acc = a
/\ m2av.bal = b
/\ m2av.val = v
BY <4>1, MsgsTypeLemmaPrime, Isa DEF 2amsgs
<5>5. PICK a \in Q \cap Q2 : a \in Acceptor
BY QuorumTheorem
<5>6. PICK mav \in acceptorMsgsOfType("2av") :
/\ mav.acc = a
/\ mav.bal = b
/\ mav.val = m.val
BY <5>3, <5>5
<5>7. PICK m2av \in acceptorMsgsOfType("2av")' :
/\ m2av.acc = a
/\ m2av.bal = b
/\ m2av.val = v
BY <5>4, <5>5
<5>8. mav \in acceptorMsgsOfType("2av")'
BY <2>4 DEF acceptorMsgsOfType, msgsOfType, Phase2av
<5>9. m.val = v
BY <5>5, <5>6, <5>7, <5>8 DEF 2avInv1, InvP, Inv, acceptorMsgsOfType, msgsOfType
<5>10. QED
BY <5>2, <5>9 DEF 2amsgs
<4>4. QED
BY <2>4, <3>1, <4>1, <4>2 DEF P!TLANext, P!Phase2a, Phase2av, Ballot, P!Ballot
<3>4.\/ msgs' = msgs
\/ (/\ msgs' # msgs
/\ \E v \in Value :
/\ [type |-> "1c", bal |-> b, val |-> v] \in msgs
/\ msgs' = msgs \cup {[type |-> "2a", bal |-> b, val |-> v]})
BY MsgsLemma, <2>4, Zenon DEF Inv
<3>5. QED
BY <3>2, <3>3, <3>4
<2>5. ASSUME NEW self \in Acceptor, NEW b \in Ballot,
Phase2b(self, b)
PROVE  P!TLANext \/ P!vars' = P!vars
<3>1. PmaxBal[self] =< b
<4>1. PmaxBal[self] =< maxBal[self]
BY PmaxBalLemma4 DEF Inv
<4>2. maxBal[self] =< b
BY <2>5 DEF Phase2b
<4>3. QED
BY <4>1, <4>2, PmaxBalLemma5 DEF Inv, TypeOK, Ballot
<3>2. PICK v \in Value :
/\ \E Q \in ByzQuorum :
\A a \in Q :
\E m \in sentMsgs("2av", b) : /\ m.val = v
/\ m.acc = a
/\ msgs' = msgs \cup
{[type |-> "2b", acc |-> self, bal |-> b, val |-> v]}
/\ bmsgs' = bmsgs \cup
{[type |-> "2b", acc |-> self, bal |-> b, val |-> v]}
/\ maxVVal' = [maxVVal EXCEPT ![self] = v]
BY <2>5, MsgsLemma DEF Inv
<3> DEFINE m == [type |-> "2a", bal |-> b, val |-> v]
m2b == [type |-> "2b", acc |-> self, bal |-> b, val |-> v]
<3>3. m \in P!sentMsgs("2a", b)
<4>1. PICK Q \in Quorum :
\A a \in Q :
\E mm \in sentMsgs("2av", b) : /\ mm.val = v
/\ mm.acc = a
BY <3>2, Isa DEF Quorum
<4>2. m \in 2amsgs
BY <4>1 DEF sentMsgs, Quorum, acceptorMsgsOfType, msgsOfType, 2amsgs
<4>3. QED
BY <4>2 DEF P!sentMsgs, msgs
<3>4. PmaxBal' = [PmaxBal EXCEPT ![self] = b]
<4>1.  ASSUME NEW a \in Acceptor,
a # self
PROVE  PmaxBal'[a] = PmaxBal[a]
BY <3>2, <4>1, PmaxBalLemma2, m2b.acc = self, Zenon
<4>2. PmaxBal'[self] = b
<5> DEFINE S == {mm.bal : mm \in {ma \in bmsgs :
/\ ma.type \in {"1b", "2b"}
/\ ma.acc = self}}
T == S \cup {m2b.bal}
<5>1. IsFiniteSet(S) /\ (S \in SUBSET Ballot)
BY PMaxBalLemma3 DEF Inv
<5>2. IsFiniteSet(T) /\ (T \in SUBSET Ballot)
BY <5>1, FS_AddElement
<5>3. PmaxBal[self] = MaxBallot(S)
BY DEF PmaxBal, 1bOr2bMsgs
<5>4. PmaxBal'[self] = MaxBallot(T)
BY <3>2, Zenon DEF PmaxBal, 1bOr2bMsgs
<5> HIDE DEF S
<5>5. CASE S = {}
<6> MaxBallot({b}) = b
BY FS_Singleton, MaxBallotLemma1, Isa DEF Ballot
<6> QED
BY <5>4, <5>5
<5>6. CASE S # {}
<6> \A bb \in T : b >= bb
BY <3>1, <5>1, <5>3, MaxBallotProp, PmaxBalLemma5 DEF Inv, Ballot
<6> QED
BY <5>2, <5>4, MaxBallotLemma1
<5>7. QED
BY <5>5, <5>6
<4>3. QED
BY <4>1, <4>2, Zenon DEF PmaxBal, 1bOr2bMsgs
<3>5. /\ maxVBal' = [maxVBal EXCEPT ![self] = b]
/\ maxVVal' = [maxVVal EXCEPT ![self] = m.val]
BY <2>5, <3>2, Zenon DEF Phase2b
<3>6. QED
BY <3>1, <3>2, <3>3, <3>4, <3>5, Zenon
DEF P!TLANext, P!Phase2b, Ballot, P!Ballot
<2>6. ASSUME NEW self \in Acceptor, NEW b \in Ballot,
LearnsSent(self, b)
PROVE  P!TLANext \/ P!vars' = P!vars
<3>1. PICK SM \in SUBSET {m \in msgsOfType("1c") : m.bal = b} :
msgs' = msgs \cup SM
BY <2>6, MsgsLemma DEF Inv
<3> DEFINE S == {m.val : m \in SM}
<3>2. S \in SUBSET Value
BY BMessageLemma DEF Inv, TypeOK, msgsOfType, 1cMessage
<3>3. msgs' = msgs \cup {[type |-> "1c", bal |-> b, val |-> v] : v \in S}
BY <3>1, BMessageLemma DEF Inv, TypeOK, msgsOfType, 1cMessage
<3>4. ASSUME NEW v \in S
PROVE  \E Q \in Quorum : P!ShowsSafeAt(Q, b, v)
<4>1. PICK ac \in Acceptor : KnowsSafeAt(ac, b, v)'
BY <3>1, MsgsTypeLemmaPrime DEF msgsOfType, 1cmsgs
<4>2. bmsgs' = bmsgs
BY <2>6 DEF LearnsSent
<4>  DEFINE Q(BQ) == BQ \cap Acceptor
SS == {m \in knowsSent'[ac] : m.bal = b}
SQ(BQ) == {1bRestrict(mm) :
mm \in {m \in SS : m.acc \in Q(BQ)}}
Q1b(BQ) == {m \in P!sentMsgs("1b", b) : m.acc \in Q(BQ)}
<4>3. ASSUME NEW BQ \in ByzQuorum,
\A a \in BQ : \E m \in SS : m.acc = a
PROVE  SQ(BQ) = Q1b(BQ)
<5>1. ASSUME NEW m \in P!sentMsgs("1b", b),
m.acc \in Q(BQ)
PROVE m \in SQ(BQ)
BY <4>2, <4>3, <5>1, MsgsTypeLemma
DEF P!sentMsgs, msgs, 1bmsgs, acceptorMsgsOfType, msgsOfType,
1bRestrict, InvP, Inv, knowsSentInv, 1bInv2
<5>2. ASSUME NEW m \in SS,
m.acc \in Q(BQ)
PROVE  1bRestrict(m) \in Q1b(BQ)
BY <4>2, <5>2
DEF InvP, Inv, knowsSentInv, msgsOfType, acceptorMsgsOfType, msgs,
1bmsgs, P!sentMsgs, 1bRestrict
<5>3. QED
BY <5>1, <5>2 DEF Q1b, SQ
<4>4. CASE KnowsSafeAt(ac, b, v)!1!1'
<5>1. PICK BQ \in ByzQuorum : KnowsSafeAt(ac, b, v)!1!1!(BQ)'
BY <4>4
<5>2. \A a \in Q(BQ) : \E m \in SQ(BQ) : /\ m.acc = a
/\ m.mbal = -1
BY <5>1, Isa DEF 1bRestrict
<5>3. \A m \in SQ(BQ) : m.mbal = -1
BY <4>2, <5>2
DEF InvP, Inv, knowsSentInv, msgsOfType, 1bRestrict, 1bInv2
<5>4. SQ(BQ) = Q1b(BQ)
BY  <4>3, <5>1
<5>5. Q(BQ) \in Quorum
BY DEF Quorum
<5> HIDE DEF SS, Q, SQ
<5> WITNESS Q(BQ) \in Quorum
<5>6. QED
BY <5>2, <5>3, <5>4 DEF P!ShowsSafeAt
<4>5. CASE KnowsSafeAt(ac, b, v)!1!2'
<5>1. PICK c \in 0..(b-1) : KnowsSafeAt(ac, b, v)!1!2!(c)'
BY <4>5
<5>2. PICK BQ \in ByzQuorum :
\A a \in BQ : \E m \in SS : /\ m.acc = a
/\ m.mbal =< c
/\ (m.mbal = c) => (m.mval = v)
BY <5>1
<5>3. SQ(BQ) = Q1b(BQ)
BY <5>2, <4>3
<5>4. P!ShowsSafeAt(Q(BQ), b, v)!1!1
<6>1. SUFFICES ASSUME NEW a \in Q(BQ)
PROVE \E m \in Q1b(BQ) : m.acc = a
OBVIOUS
<6>2. PICK m \in SS : m.acc = a
BY <5>2
<6>3. /\ 1bRestrict(m) \in SQ(BQ)
/\ 1bRestrict(m).acc = a
BY <6>2 DEF 1bRestrict
<6>. QED
BY <6>3, <5>3
<5>5. PICK m1c \in msgs :
/\ m1c = [type |-> "1c", bal |-> m1c.bal, val |-> v]
/\ m1c.bal >= c
/\ m1c.bal \in Ballot
<6>1. PICK WQ \in WeakQuorum :
\A a \in WQ : \E m \in SS : /\ m.acc = a
/\ \E r \in m.m2av :
/\ r.bal >= c
/\ r.val = v
BY <5>1
<6>2. PICK a \in WQ, m \in SS :
/\ a \in Acceptor
/\ m.acc = a
/\ \E r \in m.m2av : /\ r.bal >= c
/\ r.val = v
BY <6>1, BQA
<6>4. PICK r \in m.m2av : /\ r.bal >= c
/\ r.val = v
BY <6>2
<6>5. /\ m.bal = b
/\ m \in bmsgs
/\ m.type = "1b"
/\ r.bal \in Ballot
BY <4>2, <6>2, BMessageLemma
DEF Inv, InvP, TypeOK, 1bMessage, knowsSentInv, msgsOfType
<6>. QED
BY <6>2, <6>4, <6>5, Zenon DEF Inv, 1bInv1
<5>6. ASSUME NEW m \in Q1b(BQ)
PROVE  /\ m1c.bal \geq m.mbal
/\ (m1c.bal = m.mbal) => (m.mval = v)
<6>1. PICK mm \in SS : /\ mm.acc = m.acc
/\ mm.mbal =< c
/\ (mm.mbal = c) => (mm.mval = v)
BY <5>2
<6>2. PICK mm2 \in SS : /\ mm2.acc = m.acc
/\ m = 1bRestrict(mm2)
BY <5>3 DEF 1bRestrict
<6>3. /\ mm = mm2
/\ mm2.mbal \in Ballot \cup {-1}
BY <4>2, <6>1, <6>2, BMessageLemma
DEF Inv, InvP, TypeOK, knowsSentInv, 1bInv2, msgsOfType, 1bMessage
<6>. QED
<7> \A m1cbal, mmbal \in Ballot \cup {-1} :
mmbal =< c /\ m1cbal >= c => /\ m1cbal \geq mmbal
/\ mmbal = m1cbal => mmbal = c
BY DEF Ballot
<7> QED
BY <5>5, <6>1, <6>2, <6>3 DEF 1bRestrict
<5>7. P!ShowsSafeAt(Q(BQ), b, v)!1!2!2!(m1c)
BY <5>5, <5>6
<5>. QED
BY <5>4, <5>7, Isa DEF P!ShowsSafeAt, Quorum
<4>6. QED
BY <3>1, <4>1, <4>4, <4>5 DEF KnowsSafeAt
<3>6. QED
BY <2>6, <3>1, <3>2, <3>3, <3>4, Zenon
DEF LearnsSent, P!Phase1c, P!TLANext, Ballot, P!Ballot, PmaxBal, 1bOr2bMsgs
<2>7. ASSUME NEW self \in Ballot,
Phase1a(self)
PROVE  P!TLANext \/ P!vars' = P!vars
<3>1. msgs' = msgs \cup {[type |-> "1a", bal |-> self]}
BY <2>7, MsgsLemma DEF Inv
<3>2. UNCHANGED << PmaxBal, maxVBal, maxVVal >>
BY <2>7, Isa DEF Phase1a, PmaxBal, 1bOr2bMsgs
<3>. QED
BY <3>1, <3>2 DEF P!Phase1a, P!TLANext, Ballot, P!Ballot
<2>8. ASSUME NEW self \in Ballot,
Phase1c(self)
PROVE  P!TLANext \/ P!vars' = P!vars
<3>1. PICK SS \in SUBSET [type : {"1c"}, bal : {self}, val : Value] :
/\ \A m \in SS : \E a \in Acceptor : KnowsSafeAt(a, m.bal, m.val)
/\ msgs' = msgs \cup SS
BY <2>8, MsgsLemma DEF Inv
<3> DEFINE S == {m.val : m \in SS}
<3>2. SS = {[type |-> "1c", bal |-> self, val |-> v] : v \in S}
OBVIOUS
<3>3. ASSUME NEW v \in S
PROVE  \E Q \in Quorum : P!ShowsSafeAt(Q, self, v)
<4> DEFINE m == [type |-> "1c", bal |-> self, val |-> v]
<4>1. PICK a \in Acceptor : KnowsSafeAt(a, self, v)
BY <3>1
<4> DEFINE SK == {mm \in knowsSent[a] : mm.bal = self}
<4>2. ASSUME NEW BQ \in ByzQuorum,
\A ac \in BQ : \E mm \in SK : mm.acc = ac
PROVE  P!ShowsSafeAt(BQ \cap Acceptor, self, v)!1!1
<5> DEFINE Q == BQ \cap Acceptor
Q1b == {mm \in P!sentMsgs("1b", self) : mm.acc \in Q}
<5> SUFFICES ASSUME NEW ac \in BQ \cap Acceptor
PROVE  \E mm \in Q1b : mm.acc = ac
OBVIOUS
<5>1. PICK mm \in SK : mm.acc = ac
BY <4>2
<5>2. /\ 1bRestrict(mm) \in P!sentMsgs("1b", self)
/\ 1bRestrict(mm).acc = ac
BY <5>1 DEF acceptorMsgsOfType, msgsOfType, 1bmsgs, msgs, Inv, knowsSentInv,
1bRestrict, P!sentMsgs
<5>. QED
BY <5>2
<4>3. CASE KnowsSafeAt(a, self, v)!1!1
<5>1. PICK BQ \in ByzQuorum :
\A ac \in BQ : \E mm \in SK : /\ mm.acc = ac
/\ mm.mbal = -1
BY <4>3
<5> DEFINE Q == BQ \cap Acceptor
Q1b == {mm \in P!sentMsgs("1b", self) : mm.acc \in Q}
<5>2. P!ShowsSafeAt(Q, self, v)!1!1
BY <5>1, <4>2
<5>3. ASSUME NEW mm \in Q1b
PROVE  mm.mbal = -1
BY <5>1, MsgsTypeLemma
DEF P!sentMsgs, 1bmsgs, acceptorMsgsOfType, msgsOfType, 1bRestrict,
Inv, knowsSentInv, 1bInv2, 1bRestrict
<5>. QED
BY <5>2, <5>3, Zenon DEF P!ShowsSafeAt, Quorum
<4>4. CASE KnowsSafeAt(a, self, v)!1!2
<5>1. PICK c \in 0..(self-1) : KnowsSafeAt(a, self, v)!1!2!(c)
BY <4>4
<5>2. PICK BQ \in ByzQuorum : KnowsSafeAt(a, self, v)!1!2!(c)!1!(BQ)
BY <5>1
<5> DEFINE Q == BQ \cap Acceptor
Q1b == {mm \in P!sentMsgs("1b", self) : mm.acc \in Q}
<5>3. P!ShowsSafeAt(Q, self, v)!1!1
BY <5>2, <4>2
<5>4. PICK WQ \in WeakQuorum : KnowsSafeAt(a, self, v)!1!2!(c)!2!(WQ)
BY <5>1
<5>5. PICK ac \in WQ \cap Acceptor :
KnowsSafeAt(a, self, v)!1!2!(c)!2!(WQ)!(ac)
BY <5>4, BQA
<5>6. PICK mk \in SK : /\ mk.acc = ac
/\ \E r \in mk.m2av : /\ r.bal >= c
/\ r.val = v
BY <5>5
<5>7. PICK r \in mk.m2av : /\ r.bal >= c
/\ r.val = v
BY <5>6
<5> DEFINE mc == [type |-> "1c", bal |-> r.bal, val |-> v]
<5>9. mc \in msgs
BY <5>6, <5>7 DEF Inv, 1bInv1, knowsSentInv, msgsOfType
<5>10. ASSUME NEW mq \in  Q1b
PROVE  /\ mc.bal \geq mq.mbal
/\ (mc.bal = mq.mbal) => (mq.mval = v)
BY <5>2, <5>7, MsgsTypeLemma, BMessageLemma
DEF P!sentMsgs, 1bmsgs, acceptorMsgsOfType, msgsOfType, 1bRestrict,
Inv, TypeOK, 1bInv2, knowsSentInv, 1bMessage, Ballot
<5>11. QED
<6> Q \in Quorum
BY DEF Quorum
<6> WITNESS Q \in Quorum
<6> QED
BY <5>3, <5>9, <5>10 DEF P!ShowsSafeAt
<4>5. QED
BY <4>1, <4>3, <4>4 DEF KnowsSafeAt
<3>. QED
BY <2>8, <3>1, <3>2, <3>3, Zenon
DEF P!Phase1c, Phase1c, PmaxBal, 1bOr2bMsgs, P!TLANext, Ballot, P!Ballot
<2>9. ASSUME NEW self \in FakeAcceptor,
FakingAcceptor(self)
PROVE  P!TLANext \/ P!vars' = P!vars
<3>1. msgs' = msgs
BY <2>9, MsgsLemma DEF Inv
<3>2. PmaxBal' = PmaxBal
BY <2>9, BQA, Zenon DEF FakingAcceptor, PmaxBal, 1bOr2bMsgs
<3>. QED
BY <2>9, <3>1, <3>2 DEF P!vars, FakingAcceptor
<2>10. QED
BY  <2>3,  <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, NextDef

<1>3. QED
BY <1>1, <1>2, Invariance, PTL DEF Spec, P!Spec

-----------------------------------------------------------------------------

chosen == {v \in Value : \E BQ \in ByzQuorum, b \in Ballot :
\A a \in BQ : \E m \in msgs : /\ m.type = "2b"
/\ m.acc  = a
/\ m.bal  = b
/\ m.val  = v}

THEOREM chosen \subseteq P!chosen
BY Isa DEF chosen, P!chosen, Quorum, Ballot, P!Ballot

==============================================================================
