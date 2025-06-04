---------------------------- MODULE SumSequence ----------------------------

EXTENDS Integers, SequenceTheorems, SequencesExtTheorems, NaturalsInduction, TLAPS

CONSTANT Values
ASSUME  ValAssump == Values \subseteq Int

SeqSum(s) ==
LET SS[ss \in Seq(Int)] == IF ss = << >> THEN 0 ELSE ss[1] + SS[Tail(ss)]
IN  SS[s]

VARIABLES seq, sum, n, pc

vars == << seq, sum, n, pc >>

Init ==
/\ seq \in Seq(Values)
/\ sum = 0
/\ n = 1
/\ pc = "a"

a == /\ pc = "a"
/\ IF n =< Len(seq)
THEN /\ sum' = sum + seq[n]
/\ n' = n+1
/\ pc' = "a"
ELSE /\ pc' = "Done"
/\ UNCHANGED << sum, n >>
/\ seq' = seq

Terminating == pc = "Done" /\ UNCHANGED vars

Next == a
\/ Terminating

Spec == /\ Init /\ [][Next]_vars
/\ WF_vars(Next)

Termination == <>(pc = "Done")

-----------------------------------------------------------------------------

PCorrect == (pc = "Done") => (sum = SeqSum(seq))

-----------------------------------------------------------------------------

TypeOK == /\ seq \in Seq(Values)
/\ sum \in Int
/\ n \in 1..(Len(seq)+1)
/\ pc \in {"a", "Done"}

Inv == /\ TypeOK
/\ sum = SeqSum([i \in 1..(n-1) |-> seq[i]])
/\ (pc = "Done") => (n = Len(seq) + 1)

-----------------------------------------------------------------------------

LEMMA Lemma1 ==
\A s \in Seq(Int) :
SeqSum(s) = IF s = << >> THEN 0 ELSE s[1] + SeqSum(Tail(s))

THEOREM FrontDef  ==  \A S : \A s \in Seq(S) :
Front(s) = [i \in 1..(Len(s)-1) |-> s[i]]
BY DEF Front, SubSeq

LEMMA Lemma5  ==  \A s \in Seq(Int) :
(Len(s) > 0) =>
(SeqSum(s) =  SeqSum(Front(s)) + s[Len(s)])

-----------------------------------------------------------------------------
THEOREM Spec => []PCorrect
<1>1. Init => Inv
<2> SUFFICES ASSUME Init
PROVE  Inv
OBVIOUS
<2>1. TypeOK
BY Lemma1, ValAssump DEF Init, Inv, TypeOK
<2>2. sum = SeqSum([i \in 1..(n-1) |-> seq[i]])
<3>1. (n-1) = 0
BY DEF Init
<3>2. [i \in 1..0 |-> seq[i]] = << >>
OBVIOUS
<3>3. << >> \in Seq(Int)
OBVIOUS
<3>4. QED
BY <3>2, <3>1, <3>3, Lemma1 DEF Init
<2>3. (pc = "Done") => (n = Len(seq) + 1)
BY Lemma1, ValAssump DEF Init, Inv, TypeOK
<2>4. QED
BY <2>1, <2>2, <2>3 DEF Inv
<1>2. Inv /\ [Next]_vars => Inv'
<2> SUFFICES ASSUME Inv,
[Next]_vars
PROVE  Inv'
OBVIOUS
<2> USE ValAssump DEF Inv, TypeOK
<2>1. CASE a
<3>1. TypeOK'
<4>1. sum' \in Int
<5>1. CASE n <= Len(seq)
<6>. seq[n] \in Values
BY <5>1
<6>. QED  BY <5>1, <2>1 DEF a
<5>2. CASE ~(n <= Len(seq))
BY <5>2, <2>1 DEF a
<5>. QED  BY <5>1, <5>2
<4>. QED  BY <4>1, <2>1 DEF a
<3>2. (sum = SeqSum([i \in 1..(n-1) |-> seq[i]]))'
<4>1. CASE n > Len(seq)
<5> ~(n =< Len(seq))
BY <4>1 DEF Inv, TypeOK
<5> QED
BY <2>1, <4>1 DEF a, Inv, TypeOK
<4>2. CASE n \in 1..Len(seq)
<5> DEFINE curseq == [i \in 1..(n-1) |-> seq[i]]
s == curseq'
<5> SUFFICES sum' = SeqSum(s)
OBVIOUS
<5>1. /\ n'-1 = n
/\ Len(s) = n
/\ s[Len(s)] = seq[n]
BY <2>1, <4>2 DEF a, Inv, TypeOK
<5>2. s = [i \in 1..n |-> seq[i]]
BY <5>1, <2>1 DEF a
<5>3. sum' =  sum + seq[n]
BY <2>1, <4>2 DEF a
<5> HIDE DEF s
<5>4. SeqSum(s) = SeqSum([i \in 1..(Len(s)-1) |-> s[i]]) + s[Len(s)]
<6>1. \A S, T : S \subseteq T => Seq(S) \subseteq Seq(T)
OBVIOUS
<6>2. seq \in Seq(Int)
BY <6>1, ValAssump DEF Inv, TypeOK
<6>3. \A i \in 1..n : seq[i] \in Int
BY <6>2, <4>2
<6>4. s \in Seq(Int)
BY <6>3, <5>2, <4>2
<6>5. Front(s) = [i \in 1 .. Len(s)-1 |-> s[i]]
BY <5>1 DEF Front
<6> QED
BY <6>4, <6>5, <5>1, <4>2, Lemma5
<5>5. curseq = [i \in 1..(Len(s)-1) |-> s[i]]
BY <5>1, <5>2
<5>6. sum = SeqSum(curseq)
BY <2>1, <4>2, <5>5  DEF Inv, TypeOK, s
<5>7. QED
BY <5>1, <5>3, <5>4, <5>5, <5>6 DEF Inv, TypeOK, s
<4>3. QED
BY <4>1, <4>2 DEF Inv, TypeOK
<3>3. ((pc = "Done") => (n = Len(seq) + 1))'
BY <2>1 DEF a, Inv, TypeOK
<3>4. QED
BY <3>1, <3>2, <3>3 DEF Inv
<2>2. CASE UNCHANGED vars
BY <2>2 DEF Inv, TypeOK, vars
<2>3. QED
BY <2>1,  <2>2 DEF Next
<1>3. Inv => PCorrect
<2> SUFFICES ASSUME Inv,
pc = "Done"
PROVE  sum = SeqSum(seq)
BY DEF PCorrect
<2>1. seq = [i \in 1..Len(seq) |-> seq[i]]
BY DEF Inv, TypeOK
<2>2. QED
BY <2>1 DEF Inv, TypeOK
<1>4. QED
BY <1>1, <1>2, <1>3, PTL DEF Spec
-----------------------------------------------------------------------------

LEMMA Lemma1_Proof ==
\A s \in Seq(Int) :
SeqSum(s) = IF s = << >> THEN 0 ELSE s[1] + SeqSum(Tail(s))
<1> DEFINE DefSS(ssOfTailss, ss) == ss[1] + ssOfTailss
SS[ss \in Seq(Int)] ==
IF ss = << >> THEN 0 ELSE DefSS(SS[Tail(ss)], ss)
<1>1. TailInductiveDefHypothesis(SS, Int, 0, DefSS)
BY DEF TailInductiveDefHypothesis
<1>2. TailInductiveDefConclusion(SS, Int, 0, DefSS)
BY <1>1, TailInductiveDef
<1>3. SS = [ss \in Seq(Int) |-> IF ss = << >> THEN 0
ELSE ss[1] +  SS[Tail(ss)]]
BY <1>2 DEF TailInductiveDefConclusion
<1> QED
BY <1>3 DEF SeqSum

LEMMA Lemma2 ==
\A S : \A s \in Seq(S) :
Len(s) > 0 => /\ Tail(s) \in Seq(S)
/\ Front(s) \in Seq(S)
/\ Len(Tail(s)) = Len(s) - 1
/\ Len(Front(s)) = Len(s) - 1
<1> SUFFICES ASSUME NEW S,
NEW s \in Seq(S),
Len(s) > 0
PROVE  /\ Tail(s) \in Seq(S)
/\ Front(s) \in Seq(S)
/\ Len(Tail(s)) = Len(s) - 1
/\ Len(Front(s)) = Len(s) - 1
OBVIOUS
<1>1. Tail(s) \in Seq(S) /\ Len(Tail(s)) = Len(s) - 1
OBVIOUS
<1>2. Front(s) \in Seq(S) /\ Len(Front(s)) = Len(s) - 1
BY FrontDef
<1>3. QED
BY <1>1, <1>2

LEMMA Lemma2a ==
ASSUME NEW S, NEW s \in Seq(S), Len(s) > 1
PROVE  Tail(s) = [i \in 1..(Len(s) - 1) |-> s[i+1]]
<1>. DEFINE t == [i \in 1..(Len(s) - 1) |-> s[i+1]]
<1>1. Tail(s) \in Seq(S) /\ t \in Seq(S)
OBVIOUS
<1>2. Len(Tail(s)) = Len(t)
OBVIOUS
<1>3. \A i \in 1 .. Len(Tail(s)) : Tail(s)[i] = t[i]
OBVIOUS
<1>. QED  BY <1>1, <1>2, <1>3, SeqEqual, Zenon

LEMMA Lemma3 ==
\A S : \A s \in Seq(S) :
(Len(s) > 1) => (Tail(Front(s)) = Front(Tail(s)))
<1> SUFFICES ASSUME NEW S,
NEW s \in Seq(S),
Len(s) > 1
PROVE  Tail(Front(s)) = Front(Tail(s))
OBVIOUS
<1>1. Tail(Front(s)) = [i \in 1..(Len(s) - 2) |-> s[i+1]]
<2>1. /\ Front(s) = [i \in 1..(Len(s) - 1) |-> s[i]]
/\ Len(Front(s)) = Len(s) - 1
/\ Front(s) \in Seq(S)
/\ Len(s) \in Nat
BY FrontDef
<2>2. Len(Front(s)) > 0
BY <2>1
<2>3. Front(s) # << >>
BY <2>1, <2>2
<2>4. Tail(Front(s)) = [i \in 1..(Len(Front(s))-1) |-> Front(s)[i+1]]
BY <2>1, <2>3, Lemma2a
<2>5. \A i \in 0..(Len(s)-2) : Front(s)[i+1] = s[i+1]
BY <2>1
<2>6. Len(Front(s))-1 = Len(s) - 2
BY <2>1
<2>7. Tail(Front(s)) = [i \in 1..(Len(s)-2) |-> Front(s)[i+1]]
BY <2>4, <2>6
<2>8. \A i \in 1..(Len(s)-2) : Front(s)[i+1] = s[i+1]
BY <2>5, Z3
<2>9. QED
BY <2>7, <2>8
<1>2. Front(Tail(s)) = [i \in 1..(Len(s) - 2) |-> s[i+1]]
BY Len(s) \in Nat, Lemma2a DEF Front
<1>3. QED
BY <1>1, <1>2

LEMMA Lemma4 == \A s \in Seq(Int) : SeqSum(s) \in Int
<1> DEFINE P(N) == \A s \in Seq(Int) : (Len(s) = N) => (SeqSum(s) \in Int)
<1>1. P(0)
<2> SUFFICES ASSUME NEW s \in Seq(Int),
Len(s) = 0
PROVE  SeqSum(s) \in Int
BY DEF P
<2>1. s = << >>
OBVIOUS
<2> QED
BY <2>1, Lemma1
<1>2. ASSUME NEW N \in Nat, P(N)
PROVE  P(N+1)
<2> SUFFICES ASSUME NEW s \in Seq(Int),
Len(s) = (N+1)
PROVE  SeqSum(s) \in Int
BY DEF P
<2>1. s # << >>
OBVIOUS
<2>2. SeqSum(s) = s[1] + SeqSum(Tail(s))
BY <2>1, Lemma1
<2>3. s[1] \in Int
BY <2>1
<2>4. /\ Len(Tail(s)) = N
/\ Tail(s) \in Seq(Int)
BY <2>2, Lemma2
<2>5. SeqSum(Tail(s)) \in Int
BY <1>2, <2>4
<2>6. QED
BY <2>2, <2>3, <2>5
<1> HIDE DEF P
<1>3. \A N \in Nat : P(N)
BY <1>1, <1>2, NatInduction
<1>4. QED
BY <1>3 DEF P

LEMMA Lemma5_Proof ==
\A s \in Seq(Int) :
(Len(s) > 0) =>
SeqSum(s) =  SeqSum(Front(s)) + s[Len(s)]
<1> DEFINE P(N) == \A s \in Seq(Int) :
(Len(s) = N) =>
(SeqSum(s) = IF Len(s) = 0
THEN 0
ELSE SeqSum(Front(s)) + s[Len(s)])
<1>1. P(0)
<2> SUFFICES ASSUME NEW s \in Seq(Int),
Len(s) = 0
PROVE  SeqSum(s) = IF Len(s) = 0
THEN 0
ELSE SeqSum(Front(s)) + s[Len(s)]
BY DEF P
<2> QED
BY s = << >>,  Lemma1
<1>2. ASSUME NEW N \in Nat, P(N)
PROVE  P(N+1)
<2> SUFFICES ASSUME NEW s \in Seq(Int),
Len(s) = (N+1)
PROVE  SeqSum(s) = IF Len(s) = 0
THEN 0
ELSE SeqSum(Front(s)) + s[Len(s)]
BY DEF P
<2> SUFFICES SeqSum(s) = SeqSum(Front(s)) + s[Len(s)]
OBVIOUS
<2>1. /\ Front(s) \in Seq(Int)
/\ Len(Front(s)) = N
BY Lemma2, N+1 > 0, (N+1)-1 = N, Zenon
<2> DEFINE t == Tail(s)
<2> USE FrontDef
<2>2. /\ t \in Seq(Int)
/\ Len(t) = N
/\ SeqSum(s) = s[1] + SeqSum(t)
BY HeadTailProperties, Lemma1, s # << >>
<2>3. CASE N = 0
<3> USE <2>3
<3> HIDE FrontDef
<3>1. SeqSum(Front(s)) = 0
BY Lemma1, <2>1, Front(s) = << >>
<3>2. Len(Tail(s)) = 0
BY HeadTailProperties
<3>3. SeqSum(Tail(s)) =
IF Tail(s) = << >> THEN 0 ELSE Tail(s)[1] + SeqSum(Tail(Tail(s)))
BY <2>2, Lemma1
<3>4. SeqSum(Tail(s)) = 0
BY <3>2, <2>2, EmptySeq, Tail(s) = << >>, <3>3
<3>5. QED
BY <2>2, <3>1, <3>4
<2>4. CASE N > 0
<3> /\ Front(s) \in Seq(Int)
/\ Front(t) \in Seq(Int)
/\ Tail(Front(s)) \in Seq(Int)
<4>1. Front(s) \in Seq(Int)
BY <2>4, <2>2, Lemma2
<4>2. Front(t) \in Seq(Int)
BY <2>4, <2>2, Lemma2
<4>3. Tail(Front(s)) \in Seq(Int)
<5> Len(s) > 1
BY <2>4
<5> Len(Front(s)) > 0
BY Lemma2
<5> Front(s) \in Seq(Int)
BY Lemma2
<5> Tail(Front(s)) \in Seq(Int)
BY Lemma2
<5> QED
BY Lemma2
<4>4. QED
BY <4>1, <4>2, <4>3
<3>1. SeqSum(t) = SeqSum(Front(t)) +  t[N]
BY <1>2, <2>2, <2>4
<3>2. SeqSum(t) = SeqSum(Tail(Front(s))) + t[N]
BY <3>1, <2>4, Len(s) > 1, Lemma3
<3>3. t[N] = s[N+1]
BY <2>2, <2>4
<3> HIDE DEF Front
<3>4. /\ SeqSum(s) \in Int
/\ SeqSum(t) \in Int
/\ SeqSum(Tail(Front(s))) \in Int
/\ t[N] \in Int
/\ s[1] \in Int
<4>1. SeqSum(s) \in Int
BY <2>4, <2>2, <2>1, Lemma4
<4>2. SeqSum(t) \in Int
BY <2>4, <2>2, <2>1, Lemma4
<4>3. SeqSum(Tail(Front(s))) \in Int
<5>1. Len(s) > 1
BY <2>4
<5>2. Len(Front(s)) > 0
BY <5>1, FrontDef
<5>3. Front(s) # << >>
BY <5>2
<5>4. Tail(Front(s)) \in Seq(Int)
BY <5>3
<5>5. QED
BY <2>4, <2>2, <2>1, <5>3, Lemma4
<4>4. t[N] \in Int
BY <2>4, <2>2, <2>1
<4>4a. s[1] \in Int
BY <2>4
<4>5. QED
BY <4>1, <4>2, <4>3, <4>4
<3>5. SeqSum(s) = s[1] + SeqSum(Tail(Front(s))) + t[N]
<4>1. SeqSum(s) = s[1] + SeqSum(t)
BY <2>2
<4>2. QED
BY <4>1, <3>2, <3>4, Lemma4, Z3
<3>6. t[N] = s[N+1]
BY <2>4
<3>7. s[1] = Front(s)[1]
BY <2>4 DEF Front
<3>8. SeqSum(Front(s)) = Front(s)[1] + SeqSum(Tail(Front(s)))
BY <2>4, Lemma1
<3>9. QED
BY <3>5, <3>6, <3>7, <3>8
<2>5. QED
BY <2>3, <2>4
<1>3. \A N \in Nat : P(N)
BY <1>1, <1>2, NatInduction
<1>4. QED
BY <1>3
=============================================================================
