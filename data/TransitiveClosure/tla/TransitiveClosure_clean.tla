-------------------------- MODULE TransitiveClosure -------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC

Support(R) == {r[1] : r \in R} \cup {r[2] : r \in R}

TC(R) ==
LET S == Support(R)
IN  {<<s, t>> \in S \X S :
\E p \in Seq(S) : /\ Len(p) > 1
/\ p[1] = s
/\ p[Len(p)] = t
/\ \A i \in  1..(Len(p)-1) : <<p[i], p[i+1]>> \in R}

TC1(R) ==
LET BoundedSeq(S, n) == UNION {[1..i -> S] : i \in 0..n}
S == Support(R)
IN  {<<s, t>> \in S \X S :
\E p \in BoundedSeq(S, Cardinality(S)+1) :
/\ Len(p) > 1
/\ p[1] = s
/\ p[Len(p)] = t
/\ \A i \in  1..(Len(p)-1) : <<p[i], p[i+1]>> \in R}

R ** T == LET SR == Support(R)
ST == Support(T)
IN  {<<r, t>> \in SR \X ST :
\E s \in SR \cap ST : (<<r, s>> \in R) /\ (<<s, t>> \in T)}

TC2(R) ==
LET C[n \in Nat] == IF n = 0 THEN R
ELSE C[n-1] \cup (C[n-1] ** R)
IN  IF R = {} THEN {} ELSE C[Cardinality(Support(R)) - 1]

RECURSIVE TC3(_)
TC3(R) == LET RR == R ** R
IN  IF RR \subseteq R THEN R ELSE TC3(R \cup RR)

TC4(R) ==
LET S == Support(R)
RECURSIVE TCR(_)
TCR(T) == IF T = {}
THEN R
ELSE LET r == CHOOSE s \in T : TRUE
RR == TCR(T \ {r})
IN  RR \cup {<<s, t>> \in S \X S :
<<s, r>> \in RR /\ <<r, t>> \in RR}
IN  TCR(S)

ASSUME \A N \in 0..3 :
\A R \in SUBSET ((1..N) \X (1..N)) : /\ TC1(R) = TC2(R)
/\ TC2(R) = TC3(R)
/\ TC3(R) = TC4(R)

TC5(R(_,_), S, s, t) ==
LET CR[n \in Nat, v \in S] ==
IF n = 0 THEN R(s, v)
ELSE \/ CR[n-1, v]
\/ \E u \in S : CR[n-1, u] /\ R(u, v)
IN  /\ s \in S
/\ t \in S
/\ CR[Cardinality(S)-1, t]

ASSUME \A N \in 0..3 : \A R \in SUBSET ((1..N) \X (1..N)) :
LET RR(s, t) == <<s, t>> \in R
S == Support(R)
IN  \A s, t \in S :
TC5(RR, S, s, t) <=> (<<s, t>> \in TC1(R))
=============================================================================
