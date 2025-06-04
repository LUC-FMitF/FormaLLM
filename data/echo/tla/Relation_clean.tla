----------------------------- MODULE Relation ------------------------------
EXTENDS Naturals, FiniteSets

IsReflexive(R, S) == \A x \in S : R[x,x]

IsIrreflexive(R, S) == \A x \in S : ~ R[x,x]

IsSymmetric(R, S) == \A x,y \in S : R[x,y] <=> R[y,x]

IsAsymmetric(R, S) == \A x,y \in S : ~(R[x,y] /\ R[y,x])

IsTransitive(R, S) == \A x,y,z \in S : R[x,y] /\ R[y,z] => R[x,z]

TransitiveClosure(R, S) ==
LET N == Cardinality(S)
trcl[n \in Nat] ==
[x,y \in S |-> IF n=0 THEN R[x,y]
ELSE \/ trcl[n-1][x,y]
\/ \E z \in S : trcl[n-1][x,z] /\ trcl[n-1][z,y]]
IN  trcl[N]

ReflexiveTransitiveClosure(R, S) ==
LET trcl == TransitiveClosure(R,S)
IN  [x,y \in S |-> x=y \/ trcl[x,y]]

IsConnected(R, S) ==
LET rtrcl == ReflexiveTransitiveClosure(R,S)
IN  \A x,y \in S : rtrcl[x,y]

=============================================================================
