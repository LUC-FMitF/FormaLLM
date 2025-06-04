---------- MODULE MCEcho ----------
EXTENDS Echo

N1 == {"a", "b", "c"}

I1 == CHOOSE n \in N1 : TRUE

R1 == [ edge \in (N1 \X N1) |-> IF edge[1] = edge[2]
THEN FALSE
ELSE TRUE ]

R2 == CHOOSE r \in [ N1 \X N1 -> BOOLEAN ] :
/\ IsConnected(r, N1)
/\ IsSymmetric(r, N1)
/\ IsIrreflexive(r, N1)

TestSpec == PrintT(R) /\ Spec
===================================
