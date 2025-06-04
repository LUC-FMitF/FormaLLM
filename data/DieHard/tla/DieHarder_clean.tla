----------------------------- MODULE DieHarder ------------------------------

EXTENDS Naturals

CONSTANT Jug,
Capacity,
Goal

ASSUME /\ Capacity \in [Jug -> {n \in Nat : n > 0}]
/\ Goal \in Nat

Min(m,n) == IF m < n THEN m ELSE n
-----------------------------------------------------------------------------

VARIABLE contents

TypeOK == contents \in [Jug -> Nat]

Init == contents = [j \in Jug |-> 0]
-----------------------------------------------------------------------------

FillJug(j)  == contents' = [contents EXCEPT ![j] = Capacity[j]]

EmptyJug(j) == contents' = [contents EXCEPT ![j] = 0]

JugToJug(j, k) ==
LET amountPoured == Min(contents[j], Capacity[k]-contents[k])
IN  contents' = [contents EXCEPT ![j] = @ - amountPoured,
![k] = @ + amountPoured]

Next ==  \E j \in Jug : \/ FillJug(j)
\/ EmptyJug(j)
\/ \E k \in Jug \ {j} : JugToJug(j, k)

Spec == Init /\ [][Next]_contents
-----------------------------------------------------------------------------

NotSolved == \A j \in Jug : contents[j] # Goal

=============================================================================
