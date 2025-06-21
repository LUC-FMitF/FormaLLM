---- MODULE DieHarderMC ----
EXTENDS DieHarder

CONSTANT MCJug, MCCapacity

ASSUME /\ MCJug \in {1, 2}
       /\ MCCapacity \in [MCJug -> Nat]
       /\ \A j \in MCJug : MCCapacity[j] > 0
       /\ Goal \in Nat
       /\ Goal < MCCapacity[1] + MCCapacity[2]
=============================================================================
\* Modification History
\* Last modified Wed Feb 04 16:44:37 PST 2015 by lamport
\* Created Wed Feb 04 13:33:09 PST 2015 by lamport