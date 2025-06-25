---- MODULE DieHarderMC ----
EXTENDS DieHarder

CONSTANT MCJug, MCCapacity

ASSUME /\ MCJug \in SUBSET Nat \ {0}
       /\ MCCapacity \in [MCJug -> Nat \ {0}]
       /\ Goal \in Nat
       /\ Goal \leq UNION {MCCapacity[j] : j \in MCJug}
=============================================================================
-----END CFG-----