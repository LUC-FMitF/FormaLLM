---- MODULE DieHarderMC ----
EXTENDS DieHarder

CONSTANT MCJug, MCCapacity

ASSUME /\ MCJug \in Nat \ {0}
       /\ MCCapacity \in [MCJug -> Nat \ {0}]
       /\ Goal \in Nat \ {0}
       /\ Goal \leq MCCapacity[MCJug]

=============================================================================
-----END CFG-----