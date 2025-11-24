---- MODULE DieHarder EXTENDS DieHard ----
------------------------------------------- MODULE MCDieHarder ---------------------------------------
(**************************************************************************)
(* The following definitions duplicate the original Die Hard problem.         *)
(**************************************************************************)

CONSTANTS JugSize, Goal \* Values to be determined by TLC;
                          * can't use function-valued expressions in a configuration file.
VARIABLES  jug[JugSize]  

MCCapacity == UNSPECIFIED \* Capacity is a function of Jug size.
MCJug      == UNSPECIFIED \* Jug size is determined by TLC.

Spec        == UNCHANGED <<Capacity, Jug>> /\ DieHard.Spec 
TypeOK     == MCJug \in FiniteSets /\ MCCapacity(MCJug) \in Naturals^+ /\
              jug[i] \in {0, 1} : i \in Domain[jug]
NotSolved  == (\E i \in JugSize: jug[i] = 1) ==> ~(Capacity = Goal)
=============================================================================
====
TLC configuration (Java extension):
====