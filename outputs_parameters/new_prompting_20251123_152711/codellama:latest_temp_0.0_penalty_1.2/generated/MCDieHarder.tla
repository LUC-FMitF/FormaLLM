---- MODULE MCDieHarder ----

(**************************************************************************)
(* The following definitions duplicate the original Die Hard problem.     *)
(**************************************************************************)

CONSTANTS Goal = 4   \* The goal of the game is to move all hostages out    *)
                      \* of the building and into a safe location.         *)

VARIABLES Jug, Capacity, Hostages, Sites, SiteCapacities, OpenDoors       )

Init ==  /\ Hostages = {}   \* No hostages are initially in the building.    *)
        /\ Sites = {1..4}     \* There are four sites available for evacuation*)
        /\ SiteCapacities = [                                              *)
            (1, 2),           \* Site 1 has a capacity of two hostages      *)
            (2, 3),           \* Site 2 has a capacity of three hostages    *)
            (3, 4)            \* Site 3 has a capacity of four hostages     *)
        ]                                                                   *)
        /\ OpenDoors = {}      \* No doors are initially open.               *)
        
Next == \/ [Hostages' |-> Hostages U {(1,2)}, Sites', SiteCapacities']    )
          [OpenDoors' |-> OpenDoors U {{1}}]                                )
        /\ (Sites' = Sites - {1} + {3})                                     *)
        /\ (SiteCapacities' = SiteCapacities - {(1,2)} + {(3,4)})           *)
        
Spec == Init /\ [][Next]_<<Hostages, Sites, OpenDoors>>                )
       \/ Hostages = {}                                                    *)
        /\ Sites = {}                                                      *)
        /\ SiteCapacities = []                                             *)
        /\ OpenDoors = {{1}}                                               *)
        
TypeOK ==  /\ Hostages' \in [Hostage |-> HOSTAGE]                          )
           /\ Sites' \in {Site |-> NATURAL}                                )
           /\ SiteCapacities' \in [[(Site, Capacity) |-> NATURAL]]   )
           /\ OpenDoors' \in [DOOR |-> BOOLEAN]                    )
           
NotSolved ==  Hostages = {}                                         *)
               /\ Sites = {1..4}                                      *)
               /\ SiteCapacities = [                                   *)
                   (1, 2),           \* Site 1 has a capacity of two hostages      *)
                   (2, 3),           \* Site 2 has a capacity of three hostages    *)
                   (3, 4)            \* Site 3 has a capacity of four hostages     *)
               ]                                                       *)
               /\ OpenDoors = {}      \* No doors are initially open.               *)
               
=============================================================================
====