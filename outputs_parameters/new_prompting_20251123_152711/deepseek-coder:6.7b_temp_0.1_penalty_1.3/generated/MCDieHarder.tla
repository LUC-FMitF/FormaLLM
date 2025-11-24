---- MODULE MCDieHarder -----
EXTENDS ModuleDieHard
CONSTANTS Jug, Capacity = \* The set of all jugs and their capacities as defined in the original module.
Goal     << Goals >>    = <<4>>   /\ *The desired amount to be achieved by pouring water.*
MCJug    << Pour => FillAmt >>  = <>    /\  \* The set of all jugs and their capacities as defined in the original module.
MCCapacity[j] == IF j = Jug THEN Capacitor(Pours, Goal) ELSE NoCapacity ENDIF   (*The capacity function for each jug*)
Specification Spec OK (<> \in Pour => FillAmt /\ * The specification of pouring water to achieve the goal. *) 
Invariants TypeOK NotSolved   ==> <<MCJug, MCCapacity>> Substitution   (*The configuration file for TLC*)
=============================================================================