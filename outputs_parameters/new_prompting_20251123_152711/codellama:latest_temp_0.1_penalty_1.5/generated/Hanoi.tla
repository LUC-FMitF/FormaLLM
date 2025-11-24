---- MODULE Hanoi ----
------------------------------ MODULE Towersof Hanoi ----------------------------
(***********************************************************************
* A simple model of the classic puzzle "Towers Of Hanoi".              * 
*                                                                      *)  
* The initial state is a configuration with all disks on tower #1.     *   
* Each step consists in moving one disk from any other to another       *       
tower, provided the destination does not contain smaller            )*)        
disks and there are no larger discs above it (see "Move" below).      *)  
(******************************)                               ))     (* 
* The final state is a configuration with all disks on tower #3.       *   
* Invariants: All towers have the same number of elements, and each    )*)        
element has at least one smaller element above it (see "Invariant"   *)     
below).                               ))     (* 
******************************)            )))        ()              **/INST]
====