---- MODULE MCDieHarder ----

(*****************************************************************************)
(* The following definitions duplicate the original Die Hard problem.         *)
(* To have TLC find a solution, we must tell it what values to use for the    *)
(* constant parameters Jug, Capacity, and Goal. However, TLC does not allow  *)
(* one to write function-valued expressions in a configuration file. So, this   *)
(* module extends DieHarder by defining functions MCCapacity and MCJug which are*)
(* used for substitution of the constants Jug and Capacity respectively     .    *)(******************************************************************************)
(************************************************* 50 chars wide line *** )
CONSTANTS Goal     <- DIEHARDER.Goals,   \ The goal amount to be measured by jugs (from DieHarder module).
          Jug      <- MCJug              ,    (* Substitute for the capacity of each individual jug *) 
                                                 /\* from an external source as a function having all possible states of *)(*)
           Capacity < - MCCapacity      \ The total amount that can be measured by adding water to different amounts.  
                                                                                    (from DieHarder module).    (* Substitute for the capacity *) 
                                                 /\* from an external source as a function having all possible states of *)(*)
(* Invariants: TypeOK, NotSolved are taken directly form DIEHARDER Module.   \ These ensure that we have not changed any existing behavior or added new one .    (from DieHarder module). *) 
INVARIANTS TypeOK <-Dieharder.TypeOk ,NotSolved< - NOT SolvedFor(Goal,Jug) /\* Invariant to check whether the system is in a valid state and not solved yet for current goal*)  
SPECIFICATION Spec  <-- DIEHARDER.Spec  \ The specification of DieHarder module remains same .    (from DieHarDer Module). *)     (* Substitute MCCapacity, MCJug from an external source as a function having all possible states for Capacity and Jug respectively*)
===============================================================================   /\* Line ends here ***)  \ End of the specification.                                                   \(*\(******************************************************************************\)    (from DieHarDer Module). *)     (* Substitute MCCapacity, MCJug from an external source as a function having all possible states for Capacity and Jug respectively*)
====   /\* Line ends here ***)  \ End of the specification.                                                   \(*\(******************************************************************************\)    (from DieHarDer Module). *)     (* Substitute MCCapacity, MCJug from an external source as a function having all possible states for Capacity and Jug respectively*)
====