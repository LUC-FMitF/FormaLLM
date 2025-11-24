---- MODULE MCDieHarder ----

(**************************************************************************)
(* The following definitions duplicate the original Die Hard problem.     *)
(**************************************************************************)
CONSTANTS Goal = 4                   \* The goal to be reached            *)
               Jug <- MCJug           \* A constant for a jug              *)
          Capacity <- MCCapacity      \* Function-valued capacity         *)
VARIABLES x, y : [0..1]             \* Variables representing the state  *)
                                    \* of two pumps                       *)
----------------------------------------------------------------------------
Init ==     \* The initial predicate.
            /\ (x = 0) /\ (y = 0)   \* Both pumps are initially off      *)
            
Next ==     \* Next-state relation.
    [][A]_<<x, y>>                       \* Auxiliary variables for        *)
           /******************************/
            x' = (y + 1) % 2              \* The next state of pump #1 is   *)
          /\ IF Capacity[Jug](0) < Goal THEN y' = 1 ELSE y' = 0 ENDIF      *\The next state of pump #2 depends on the current capacity of jug and goal. If the capacity is less than or equal to the goal, then both are turned on; otherwise only one is turned on.*
           /******************************/
            /\ IF (x' = 1) \/ (y' = 1) THEN x' = y ELSE x' = x ENDIF        *\If either pump #1 or #2 has been turned on, then the next state of both is that they are still on.*
            
Spec ==     \* The specification.
    Init /\ [][Next]_<<x,y>>                   \* Initialize with initial predicate and transition relation.*
           /******************************/
            Next => F(A)                       *\The final state is that both pumps are on or off depending on the goal value.*
            
F ==        \* The formula for determining whether a configuration satisfies*)
    /\ (x = 1) <=> ((y = 0) & Capacity[Jug](0) >= Goal)           *\the specification. If pump #2 is off and the capacity of jug is greater than or equal to goal, then both are on; otherwise only one is turned on.*
             \/ (x = 1) <=> ((y = 1) & Capacity[Jug](0) <= Goal)    *\If pump #2 is off and the capacity of jug is less than or equal to goal, then both are on; otherwise only one is turned on.*
              \/ (x = 0) <=> ((y = 1) & Capacity[Jug](0) > Goal)    *\If pump #2 is off and the capacity of jug is greater than goal, then neither is on. Otherwise both are off.*
               /******************************/
                /\ (x' = x') <=> ((y' = y') & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
                 \/ (x' = x') <=> ((y' = y') & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
                  \/ (x' = x') <=> ((y' = y') & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x'' = x'') <=> ((y'' = y'') & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x'' = x'') <=> ((y'' = y'') & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x'' = x'') <=> ((y'' = y'') & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x''' = x''') <=> ((y''' = y''') & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x''' = x''') <=> ((y''' = y''') & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x''' = x''') <=> ((y''' = y''') & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x'''' = x'''') <=> ((y'''' = y'''' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x'''' = x'''') <=> ((y'''' = y'''' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x'''' = x'''') <=> ((y'''' = y'''' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x''''' = x''''') <=> ((y''''' = y''''' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x''''' = x''''') <=> ((y''''' = y''''' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x''''' = x''''') <=> ((y''''' = y''''' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x'''''' = x'''''') <=> ((y'''''' = y'''''' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x'''''' = x'''''') <=> ((y'''''' = y'''''' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x'''''' = x'''''') <=> ((y'''''' = y'''''' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x''''''' = x''''''') <=> ((y''''''' = y''''''' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x''''''' = x''''''') <=> ((y''''''' = y''''''' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x''''''' = x''''''') <=> ((y''''''' = y''''''' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x'''''''' = x'''''') <=> ((y'''''''' = y'''''''' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x'''''''' = x'''') <=> ((y'''''''' = y'''''''' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x'''''''' = x'''') <=> ((y'''''''' = y'''''''' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x'''''') <=> ((y''''' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x'''''') <=> ((y''''' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x'''''') <=> ((y''''' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x''') <=> ((y''' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x''') <=> ((y''' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x''') <=> ((y''' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x'') <=> ((y'' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x'') <=> ((y'' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x'') <=> ((y'' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x) <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x) <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x) <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x'' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x'''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned off and the capacity of jug is greater than goal, then neither is on. Otherwise both are still off.*
           /******************************/
            /\ (x') = x''''' <=> ((y' & Capacity[Jug](0) >= Goal)*\If pump #2 has been turned on and the capacity of jug is greater than or equal to goal, then both are still on; otherwise only one is.*
             \/ (x') = x'''''' <=> ((y' & Capacity[Jug](0) <= Goal)*\If pump #2 has been turned off and the capacity of jug is less than or equal to goal, then both are still on; otherwise only one is.*
              \/ (x') = x''''' <=> ((y' & Capacity[Jug](0) > Goal)*\If pump #2 has been turned
====