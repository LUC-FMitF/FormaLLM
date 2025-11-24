---- MODULE MCEWD687a ----

(***************************************************************************)
(* Defines a distributed tree, where each process maintains a subtree.      *)
(***************************************************************************)

CONSTANTS   L,  \* The set of all processes.
            P1, P2, P3, \* The set of all processes.
            Procs, \* MV CONSTANT definitions
            Edges, \* CONSTANT definitions
            Leader, \* CONSTANT definitions
            constr_1633116534008313000, \* CONSTRAINT definition
            Spec, \* SPECIFICATION definition
            CountersConsistent, \* PROPERTY definition
            TreeWithRoot, \* PROPERTY definition
            StableUpEdge, \* PROPERTY definition
            DT1Inv, \* INVARIANT definition
            DT2, \* PROPERTY definition
            TypeOK \* INVARIANT definition

CONSTANT
    Procs <- const_1633116534008310000

CONSTANT
    Edges <- const_1633116534008311000

CONSTANT
    Leader <- const_1633116534008312000

CONSTRAINT
    constr_1633116534008313000

SPECIFICATION
    Spec

CHECK_DEADLOCK
    FALSE

INVARIANT
    TypeOK
    DT1Inv

PROPERTY
    DT2

PROPERTIES
    CountersConsistent
    TreeWithRoot
    StableUpEdge

-----------------------------------------------------------------------------

=============================================================================
====