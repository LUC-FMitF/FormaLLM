---- MODULE MCEWD687a ----

(************************************************************)
(* A distributed tree with a leader.                        *)
(************************************************************)

CONSTANTS
    L = L
    P1 = P1
    P2 = P2
    P3 = P3

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

====