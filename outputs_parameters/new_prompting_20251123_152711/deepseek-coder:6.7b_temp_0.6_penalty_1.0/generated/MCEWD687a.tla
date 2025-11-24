---- MODULE MCEWD687a ----------------------------

EXTENDS Model

CONSTANTS
    L, P1, P2, P3

CONSTANT
    Procs <- const_1633116534008310000
    Edges <- const_1633116534008311000
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

=============================================================================
====