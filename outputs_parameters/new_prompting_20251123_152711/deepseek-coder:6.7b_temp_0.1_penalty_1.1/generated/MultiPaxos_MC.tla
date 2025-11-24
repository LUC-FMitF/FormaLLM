---- MODULE MultiPaxos_MC ----

(***************************************************************************)
(* Defines a replicated state machine.                                           *)
(***************************************************************************)

EXTENDS Module

CONSTANTS
    Replicas = {s1, s2, s3}
    Writes = {w1, w2}
    Reads = {r1}
    MaxBallot = ConstMaxBallot

VARIABLES
    ballot, writeValue, readValue

ASSIGN
    SymmetricPerms == {s1, s2, s3}

INVARIANTS
    TypeOK ==
        \E s \in Replicas : ballot[s] \in 0 .. MaxBallot
        \E s \in Replicas : writeValue[s] \in Writes
        \E s \in Replicas : readValue[s] \in Reads

    Linearizability ==
        \E s \in Replicas : ballot[s] \in 0 .. MaxBallot
        \E s \in Replicas : writeValue[s] \in Writes
        \E s \in Replicas : readValue[s] \in Reads

SPECIFICATION Spec

=============================================================================
====

(* TLC Configuration *)
CONSTANTS
    Replicas = {s1, s2, s3}
    Writes = {w1, w2}
    Reads = {r1}
    MaxBallot = ConstMaxBallot

SPECIFICATION Spec

INVARIANTS
    TypeOK
    Linearizability

CHECK_DEADLOCK TRUE
====