---- MODULE MultiPaxos_MC ----

(*******************************************************************************)
(* A simple example of linearizability.                                         *)
(*******************************************************************************)

CONSTANTS   Replicas = {s1, s2, s3}
            Writes = {w1, w2}
            Reads = {r1}
            MaxBallot <- ConstMaxBallot

SYMMETRY SymmetricPerms

INVARIANTS 
    TypeOK
    Linearizability

CHECK_DEADLOCK TRUE

--------------------------------------------------------------------------------

TypeOK ==
    /\ Replicas \in FiniteSets
    /\ Writes \in FiniteSets
    /\ Reads \in FiniteSets
    /\ MaxBallot \in FiniteSets

Linearizability ==
    /\ \A r \in Reads : \A w \in Writes :
        \A s \in Replicas :
            (r, w) \in s
            \/ (r, w) \in s'
            \/ (r, w) \in s''
            \/ (r, w) \in s'''

SymmetricPerms ==
    /\ \A r \in Reads : \A w \in Writes :
        \A s \in Replicas :
            (r, w) \in s
            \/ (r, w) \in s'
            \/ (r, w) \in s''
            \/ (r, w) \in s'''
        \/ (r, w) \in s
        \/ (r, w) \in s'
        \/ (r, w) \in s''
        \/ (r, w) \in s'''

Spec ==
    Init /\ [](TypeOK /\ Linearizability)

Init ==
    [](
        Replicas = {s1, s2, s3}
        Writes = {w1, w2}
        Reads = {r1}
        MaxBallot <- ConstMaxBallot
    )

=============================================================================
====