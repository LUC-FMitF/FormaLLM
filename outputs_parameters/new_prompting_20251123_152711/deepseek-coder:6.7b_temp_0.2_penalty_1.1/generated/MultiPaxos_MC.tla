---- MODULE MultiPaxos_MC ----

(*********************************************************************************************)
(* TLC config-related defs.                                                                 *)
(*********************************************************************************************)
CONSTANTS   ConstMaxBallot \* Maximum ballot number that can be used in the system.
            Quorum = {s1, s2}  \* The set of replicas required to commit a value.

\* Type check invariant.
TypeOK == [Replicas]_v /\ Cardinality([r \in Reads |-> r]) = Replicas

\* Linearizability constraint.
Linearizability == \A w \in Writes : 
    (EXISTS b \in BallotNumbers : Write[b, w] /\ Majority(Quorum, b)) =>
        EXISTS s \in Quorum : Read[s, Values[w]]

SPECIFICATION Spec

SYMMETRY SymmetricPerms == [Replicas]_v = {r \in Replicas |-> r}

INVARIANTS  TypeOK /\ Linearizability

CHECK_DEADLOCK TRUE
=============================================================================
====