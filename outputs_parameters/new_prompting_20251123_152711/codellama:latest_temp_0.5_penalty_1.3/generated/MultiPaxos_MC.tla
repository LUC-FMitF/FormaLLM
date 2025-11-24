---- MODULE MultiPaxos_MC ----

(***************************************************************************)
(* Defines the leader election protocol for a set of replicas. Each        *)
(* replica maintains an internal ballot number that is incremented each  *)
(* time it sends a request to become the leader. The replica with the   *)
(* highest ballot number wins the election and becomes the new leader.    *)
(***************************************************************************)

CONSTANTS Replicas, Writes, Reads

VARIABLES 
    Leader \* The current leader of the replica set.
    Ballots <- ConstBallotMap   \* A map from each replica to its ballot number.

-----------------------------------------------------------------------------
Init ==                                                                     *)
    /\ Leader = NoLeader         \* There is no leader initially.
    /\ ALL r : Replicas | Ballots[r] = 0   \* Each replica has a ballot number of 0.
-----------------------------------------------------------------------------
Next ==                                                                     *)
    NextLeader(Replicas, Writes, Reads) => Leader' \* If the next leader is determined, update it.
    /\ Leader /= NoLeader         =>                      \* Otherwise...
        /\ Leader = Choose r : Replicas | Ballots[r] >= Ballots[Leader]     \* ...select a replica with the highest ballot number as leader.
-----------------------------------------------------------------------------
NextLeader == 
    Init =>                                                \* The initial predicate is true if...
        /\ ALL r : Replicas | Ballots[r] = 0             \* ...all replicas have a ballot number of 0.
    [] Leader /= NoLeader         =>                      \* ...if there is no leader, then the next leader is determined by...
        /\ ALL r : Replicas | Ballots[r] >= Ballots[Lea   \* ...the highest ballot number of each replica.
    [] Leader = NoLeader          =>                      \* ...if there was no leader, then the next leader is determined by...
        /\ ALL r : Replicas | Ballots[r] >= 0            \* ...the highest ballot number of each replica that is greater than or equal to zero.
-----------------------------------------------------------------------------
TypeOK ==                                                      *)
    Leader \in {NoLeader} UNION Replicas        \* The leader can be NoLeader or a member of the set of replicas.
    ALL r : Replicas | Ballots[r] >= 0     \* Each ballot number is greater than or equal to zero.
-----------------------------------------------------------------------------
Linearizability ==                                             *)
    Init => TRUE                \* The initial predicate must be true.
    [] Leader /= NoLeader         =>           \* If there is a leader, then...
        /\ ALL r : Replicas | Ballots[r] >=   \* ...the ballot number of each replica that is greater than or equal to the current leader's ballot number.
-----------------------------------------------------------------------------
Spec ==                                                          *)
    Init => [](TypeOK /\ Linearizability)       \* The specification consists of two parts: the initial predicate and a linearizability constraint.
=============================================================================
====