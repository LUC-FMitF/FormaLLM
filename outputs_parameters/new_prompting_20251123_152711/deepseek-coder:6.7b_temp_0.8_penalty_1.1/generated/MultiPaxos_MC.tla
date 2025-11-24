---- MODULE Paxos  ----
(*******************************************************************************)
(* Defines Paxos consensus algorithm.                                           *)
(*******************************************************************************)

EXTENDS ZSequences

CONSTANTS   ConstMaxBallot \* Maximum ballot number

ASSUME CONSTANTS
    Replicas = {s1, s2, s3}  \* The set of all replicas.
    Writes  = {w1, w2}       \* The set of all write operations.
    Reads   = {r1}           \* The set of all read operations.
    MaxBallot <- ConstMaxBallot  \* The maximum ballot number.
    
\* Type check invariant.
TypeOK ==  
    /\ Replicas \in POWERSET Writes
    /\ Cardinality(Replicas) = Len(Writes) + 1
    /\ MaxBallot \notin Domain(Writes)
    
\* Linearizability constraint.
Linearizability ==  
    [r ∈ Reads] /\ r ∈ Domain(ReadValues) => ReadValues[r] = Values[NextState -> Writes[r]]
    
SPECIFICATION Spec

INVARIANTS TypeOK Linearizability

CHECK_DEADLOCK TRUE
===============================================================================
====