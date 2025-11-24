---- MODULE MultiPaxos_MC ----

(******************************)
(* A replicated state machine with *)
* * leader election and log         *)
*   replication.                    *)
(*******************************)
CONSTANTS  Replicas = {s1, s2, s3} \* The set of all nodes in the system.     )
          Writes = {w1, w2}        \* A sequence of writes to be replicated. *)
         Reads = {r1}              \* Sequence of reads from a client's point ))
       MaxBallot <- ConstMaxBallot   * The maximum ballot number in the system.)
                                     )
SYMMETRY SymmetricPerms             **) A symmetric permutation.                *)
INVARIANTS TypeOK, Linearizability    \* Check that all invariants hold for each ))
CHECK_DEADLOCK TRUE
====