---- MODULE MultiPaxos_MC ----

(**************************************************************************)
(* TLC config-related defs.                                                       *)
(**************************************************************************)
CONSTANTS   ConstMaxBallot, MaxBallot \* The maximum ballot number possible.
            Writes, Reads             \* The set of all write and read operations respectively.
VARIABLES   replicas                  \* The set of all state machine replicas.
            curr_ballot               \* The current ballot number.
            log                       \* A log of all operation executed in the state machine.
            
SYMMETRY SymmetricPerms ==             \* Defining a symmetry relation for permutations.
    DOMAIN replicas  PERMUTES {s1, s2, s3}
    
(* Type check invariant *)
TypeOK == 
    DOMAIN curr_ballot <= MaxBallot
    REPL(replicas) IN SymmetricPerms * Writes UNION Reads
    
(* Linearizability constraint *)
Linearizability ==                       \* Defining linearizability.
    [op \in log |-> op[curr_ballot] ](log) = replicas[curr_ballot]
    
SPECIFICATION Spec == 
    Init /\ [][Next]_<<replicas, curr_ballot, log>>

(* Definition of the next state relation *)
Next ==                                  \* The definition of the next state relation.
    /\  \E op \in Writes : Update(op)
    /\  \E op \in Reads  : Read(op)
    
Update(op) == 
    IF curr_ballot < MaxBallot THEN
        curr_ballot' = curr_ballot + 1
        log' = log UNION {[curr_ballot' -> op]}
    ELSE 
        (* Ballot overflow *)
        curr_ballot' = curr_ballot
        log' = log
    
Read(op) == 
    IF curr_ballot < MaxBallot THEN
        curr_ballot' = curr_ballot + 1
        log' = log UNION {[curr_ballot' -> op]}
    ELSE 
        (* Ballot overflow *)
        curr_ballot' = curr_ballot
        log' = log
        
Init == 
    replicas = {s1, s2, s3}
    curr_ballot = 0
    log = {}
    
(* Definition of the specification *)
Spec == Init /\ [][Next]_<<replicas, curr_ballot, log>>
=============================================================================
====
CHECK_DEADLOCK TRUE  \* Check for deadlocks in our system.
====