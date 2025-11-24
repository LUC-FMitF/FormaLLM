---- MODULE MultiPaxos ---------------------
EXTENDS TLC

CONSTANT Replicas = {1..n}

ASSUME \A r \in Replicas . ~(Stutter(Replica[r]) U NextState(Replica[r]))

VARIABLES
    ...  (* Variables definition here *)

PROCEDURES
    BecomeLeader /1-1/ (r)
        (* Procedure body here *)
    END;
    
    HandlePrepare /2-1/ (r)
        (* Procedure body here *)
    END;
    
    ...  (* More procedures definition here *)

PROCEDURE Replica[x] /0/, x \in Replicas /
BEGIN
    rloop: WHILE ~terminated DO
        CHOOSE nj /~nj/ FROM {BecomeLeader(r), HandlePrepare(r), ...} END;  (* Choose next operation *)
        ~NextState[x];   (* Apply stuttering *)
    END;
END;
====