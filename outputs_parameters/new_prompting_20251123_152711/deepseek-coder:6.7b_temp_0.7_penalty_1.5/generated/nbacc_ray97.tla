---- MODULE nbacc_ray97 ----

(***************************************************************************)
(* TLA+ encoding of the algorithm NBAC with crashes in:                    *)
(* [1] Raynal, Michel. "A case study of agreement problems in distributed   *)
(* systems: non-blocking atomic commitment." High-Assurance Systems Engineering  *)
(* Workshop, 1997., Proceedings. IEEE, 1997.                              *)
(* Igor Konnov, Thanh Hai Tran, Josef Widder, 2016                          *)
(* This file is a subject to the license that is bundled together with this   *)
(* package and can be found in the file LICENSE.                             *)
(***************************************************************************)

CONSTANTS 
    N = 2 (* Number of processes *)

VARIABLES 
    Proc == {0 .. N-1} (* Processes indices *)
    pc[Proc] == "" (* Process counters: "YES", "NO" or "CRASH" *)
    fd[Proc] == FALSE (* Failure detector state for each process *)

LOCAL FUNCTION Receive() 
    == CHOOSE x \in Proc; CHOICE y IN {"YES", "NO"} -> (pc[x] = y, TRUE) END
    [Receive()]_pc[Proc];

OPERATIONS 
    (* Process self becomes crash *)
    Crash(self) == fd[self] := TRUE, pc[self] := "CRASH"
    
    (* Sends a YES message *)
    SendYes(self) == ~(pc[self] = "YES") /\ Receive() -> (pc[self] = "YES", TRUE) END
    
    (* Sends a NO message *)
    SendNo(self) == ~(pc[self] = "NO") /\ Receive() -> (pc[self] = "NO", TRUE) END
        
INVARIANTS 
    TypeOK == \A self \in Proc : pc[self] IN {"YES", "NO", "CRASH"}

SPECIFICATION Spec == 
    <>[](<>(\A self  \in Proc : (fd[self] = FALSE)) -> 
        <>(\A self \in Proc : ((pc[self] = "COMMIT") OR (pc[self] = "ABORT"))))
    [Receive()](<>[](\A self \in Proc : pc[self] # "CRASH"  /\ fd[self] = FALSE) -> 
        <>(<>(\A self \in Proc : (pc[self] = "COMMIT") OR (pc[self] = "ABORT"))))
    [SendYes()](<>[](\A self \in Proc : pc[self] # "CRASH"  /\ fd[self] = FALSE) -> 
        <>(<>(\A self \in Proc : (pc[self] = "COMMIT") OR (pc[self] = "ABORT"))))
    [SendNo()](<>[](\A self \in Proc : pc[self] # "CRASH"  /\ fd[self] = FALSE) -> 
        <>(<>(\A self \in Proc : (pc[self] = "COMMIT") OR (pc[self] = "ABORT"))))
    []<>[](<>(\A self \in Proc : pc[self] # "CRASH"  /\ fd[self] = FALSE) -> 
        <>(<>(\A self \in Proc : (pc[self] = "COMMIT") OR (pc[self] = "ABORT"))))
    =============================================================================
    ====