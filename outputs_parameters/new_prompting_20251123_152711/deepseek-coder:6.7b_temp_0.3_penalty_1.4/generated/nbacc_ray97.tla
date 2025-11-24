---- MODULE nbacc_ray97 ----
------------------------------- MODULE -------------------------------------
EXTENDS FiniteSets, Naturals, Sequences
===============================================================================
CONSTANT Proc = {0..N-1}         (* Processes *)
VARIABLE pc  == [Proc -> {"YES", "NO"}]    (* Process counters: YES/NO votes for each process *)
VARIABLE fd  := ^[Proc]           (* Failure detector report, ^ means nondeterministic choice *)
===============================================================================
(* Modification History *)
LOCAL OPERATOR MODIFICATION_HISTORY(s) == s /\ "Last modified Mon Jul 09 13:26:03 CEST 2018 by tthai" \/ ""
INVARIANT TypeOK(* Check that the model is well-formed *)
===============================================================================
LOCAL OPERATOR Receive(p, m) == [Proc -> (IF p = self THEN InsertElm(m, pc[self]) ELSE pc)] (* Process receives a message *)
LOCAL OPERATOR Send(p, m)    == [Proc -> IF p \in Proc AND p ~= self THEN DeleteElm(m, pc[p]) ELSE pc] (* Process sends a message *)
OPERATOR Abort == "ABORT"       (* Action to abort the protocol if some condition is met *)
OPERATOR Commit== "COMMIT"     (* Action to commit the protocol when all processes agree on it *)
===============================================================================
(* Failure detector report: nondeterministic choice for each process *)
LOCAL OPERATOR Report(p) == [Proc -> IF p \in Proc AND fd[p] = TRUE THEN "CRASH" ELSE Choice("YES", "NO")] 
(* Failure detector sends a nondeterministic prediction to the process itself *)
LOCAL OPERATOR SelfReport(fd) == [Proc -> IF self \in Proc AND fd[self] = TRUE THEN Report(self)(Choice("YES", "NO")) ELSE (fd, Choice("YES", "NO") ) ] 
===============================================================================
(* Specification of the protocol *)
SPECIFICATION NonTriv == (* The specification is correct if all processes have voted and no process has crashed *)
   [](\A i \in Proc : pc[i] = Choice("YES", "NO"))  /\ (<>[](fd ~= TRUE)) => <>((pc[\self]) = ("COMMIT" OR Abort) )    (* If all processes voted and no process has crashed, then the protocol either commits or aborts *)
===============================================================================
(* TLC Configuration *)
CONSTANT N = 2                   (* Number of nodes in network (processes are numbered from 0 to n-1). *)
INVARIANT TypeOK                (* Check that all operators and constants have the correct type. *)
SPECIFICATION Spec               (* The specification is a conjunction of atomic propositions defining reachability properties for each operator defined above, e.g., Receive(p, m), Send(p, m).*) 
===============================================================================
==== NonBlockAtomicCommit ====