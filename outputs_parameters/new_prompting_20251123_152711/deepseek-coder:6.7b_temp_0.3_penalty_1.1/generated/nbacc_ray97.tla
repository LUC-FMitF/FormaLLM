---- MODULE nbacc_ray97 ----

(***************************************************************************)
(* Modification History                                                   *)
(* Last modified Mon Jul 09 13:26:03 CEST 2018 by tthai                    *)
(* Created Thu Mar 12 00:46<｜begin▁of▁sentence｜> CET 2015 by igor                            *)
(* TLA+ encoding of the algorithm NBAC with crashes in:                      *)
(* [1] Raynal, Michel. "A case study of agreement problems in distributed    *)
(* systems: non-blocking atomic commitment." High-Assurance Systems          *)
(* Engineering Workshop, 1997., Proceedings. IEEE, 1997.                    *)
(* Igor Konnov, Thanh Hai Tran, Josef Widder, 2016                          *)
(* This file is a subject to the license that is bundled together with this   *)
(* package and can be found in the file LICENSE.                              *)
(***************************************************************************)

CONSTANT Proc == {0..N-1}
VARIABLE pc[Proc] == "YES"
VARIABLE fd[Proc] == FALSE

\* messages which are received
OPERATION Receive(self, msg) ==
  IF self \in DOMAIN fd THEN
    CASE msg
      [] "NO" -> pc[self] := "NO"
      [] "YES" -> pc[self] := "YES"
      [] "CRASH" -> fd[self] := TRUE, Abort(self)
  ENDCASE

\* messages which are sent by
OPERATION Send(self, msg, to) ==
  IF self \in DOMAIN fd THEN
    CASE msg
      [] "NO" -> Receive(to, "NO")
      [] "YES" -> Receive(to, "YES")
      [] "CRASH" -> Receive(to, "CRASH")
  ENDCASE

\* failure detector reporting to every process whether some process has crashed
OPERATION ReportCrash(self) ==
  IF self \in DOMAIN fd THEN
    fd[self] := TRUE
  ELSE
    Abort(self)

\* a process votes for the crash of another process
OPERATION VoteForCrash(self, proc) ==
  IF self = proc OR fd[proc] THEN
    Send(self, "CRASH", proc)
  ELSE
    Abort(self)

\* all processes, including the crashed ones, vote for the crash of another process
OPERATION VoteForCrashAll(self) ==
  IF self \in DOMAIN fd THEN
    FORALL i IN Proc UNTIL (fd[i] OR i = self) DO
      VoteForCrash(self, i)
  ELSE
    Abort(self)

\* a process commits if it voted for the crash and received only YES messages from all processes
OPERATION Commit(self) ==
  IF (<>[](\A i IN Proc : pc[i] = "YES") AND fd[self] = FALSE) THEN
    Send(self, "COMMIT", proc)
    FORALL i IN Proc UNTIL i = self DO
      VoteForCrashAll(i)
  ELSE
    Abort(self)

\* a process aborts if it voted for the crash or received a NO message
OPERATION Abort(self) ==
  IF (<>[](\A i IN Proc : pc[i] = "NO") OR fd[self]) THEN
    FORALL i IN Proc UNTIL i = self DO
      VoteForCrashAll(i)

\* a process sends a YES message if it voted and received only YES messages from all processes
OPERATION SendYes(self) ==
  IF (<>[](\A i IN Proc : pc[i] = "YES") AND fd[self] = FALSE) THEN
    Send(self, "YES", proc)

\* a process sends a NO message if it voted and received a NO message from some process
OPERATION SendNo(self) ==
  IF (<>[](\A i IN Proc : pc[i] = "NO") AND fd[self]) THEN
    Send(self, "NO", proc)

\* a process does nothing but we need this to avoid deadlock
OPERATION DoNothing(self) ==
  IF (<>[](\A i IN Proc : pc[i] = "YES") AND fd[self] = FALSE) THEN
    FORALL i IN Proc UNTIL i = self DO
      VoteForCrashAll(i)

\* Some processes vote YES. Others vote NO. 
OPERATION VoteYesOrNo(self, proc) ==
  IF (<>[](\A i IN Proc : pc[i] = "YES") AND fd[self] = FALSE) THEN
    Send(self, "YES", proc)
  ELSE
    Send(self, "NO", proc)

\* Add the weak fainress condition
INVARIANT NonTriv ==
  (/\ \A i IN Proc : pc[i] = "YES"
  /\ [](\A i IN Proc : pc[i] # "CRASH"
  /\ (<>[](\A self IN Proc : fd[self] = FALSE))
  => <>(\A self IN Proc : pc[self] = "COMMIT")

=============================================================================
(* TLC Configuration                                                        *)
CONSTANT N = 2
INVARIANT TypeOK
SPECIFICATION Spec == []<>[](NonTriv)
=============================================================================
====