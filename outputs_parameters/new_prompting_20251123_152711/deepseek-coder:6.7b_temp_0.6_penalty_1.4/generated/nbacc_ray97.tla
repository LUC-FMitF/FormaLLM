---- MODULE nbacc_ray97 ----
EXTENDS FiniteSets, Integers1

(* Modification History *)
(* Last modified Mon Jul 09 13:26:03 CEST 2018 by tthai *)
(* Created Thu Mar 12 00:46<｜begin▁of▁sentence｜>&%$# CET 2015 by igor *)
(* TLA+ encoding of the algorithm NBAC with crashes in: [1] Raynal, Michel. "A case study of agreement problems in distributed systems: non-blocking atomic commitment." High-Assurance Systems Engineering Workshop, 1997., Proceedings. IEEE, 1997. *)
(* Igor Konnov, Thanh Hai Tran, Josef Widder, 2016 *)
(* This file is a subject to the license that is bundled together with this package and can be found in the file LICENSE. *)

CONSTANT Proc = {...} (* Set of processes *)
VARIABLE msg[Proc] = [<..> : p \in Proc] (* Messages received by each process *)
VARIABLE fd[Proc] = [<..> : p \in Proc] (* Failure detector state for each process *)
VARIABLE pc[Proc] = [<..> : p \in Proc] (* Process-local counters *)

(* Messages which are received by a process *)
RECEIVE(p, m) == msg[p] <- {...} /\ fd[p] <- TRUE

(* Messages which are sent by a process *)
SEND(m) == [<..> : p \in Proc] /\ pc[p] <- "YES" /\ EXISTS self \in Proc: (pc[self] = "CRASH") -> abort

(* Failure detector reporting to every process *)
FAILURE(p) == fd[p] <- TRUE /\ EXISTS self \in Proc : (fd[self] = FALSE) -> pc[p] <- "COMMIT"

(* All processes, including the crashed ones *)
ProcIncCrashes == [<..> : p \in Proc] /\ fd[p] = TRUE

(* Process self votes YES. Others vote NO. *)
VoteYES(self) == pc[self] <- "YES" /\ EXISTS q \in Proc - {self} : pc[q] <- "NO"

(* Some process has crashed *)
ProcessCrashed == EXISTS p \in Proc: fd[p] = FALSE

(* Add the weak faith condition *)
INVARIANT NonTriv == [[](pc[self] # "CRASH") -> [](\A self \in Proc : pc[self] = "COMMIT")] /\ EXISTS self \in Proc : (fd[self] = FALSE) => (<>[](\A self \in Proc : pc[self] = "COMMIT"))

(* Specification *)
SPECIFICATION Spec == [](ProcIncCrashes U (VoteYES(self) /\ FAILURE(self)))

(* TLC Configuration *)
CONSTANT N = 2 (* Number of processes *)
INVARIANT TypeOK == MOD(#Proc, 2) = 0 (* Ensure that the number of processes is even *)
SPECIFICATION Spec
====