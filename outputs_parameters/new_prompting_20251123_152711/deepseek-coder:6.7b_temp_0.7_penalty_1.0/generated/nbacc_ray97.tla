---- MODULE nbacc_ray97 ----


(* Modification History
   Last modified Mon Jul 09 13:26:03 CEST 2018 by tthai
   Created Thu Mar 12 00:46<｜begin▁of▁sentence｜>5 by igor
   TLA+ encoding of the algorithm NBAC with crashes in:
   [1] Raynal, Michel.  "A case study of agreement problems in distributed
   systems: non-blocking atomic commitment." High-Assurance Systems Engineering
   Workshop, 1997., Proceedings. IEEE, 1997.
   Igor Konnov, Thanh Hai Tran, Josef Widder, 2016
   This file is a subject to the license that is bundled together with this
   package and can be found in the file LICENSE. *)

CONSTANTS
   Proc == {0 .. N-1} (* processes *)

VARIABLES
   pc[Proc], fd[Proc] (* program counters, failure detector *)

(* messages which are received *)
PROCEDURE Receive(self, msg) ==
   IF fd[self] THEN
      (* failure detector reporting to every process whether some process has crashed *)
      fd[self] := FALSE
   ELSIF msg = "NO" AND pc[self] = "YES" THEN
      (* a process self becomes crash *)
      pc[self] := "CRASH"
   ELSIF msg = "YES" THEN
      (* sends a YES message *)
      pc[self] := "YES"
   ELSE
      (* sends a NO message *)
      pc[self] := "NO"

(* all processes, including the crashed ones *)
PROCEDURE AllProcesses ==
   [p |-> Receive(p, msg) : msg <> {}]

(* failure detector sending a nondeterministically new prediction to process self *)
PROCEDURE FailureDetector(self) ==
   IF fd[self] THEN
      (* process self becomes crash *)
      fd[self] := FALSE
   ELSE
      (* failure detector reporting to every process whether some process has crashed *)
      fd[self] := TRUE

(* The main specification *)
SPECIFICATION Spec ==
   [](<>AllProcesses[1, "YES"])
   /\ [](\A self ><\A i ><\A msg ><\A j ><\A k ><\A l ><\A m 
         : ((self >< i >< msg >< j >< k >< l >< m 
         : (self >< i >< msg >< j >< k >< l >< m : (self >< i >< msg >< j >< k >< l >< m : True))))
   )

INVARIANT TypeOK ==
   \A self ><\A i ><\A msg ><\A j ><\A k ><\A l ><\A m 
   : ((self >< i >< msg >< j >< k >< l >< m 
   : (self >< i >< msg >< j >< k >< l >< m : (self >< i >< msg >< j >< k >< l >< m : True))))

(* TLC Configuration *)
CONSTANT N = 2
====