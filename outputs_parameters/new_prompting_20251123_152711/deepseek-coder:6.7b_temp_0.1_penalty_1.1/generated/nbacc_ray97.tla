---- MODULE nbacc_ray97 ----

(***************************************************************************)
(* TLA+ encoding of the algorithm NBAC with crashes in:
[1] Raynal, Michel.  "A case study of agreement problems in distributed
systems: non-blocking atomic commitment." High-Assurance Systems Engineering
Workshop, 1997., Proceedings. IEEE, 1997.
Igor Konnov, Thanh Hai Tran, Josef Widder, 2016
This file is a subject to the license that is bundled together with this
package and can be found in the file LICENSE.
*)
(***************************************************************************)

CONSTANT N 

\* program counters
LOCAL INSTANCE ProgramCounters
  [i \in 0..(N-1)] -> { "YES", "NO", "CRASH" }

\* messages which are received
LOCAL INSTANCE ReceivedMessages
  [i \in 0..(N-1)] -> { "YES", "NO" }

\* messages which are sent by
LOCAL INSTANCE SentMessages
  [i \in <｜begin▁of▁sentence｜>..(N-1)] -> { "YES", "NO" }

\* a failure detector reporting to every process
LOCAL INSTANCE FailureDetector
  [i \in 0..(N-1)] -> { TRUE, FALSE }

\* whether some process has crashed
LOCAL INSTANCE CrashedProcesses
  [i \in 0..(N-1)] -> { TRUE, FALSE }

\* all processes, including the crashed ones
LOCAL INSTANCE AllProcesses
  [i \in 0..(N-1)] -> { "YES", "NO", "CRASH" }

\* Receive new messages
LOCAL INSTANCE NewMessages
  [i \in 0..(N-1)] -> { "YES", "NO" }

\* The failure detector sends a nondeterministically new prediction to process self.
LOCAL INSTANCE NewPrediction
  [i \in 0..(N-1)] -> { "YES", "NO" }

\* Process self becomes crash.
LOCAL INSTANCE SelfCrash
  [i \in 0..(N-1)] -> { TRUE, FALSE }

\* Sends a YES message
LOCAL INSTANCE SendYes
  [i \in 0..(N-1)] -> { TRUE, FALSE }

\* Sends a NO message
LOCAL INSTANCE SendNo
  [i \in 0..(N-1)] -> { TRUE, FALSE }

\* Some processes vote YES. Others vote NO.
LOCAL INSTANCE Vote
  [i \in 0..(N-1)] -> { "YES", "NO" }

\* Add the weak fainress condition
LOCAL INSTANCE WeakFairness
  [i \in 0..(N-1)] -> { TRUE, FALSE }

\* NonTriv
LOCAL NonTriv
  ==
  (  /\  \A i \in Proc : pc[i] = "YES"
  /\  [](\A i \in Proc : pc[i] # "CRASH"
  /\  (<>[](\A self \in Proc : (fd[self] = FALSE)))
  => <>(\A self \in Proc : (pc[self] = "COMMIT"))
  )

=============================================================================
====

(* TLC Configuration *)
CONSTANT N = 2
INVARIANT TypeOK
SPECIFICATION NonTriv
====