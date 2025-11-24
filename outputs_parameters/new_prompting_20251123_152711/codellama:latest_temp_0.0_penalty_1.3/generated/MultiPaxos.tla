---- MODULE MultiPaxos ----
MultiPaxos in state machine replication (SMR) style with write/read commands   *)
on a single key. Please refer to the detailed comments in PlusCal code to see  *)
how this spec closely models a practical SMR log replication system.           *)
*)
Network is modeled as a monotonic set of sent messages. This is a particularly *)
efficient model for a practical non-Byzantine asynchronous network: messages   *)
may be arbitrarily delayed, may be duplicatedly received, and may be lost (but *)
in this case the sender would repeatedly retry and thus the message should     *)
eventually gets received).                                                     *)
*)
Linearizability is checked from global client's point of view on the sequence  *)
of client observed request/acknowledgement events after termination.           *)
*)
Liveness is checked by not having deadlocks till observation of all requests.  *)
*)
Possible further extensions include node failure injection, leader lease and   *)
local read mechanism, etc.                                                     *)
******************************)
Model inputs & assumptions: *)
Ballots = {b \in Nat |-> b >= 0}; (* ballot numbers from proposers are unique*)
Commands = Writes U Reads;        (* write commands (each with a distinct value)*);
Slots = [1..NumCmd];          (* slots for pending requests/acks *)
Replicas = {r \in Nat |-> r >= 0};   (* replica IDs in the system*)
ObservedEvents = ReqEvent U AckEvent;(* events observed by clients: req, acks*);
MajorityNum = NumCmd div 2 + 1;                    *)
Allow infinite stuttering to prevent deadlock on termination. *] (*) [/INST_END];
====