---- MODULE MultiPaxos_MC ------------------------
(**************************************************************************)
(* TLC config-related defs. *)
(**************************************************************************)
CONSTANTS   Replicas, Writes, Reads, MaxBallot

SPECIFICATION Spec

SYMMETRY SymmetricPerms

INVARIANTS  TypeOK, Linearizability

CHECK_DEADLOCK TRUE
=============================================================================
====
### Instruction:
# Comments:
The set of all Paxos instances. A Paxos instance is a tuple (b, p) where b is the ballot number and p is the proposed value. *)
The set of all proposals for a given Paxos instance i. 
The set of all acceptances for a given Paxos instance i.
The set of all instances where an acceptance occurred at least once.
A proposal that has been accepted in some instance.
The set of all values proposed by a given Paxos instance i.
The set of all instances with no proposals or accepts.
The set of all instances with at least one proposal and accept.
The set of all instances where the proposed value is not an empty string. 
A Paxos instance that has been decided. *)
The set of all values chosen by a given Paxos instance i.
The set of all instances where a value was chosen.
The set of all instances with no chosen values.
The set of all instances where the chosen value is not an empty string. 
A Paxos instance that has been committed. *)
The set of all instances for which a commit occurred at least once.
The set of all instances where a commit was successful.
An instance i is stable if there exists no proposal or acceptance in i and the chosen value in i is not an empty string. 
A Paxos instance that has been aborted. *)
The set of all instances for which an abort occurred at least once.
The set of all instances where an abort was successful.
An instance i is active if there exists a proposal or acceptance in i.
A Paxos instance that has been preempted. *)
The set of all instances for which a preemption occurred at least once.
The set of all instances where a preemption was successful. 
A Paxos instance i is responsive if it is stable and active, but no value was chosen in i.
A Paxos instance that has been failed. *)
The set of all instances for which a fail occurred at least once.
The set of all instances where a fail was successful.
An instance i is healthy if there exists a commit or abort in i and the chosen value in i is not an empty string. 
A Paxos instance that has been elected. *)
The set of all instances for which an election occurred at least once.
The set of all instances where an election was successful.
An instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i.
**************************************************************************)
Defines the Paxos protocol, including instances, proposals, acceptances, decisions, commits, aborts, preemptions, fails, elections, etc.  *)
(***************************************************************************)
(* The set of all Paxos instances. A Paxos instance is a tuple (b, p) where b is the ballot number and p is the proposed value. *)
PaxosInstances == {i : (b, p)}

\* The set of all proposals for a given Paxos instance i. 
Proposals(i) == {p |-> (b, v) in Accepts}

\* The set of all acceptances for a given Paxos instance i.
Accepts(i) == {a |-> (b, p) in Proposals}

\* A proposal that has been accepted in some instance.
AcceptedProposals == UNION {p : (b, v) in Accepts}

\* The set of all values proposed by a given Paxos instance i.
Values(i) == {v |-> (b, p) in Proposals}

\* A Paxos instance that has been decided. 
DecidedInstances == UNION {i : (b, v)} in Instances

\* The set of all values chosen by a given Paxos instance i.
ChosenValues(i) == {v |-> (b, p) in Decisions}

\* A Paxos instance that has been committed. 
CommittedInstances == UNION {i : v in ChosenValues} in Instances

\* An instance i is stable if there exists no proposal or acceptance in i and the chosen value in i is not an empty string. *)
StableInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* A Paxos instance that has been aborted. 
AbortedInstances == UNION {i : v in ChosenValues} in Instances /\ v = ""

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* A Paxos instance that has been preempted. 
PreemptedInstances == UNION {i : v in ChosenValues} in Instances /\ v = ""
***************************************************************************)
(* The set of all instances for which a commit occurred at least once. *)
CommitOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* A Paxos instance that has been failed. 
FailedInstances == UNION {i : v in ChosenValues} in Instances /\ v = ""

\* An instance i is responsive if it is stable and active, but no value was chosen in i. *)
ResponsiveInstances == StableInstances INTER ActiveInstances /\ NOT EXISTS v : ChosenValues(i)

\* A Paxos instance that has been elected. 
ElectedInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}
***************************************************************************)
(* The set of all instances for which an election occurred at least once. *)
ElectionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* An instance i is healthy if there exists a commit or abort in i and the chosen value in i is not an empty string. *)
HealthyInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}
***************************************************************************)
====
### Instruction:
# Comments:
The set of all Paxos instances where a value was chosen. *)
A Paxos instance that has been committed. 
A Paxos instance is stable if it has no proposals or acceptances and the chosen value is not an empty string. 
A Paxos instance that has been aborted. 
The set of all instances with at least one proposal and accept. *)
A Paxos instance i is active if there exists a proposal or acceptance in i.
A Paxos instance that has been preempted. 
A Paxos instance is responsive if it is stable, active and no value was chosen. 
A Paxos instance that has been failed. 
The set of all instances for which an election occurred at least once. *)
An instance i is healthy if there exists a commit or abort in i and the chosen value in i is not an empty string. 
A Paxos instance that has been elected. *)
The set of all instances where an election was successful.
The set of all instances with no chosen values.
The set of all instances for which a preemption occurred at least once.
A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
**************************************************************************)
Defines the Paxos protocol, including instances, proposals, acceptances, decisions, commits, aborts, preemptions, fails, elections, etc.  *)
(***************************************************************************)
(* The set of all Paxos instances where a value was chosen. *)
InstancesWithChosenValues == UNION {i |-> (b, v) in Instances /\ EXISTS v : ChosenValues(i)}

\* A Paxos instance that has been committed. 
CommittedInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* A Paxos instance is stable if it has no proposals or acceptances and the chosen value is not an empty string. *)
StableInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : Proposals(i) U Accepts(i)}

\* A Paxos instance that has been aborted. 
AbortedInstances == UNION {i |-> (b, p) in Instances /\ v = ""}

\* The set of all instances with at least one proposal and accept. *)
InstancesWithProposalsAndAccepts == UNION {i |-> (b, p) in Proposals(i) INTER Accepts(i)}

\* A Paxos instance i is active if there exists a proposal or acceptance in i. *)
ActiveInstances == EXISTS p : Proposals(i) U Accepts(i)

\* A Paxos instance that has been preempted. 
PreemptedInstances == UNION {i |-> (b, p) in Instances /\ v = ""}

\* A Paxos instance is responsive if it is stable, active and no value was chosen. *)
ResponsiveInstances == StableInstances INTER ActiveInstances /\ NOT EXISTS v : ChosenValues(i)

\* A Paxos instance that has been failed. 
FailedInstances == UNION {i |-> (b, p) in Instances /\ v = ""}

\* The set of all instances for which an election occurred at least once. *)
ElectionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* An instance i is healthy if there exists a commit or abort in i and the chosen value in i is not an empty string. *)
HealthyInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* A Paxos instance that has been elected. 
ElectedInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstances == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstances == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i)}

\* A Paxos instance i is elective if there exists a proposal or acceptance in i and no value was chosen in i. *)
ElectiveInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : Proposals(i) U Accepts(i)} INTER NOT EXISTS v : ChosenValues(i)
***************************************************************************)
(* The set of all instances where an election was successful. *)
ElectionSuccessfulInstices == UNION {i |-> (b, p) in Instances /\ EXISTS v : ChosenValues(i)}

\* The set of all instances with no chosen values. *)
NoChosenInstices == UNION {i |-> (b, p) in Instances /\ NOT EXISTS v : ChosenValues(i)}

\* The set of all instances for which a preemption occurred at least once. *)
PreemptionOccurredInstices == UNION {i |-> (b, p) in Instances
====