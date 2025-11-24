---- MODULE nbacc_ray97 ----

LOCAL INSTANCE Processes
CONSTANT N = 2
VARIABLE pc[Processes] = "YES" -- program counters
VARIABLE fd[Processes] = TRUE -- failure detector

-- messages which are received
OPERATION Receive(self, msg) ==
  IF self IN Processes THEN
    CASE msg OF
      "NO": pc[self] = "NO"
      | _ : pc[self] = "YES"
    ENDCASE
  ENDIF

-- messages which are sent by the failure detector
OPERATION Send(self, msg) ==
  IF self IN Processes THEN
    fd[self] = FALSE
  ENDIF

-- a failure detector reporting to every process whether some process has crashed
INVARIANT FDInvariant == <>[](\A self  \in Processes : (pc[self] # "CRASH") => fd[self])

-- all processes, including the crashed ones
OPERATION AllProcesses(pc) == {p | p IN Processes}

-- Receive new messages
INVARIANT ReceiveInvariant == <>[](\A self  \in Processes : (Receive(self, "NO") /\ fd[self] = TRUE => pc[self] # "CRASH"))

-- The failure detector sends a nondeterministically new prediction to process self.
OPERATION FailureDetector(self) ==
  IF self IN Processes THEN
    CASE SELFSTATUS OF
      "CRASH": pc[self] = "CRASH"
      | _ : fd[self] = TRUE /\ CHOOSE msg IN {"YES", "NO"} /\ Send(self, msg)
    ENDCASE
  ENDIF

-- Sends a YES message
OPERATION YesMessage(self) == IF self IN Processes THEN pc[self] = "YES" ENDIF

-- Sends a NO message
OPERATION NoMessage(self) == IF self IN Processes THEN pc[self] = "NO" /\ fd[self] = FALSE ENDIF

INVARIANT AbortInvariant1 == ^[](\A self  \in Processes : (pc[self] = "YES" /\ NoMessage(self) => pc[self] # "ABORT"))

INVARIANT AbortInvariant2 == <>[](\A self  \in Processes : ((pc[self] = "YES" /\ fd[self] = TRUE) /\ (<>[](\A p \in AllProcesses(pc) : pc[p] # "CRASH")) => pc[self] # "ABORT"))

INVARIANT CommitInvariant == <>[](\A self  \in Processes : ((pc[self] = "YES" /\ fd[self] = TRUE) /\ (<>[](\A p \in AllProcesses(pc) : pc[p] = "YES")) => pc[self] = "COMMIT"))

-- Some processes vote YES. Others vote NO.
OPERATION Vote(self, msg) == IF self IN Processes THEN pc[self] = msg ENDIF

-- Add the weak fainress condition
INVARIANT WeakFairness == ^[](\A i \in Proc : (pc[i] = "YES" /\ fd[i] = TRUE))

SPECIFICATION Spec == []<>(ReceiveInvariant /\ FDInvariant) => <>(AbortInvariant1 /\ AbortInvariant2 /\ CommitInvariant)
=============================================================================
CONSTANT N = 2
INVARIANT TypeOK
SPECIFICATION Spec
====