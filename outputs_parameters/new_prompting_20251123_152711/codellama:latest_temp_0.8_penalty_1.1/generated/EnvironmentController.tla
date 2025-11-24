---- MODULE EnvironmentController ----
CONSTANTS
  N = 3                   -- number of processes
  T = 1                    -- maximum time-out interval for all delta(p)(q)
  d0 = 2                   -- default value of message delay in partial synchrony
  SendPoint = 2             -- the point at which a process can send alive messages to others
  PredictPoint = 3          -- the point at which every correct process makes predictions about failures
  DELTA = PHI = 1           -- upper bound of message delay and relative speeds of different processes in partial synchrony
VARIABLES
  failed[i]                -- a set of processes that crashed
  nofailures               -- the number of current failures
  outgoingMessages[i]      -- a set of messages sent by correct processes
  moved'[i][t'] = INIT     -- how long a process p_i has not taken a transition in this tick
  procPause'[i] = 0        -- the last transition that a process p_i take
  fromLastHeard[i][j]      -- How many times the message sent by correct processes have been picked up. If the number of pickups is greater than delta(p)(q), then procPause'[i] = 0.
ASSUMPTIONS
  SendPoint # PredictPoint since a process cannot both send messages and receive messages in one transition.
  PredictPoint % SendPoint # 0 /\ SendPoint % PredictPoint # 0 : the operation Predict cannot subsume the operation Predict and vice versa.
SPECIFICATION Spec
PROPERTY StrongCompleteness
ASSUMPTION failed[i] = TRUE => ( \A m \in outgoingMessages[i]: \/ m.content.to # i /\ m.age <= DELTA )
PROPERTY EventuallyStrongAccuracy
ASSUMPTION nofailures < N - 1
INVARIANT TypeOK
CONSTRAINT PHIConstraint
PREDICATE PHI(i, t) == ( \A p : procPause[p] > PHI => moved'[p][t'] = INIT )
CONSTRAINT DELTAConstraint
PREDICATE DELTA(m, i, j) == ( m.content.to # j /\ m.age <= DELTA => fromLastHeard[i][j] >= 1 )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause'[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint1
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
INVARIANT TypeOK
CONSTRAINT PHIConstraint2
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint3
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
INVARIANT TypeOK
CONSTRAINT PHIConstraint4
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint5
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint6
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint7
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint8
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint9
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint10
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint11
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint12
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint13
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint14
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint15
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint16
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint17
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint18
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint19
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint20
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint21
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint22
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint23
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint24
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint25
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint26
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint27
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint28
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint29
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint30
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint31
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint32
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint33
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint34
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint35
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint36
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint37
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint38
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint39
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint40
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint41
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INI▁<SUF>> T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint45
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint46
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint47
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint48
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint49
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint50
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint51
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint52
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint53
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint54
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint55
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint56
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint57
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint58
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint59
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint60
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint61
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint62
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint63
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint64
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint65
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint66
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint67
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint68
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint69
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint70
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint71
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint72
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint73
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint74
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint75
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint76
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint77
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint78
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint79
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint80
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint81
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint82
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint83
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint84
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint85
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint86
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint87
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint88
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint89
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint90
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint91
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint92
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint93
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint94
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint95
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint96
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint97
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint98
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint99
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
-------------------
CONSTRAINT PHIConstraint100
PREDICATE PHI(i, t) == ( \A p : procPause'[p] > PHI => moved'[p][t'] = INIT )
FUNCTION SomeLocallyTicked() = \E t : t > T -> (\A p: procPause[p] != INIT ==> moved'[p][t'] = INIT)
INITIALIZATION
  nofailures := N - 1
  outgoingMessages := { }
  failed := {}
  FORALL i, j : (outgoingMessages[i].content.to # j -> fromLastHeard[j][i] >= 1 )
TRANSITION
  moved' := INIT
  procPause' := INIT
  outgoingMessages' := { }
  failed' := {}
FORALL i, t : (moved'[i][t] = INIT <-> nofailures > N - 1) /\ (procPause'[i] != INIT <-> nofailures > N - 1)
FORALL i, j: (fromLastHeard[i][j] >= 1 -> procPause'[i] = 0 )
FORALL m : (m.age <= DELTA \/ m.content.to # j /\ fromLastHeard[j][i] >= delta(p)(q) )
====