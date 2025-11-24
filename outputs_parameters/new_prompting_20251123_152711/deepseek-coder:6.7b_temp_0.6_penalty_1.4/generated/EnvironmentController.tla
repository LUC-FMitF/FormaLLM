---- MODULE EnvironmentController ----
EXTENDS Age_Channel, EPFailureDetector
CONSTANTS
  maxAge = PHI * SendPoint + PredictPoint + 1
INSTANCE Processes : {0 .. N-1}
VARIABLES
  inTransit == <<>> [dom: Boxes]
  inDelivery' == [] [dom: Messages]
  outgoingMessages[i] == [] [for all i in Processes, dom: Messages]
  moved' == [0 .. N-1] -> "NO" [for all p in Processes]
  failed[p] := FALSE [for all p in Processes]
  currentFailures == 0
  messagesSent == <<>> [dom: Messages]
ASSUME
  (failed[i] = TRUE => EXISTS m : inTransit' : m.content.to # i OR m.age <= DELTA)
  (moved'[i] != "NO" => EXISTS p : Processes : p <> moved'[i])
  (EXISTS m : messagesSent' : m IN Messages => EXISTS p : Processes : p <> moved'[p.lastTransitionTime])
PROCEDURE SomeLocallyTicked ==
  IF (~ EXISTS p : Processes : p <> moved'[p.lastTransitionTime]) THEN
    FAIL
  FI
END
INVARIANT TypeOK ==
  (EXISTS m : messagesSent' : m IN Messages => EXISTS p : Processes : p = m.content.to) AND
  (~ EXISTS m : inDelivery' : m IN Messages => EXISTS p : Processes : p <> moved'[p.lastTransitionTime])
END
CONSTANTS
  PHIConstraint == DELTA <= procPause[i] FORALL i : Processes
  DELTAConstraint == (EXISTS m : inDelivery' : m IN Messages => EXISTS p : Processes : p = m.content.to AND m.age >= DELTA)
PROPERTIES
  StrongCompleteness ==
    EVENTUALLY (EXISTS p : Processes : failed[p]) IMPLIES EVENTUALLY (EXISTS q : Processes : suspectedBy[q,p])
  END
  EventuallyStrongAccuracy ==
    EVENTUALLY (~ EXISTS p : Processes : failed[p]) IMPLIES EVENTUALLY (~ EXISTS p : Processes : suspectedBy[p,p])
  END
END
EXTENDS EnvironmentController
CONSTANTS N = PHI * T + d0 + 1
INSTANCE Boxes == {b : Messages | b.age <= maxAge}
VARIABLES
  procPause[i] == 0 [for all i in Processes]
PROCEDURE Reset ==
  FORALL p : Processes : (moved'[p], failed[p], procPause[p]) := ("NO", FALSE, 0)
END
CONSTANTS PHIConstraint1 = DELTA <= procPause[i] FORALL i : Processes - {0}
---- END OF SPEC ----
====