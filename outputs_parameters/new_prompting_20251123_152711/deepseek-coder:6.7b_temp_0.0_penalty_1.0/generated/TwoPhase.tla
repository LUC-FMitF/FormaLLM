---- MODULE TwoPhase -------------------------------
EXTENDS Alternate
CONSTANTS RM = {r1, r2, r3}
VARIABLES vBar == [p, c] \in XInit /\ [p, c] -> [XAct[v], XAct[c]]

Init == 
  TPInit /\ Inv(<<>>)
Next == 
  (TPNext[vBar]) /\ Inv([p, c] \in XInit /\ [p, c] -> [XAct[v], XAct[c]])
Spec == Init /\ [][]_<<vBar>>[TPNext[vBar]]

====