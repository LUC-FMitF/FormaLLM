----------------------------------------- MODULE KnuthYao -----------------------------------------
EXTENDS DyadicRationals

VARIABLES p,
state,
flip

vars == <<p, state, flip>>

Done == {"1", "2", "3", "4", "5", "6"}
Flip == { "H", "T" }

Transition == [s0 |-> [H |-> "s1", T |-> "s2"],
s1 |-> [H |-> "s3", T |-> "s4"],
s2 |-> [H |-> "s5", T |-> "s6"],
s3 |-> [H |-> "s1", T |-> "1" ],
s4 |-> [H |-> "2",  T |-> "3" ],
s5 |-> [H |-> "4",  T |-> "5" ],
s6 |-> [H |-> "6",  T |-> "s2"]]

TossCoin == flip' \in Flip

Init == /\ state = "s0"
/\ p     = One
/\ flip  \in Flip

Next == /\ state  \notin Done
/\ state' = Transition[state][flip]
/\ p' = Half(p)
/\ TossCoin

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====================================================================================================
