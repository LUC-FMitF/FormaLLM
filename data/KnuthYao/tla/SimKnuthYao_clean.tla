----------------------------------------- MODULE SimKnuthYao -----------------------------------------
EXTENDS KnuthYao, Integers, Functions, CSV, TLC, TLCExt, IOUtils, Statistics

StatelessCrookedCoin ==

/\ IF RandomElement(1..8) \in 1..3
THEN /\ flip' = "T"

ELSE /\ flip' = "H"

----------------------------------------------------------------------------------------------------

StatefulCrookedCoin ==

/\ IF RandomElement(1..p.den) = 1
THEN flip' = "T"
ELSE flip' = "H"

----------------------------------------------------------------------------------------------------

SimInit ==
/\ state = "init"
/\ p     = One
/\ flip  \in Flip

SimNext ==

\/ /\ state = "init"
/\ state' = "s0"
/\ UNCHANGED p
/\ TossCoin
\/ /\ state # "init"
/\ state  \notin Done
/\ state' = Transition[state][flip]
/\ p' = Half(p)
/\ TossCoin

IsDyadic ==

IsDyadicRational(p)

----------------------------------------------------------------------------------------------------

ASSUME

/\ TLCGet("config").mode = "generate"

/\ TLCGet("config").depth >= 15 \/ TLCGet("config").depth = -1

/\ TLCGet("config").deadlock = FALSE

/\ TLCGet("revision").timestamp >= 1663720820

CSVFile ==
"SimKnuthYao.csv"

ASSUME

/\ CSVRecords(CSVFile) = 0 => CSVWrite("side,p,flip", <<>>, CSVFile)

/\ \A i \in Done: TLCSet(atoi(i), 0)

Stats ==

/\ state \in Done =>
/\ CSVWrite("%1$s,%2$s,%3$s", <<state, p.den, flip>>, CSVFile)
/\ TLCSet(atoi(state), TLCGet(atoi(state)) + 1)

/\ TLCGet("stats").traces % 250 = 0 =>
/\ IOExec(<<"/usr/bin/env", "Rscript", "SimKnuthYao.R", CSVFile>>).exitValue = 0

----------------------------------------------------------------------------------------------------

PostCondition ==

LET uniform == [ i \in 1..6 |-> 6 ]
samples == [ i \in Done |-> TLCGet(atoi(i)) ]
sum == FoldFunctionOnSet(+, 0, samples, Done)
IN /\ Assert(TLCGet("config").traces = sum, <<"Fewer samples than expected:", sum>>)
/\ Assert(ChiSquare(uniform, samples, "0.2"), <<"ChiSquare test failed:", samples>>)

====================================================================================================

$ rm *.csv ; tlc SimKnuthYao -note -generate -depth -1
