------------------------------- MODULE SmokeEWD998_SC -------------------------------
EXTENDS Naturals, TLC, IOUtils, CSV, Sequences, FiniteSets

CSVFile ==
"SmokeEWD998_SC" \o ToString(JavaTime) \o ".csv"

ASSUME
CSVWrite("BugFlags#Violation", <<>>, CSVFile)

Cmd == LET absolutePathOfTLC == TLCGet("config").install
IN <<"java", "-jar",
absolutePathOfTLC,
"-noTE",
"-simulate",
"SmokeEWD998.tla">>

ASSUME \A i \in 1..30 : \A bf \in SUBSET (1..6) : Cardinality(bf) # 1 \/
LET ret == IOEnvExec([BF |-> bf, Out |-> CSVFile, PN |-> RandomElement(3..4)], Cmd)
IN /\  CASE ret.exitValue =  0 -> PrintT(<<JavaTime, bf>>)
[] ret.exitValue = 10 -> PrintT(<<bf, "Assumption violation">>)
[] ret.exitValue = 12 -> PrintT(<<bf, "Invariant violation (Inv)">>)
[] ret.exitValue = 13 -> PrintT(<<bf, "Property violation (TDSpec)">>)

[] OTHER    -> PrintT(ret)
/\  CSVWrite("%1$s#%2$s", <<bf, ret.exitValue>>, CSVFile)

===============================================================================
