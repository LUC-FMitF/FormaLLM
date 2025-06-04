----------------------------- MODULE EWD998_optsSC -----------------------------
EXTENDS TLC, IOUtils, Naturals, Sequences, CSV

Features ==

{"pt1","pt2","pt3","pt4","pt5"}

Nodes ==
{7,29,43}

-----------------------------------------------------------------------------

CSVFile ==
"EWD998_opts_" \o ToString(JavaTime) \o ".csv"

ASSUME
CSVWrite("Variant#Node#Length#T#T2TD#InitiateProbe#PassToken#SendMsg#RecvMsg#Deactivate",
<<>>, CSVFile)

Cmd == LET absolutePathOfTLC == TLCGet("config").install
IN <<"java", "-jar",
absolutePathOfTLC,
"-deadlock", "-noTE",
"-depth", "-1",
"-workers", "auto",
"-generate", "num=10",
"-config", "EWD998_opts.tla",
"EWD998_opts.tla">>

ASSUME \A features \in SUBSET Features:
\A n \in Nodes:
LET ret == IOEnvExec([N |-> n, F |-> features, Out |-> CSVFile], Cmd).exitValue
IN CASE ret =  0 -> PrintT(<<JavaTime, n, features>>)
[] ret = 10 -> PrintT(<<n, features, "Assumption violation">>)
[] ret = 12 -> PrintT(<<n, features, "Safety violation">>)
[] ret = 13 -> PrintT(<<n, features, "Liveness violation">>)

[] OTHER    -> Print(<<n, features,
IOEnvExec([N |-> n, F |-> features, Out |-> CSVFile], Cmd),
"Error">>, FALSE)

=============================================================================
---- CONFIG EWD998_optsSC ----

====

$ tlc -config EWD998_optsSC.tla EWD998_optsSC.tla
