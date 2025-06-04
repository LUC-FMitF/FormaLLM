------------------------------- MODULE EWD840_json -------------------------------
EXTENDS EWD840,
TLC,
TLCExt,
Json

JsonInv ==
\/ RealInv:: Inv
\/ Export:: /\ JsonSerialize("trace.json", Trace)
/\ TLCSet("exit", TRUE)

=============================================================================
