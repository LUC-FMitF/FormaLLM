This modules demonstrates how to integrate TLC with third-party tools by
exporting counter-examples/error-traces.  You can ignore  MCInit  and  RealInv
and skip to  JsonInv  and  PostInv.

Run TLC in simulations/generator mode to quickly violate  RealInv  :

$ tlc -generate -noTE EWD998ChanID_export

------------------------ MODULE EWD998ChanID_export ------------------------
EXTENDS EWD998ChanID, TLCExt, TLC, IOUtils, Json

MCInit ==

/\ counter = [n \in Node |-> 0]
/\ inbox = [n \in Node |-> IF n = Initiator
THEN << [type |-> "tok", q |-> 0, color |-> "black" ] >>
ELSE <<>>]

/\ active \in [Node -> {TRUE}]
/\ color \in [Node -> {"white"}]

/\ clock = [n \in Node |-> [m \in Node |-> 0] ]

----------------------------------------------------------------------------

RealInv ==

EWD998Chan!EWD998!terminationDetected => TLCGet("level") < 23

----------------------------------------------------------------------------

JsonInv ==
\/ RealInv
\/ /\ JsonSerialize("EWD998ChanID_export.json", Trace)
/\ Print("JSON trace written to EWD998ChanID_export.json",
FALSE)

----------------------------------------------------------------------------

Curl ==
<<"curl", "-H", "Content-Type:application/json",
"-X", "POST", "-d", "%s", "https://postman-echo.com/post">>

PostInv ==
\/ RealInv
\/ Print(
IOExecTemplate(Curl, <<ToJsonObject(Trace)>>).stdout,
FALSE)

=============================================================================
