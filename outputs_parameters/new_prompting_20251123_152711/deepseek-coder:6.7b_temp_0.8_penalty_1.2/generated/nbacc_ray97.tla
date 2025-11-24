---- MODULE nbacc_ray97 ----

(******************************************************************************)
(* TLA+ encoding of the algorithm NBAC with crashes in:                       *)
(* [1] Raynal, Michel. "A case study of agreement problems in distributed     *)
(* systems: non-blocking atomic commitment." High-Assurance Systems Engineering*)
(* Workshop, 1997., Proceedings. IEEE, 1997.                                  *)
(* Igor Konnov, Thanh Hai Tran, Josef Widder, 2016                            *)
(******************************************************************************)

EXTENDS FiniteSets, Naturals, ZSequences

CONSTANTS
    N == 2

VARIABLES
    Proc == {0 .. N-1}       (* processes                          *)
    pc[Proc] == "YES"        (* process counters (votes)            *)
    fd[Proc] == FALSE         (* failure detector report             *)
    msg[Proc] == {}           (* messages received by each process   *)

ASSUME
    NonTriv == 
       (/\ \A i \in Proc : pc[i] = "YES" 
       /\ [](\A i \in Proc : pc[i] # "CRASH"
       /\ (<>[](\A self \in Proc : fd[self] = FALSE))
       => <>(\A self \in Proc : pc[self] = "COMMIT")) 

OPERATIONS
    Receive(p) == 
        [i \in Proc |-> 
            IF i = p THEN msg[p] \ {m} ELSE msg[i]]

    Send(p, m) ==
         [i \in Proc |->
             IF i = p THEN Union(msg[p], {m}) ELSE msg[i]]

SPECIFICATION 
     NonTriv /\ <>  [] (\A self \in Proc : (fd[self] = FALSE) => pc[self] = "COMMIT")

INVARIANT TypeOK == MODULE NBAC == {Proc, pc, fd, msg}

OPERATIONALS 
    Process(p) == 
        IF p \in Proc THEN
            [i \in Proc |->
                IF i = p THEN (fd[p] = FALSE ; []msg[p] = {} ) ELSE ()]fd[p] = TRUE ]
        
        OTHERWISE 
           []Proc = {p} /\ fd[p] = FALSE /\ msg[p] = {}
            
    FailureDetector(p) == 
         IF <>[](\A q \in Proc : (q != p ) => (fd[q] = TRUE)) THEN 
            [self \in Proc |-> fd[self] = TRUE ]
          ELSE 
             []fd[p] = FALSE

    ReceiveNewMessages(p) == 
        IF <>[](\A q \in Proc : (q != p ) => (msg[q] \ {} = msg[q])) THEN 
           [self \in Proc |-> msg[self] = Receive(self)]
         ELSE 
            []<>[](\A self \in Proc : (fd[self] = TRUE)) 
            => <>(\A self \in Proc : ((pc[self] = "COMMIT") OR (pc[self]  = "ABORT")))
    
    Vote(p, vote) == 
        [i \in Proc |->  IF i= p THEN pc[i] =  vote ELSE []pc[i] = pc[i]] 

    CommitAbort(p) ==
      IF <>[](\A q \in Proc : (q != p ) => ((pc[q]  = "COMMIT") OR (pc[q]  = "ABORT"))) THEN  
        [self \in Proc |-> 
            IF  pc[self] = "NO" AND <>[](\A q \in Proc :(pc[q] = "CRASH"))  THEN 
                pc[self] =  "ABORT" 
            ELSE 
                []fd[self] = TRUE /\ (<>[](\A self \in Proc : (fd[self] = FALSE))) => pc[self]  = "COMMIT"]
      ELSE 
         []pc[p] = "NO"  

    AddWeakFaultTolerance(p) ==
        IF <>[](\A q \in Proc : ((q != p ) AND (pc[q] = "YES")) => pc[p] = "CRASH") THEN 
           [self \in Proc |->  pc[self]  = "NO" ]  
      ELSE 
        []<>[](\A self \in Proc : ((pc[self] = "COMMIT") OR (pc[self]  = "ABORT"))) =>  <>[](\A self \in Proc :((pc[self] = "YES") OR (pc[self]  = "CRASH")))
====