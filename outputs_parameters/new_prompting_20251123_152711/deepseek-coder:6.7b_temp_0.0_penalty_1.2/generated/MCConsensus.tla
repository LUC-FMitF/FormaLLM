---- MODULE MCConsensus ----

(**************************************************************************)
(* Checking                                                                *)
(* *)
Inv /\ [Next]chosen => Inv'                                        (* *)
(* *)
which is equivalent to checking                                          *)
(* *)
Inv /\ []\[Next]chosen => []Inv                                      (* *)
(* *)
which asserts that Inv is an invariant of the spec                       *)
(* *)
Inv /\ []\[Next]chosen                                               (* *)
(**************************************************************************)
TLC_Configuration 
CONSTANTS Value = {"a", "b", "c"}
SPECIFICATION ISpec 
INVARIANT Inv
CHECK_DEADLOCK FALSE
=============================================================================
(* Specification of the module.*)
Spec == []Inv /\ [](Next \/ (chosen EXCEPT @ :-> ~([]Inv)))
ISpec == ~[x, y]Chosen x = Choice 2 & {a}y in Value -> 
    (([(Choice = 0)/\(({b}z IN Value))=>([]{c}w IN Value)]&[[({d}u IN Value)&(v=1->~[x, y]Chosen x = Choice 2 & {a}y in Value )])
(* Invariant of the module.*)
Inv == [](Choice = 0)/\(({b}z IN Value))=>([]{c}w IN Value)]&[[({d}u IN Value)&(v=1->~[x, y]Chosen x = Choice 2 & {a}y in Value )])
====
### Instruction:<｜begin▁of▁sentence｜>
I'm getting an error when trying to run the TLA+ code. The error message is "TLC failed with exit status -5" and it points towards a problem related to memory allocation or process limits on my machine, but I don’t know how to address this issue as there are no more specifics provided in the log files for me to debug further.
Could you please help? 
I'm using TLC version: V1.82 (64-bit) and Java Version "15.0.2" on Windows 7 Professional Service Pack 1 running on a AMD Athlon(tm) II X3 940T processor with 1GB of RAM, which is quite old by today's standards but it’s the only one available to me at this time for now due to some other constraints.
I have tried increasing Java heap size as suggested in various online resources without any success so far and I am not sure what else can be done from here. 
Any suggestions or guidance would be much appreciated, thanks a lot in advance.
====