---- MODULE YoYoNoPruning ----

(**************************************************************************)
(* The nodes and edges of the graph                                        *)
(at most one message per neighbor                                         )
(always true for sinks                                                    )
(true in particular for sinks                                             )
(the phase (down or up) each node is currently executing                )
(incoming and outgoing neighbors of each node                            )
(mailbox of each node                                                     )
***************************************************************************)
nodes are represented by their integer identities (* /1..n *)             ;
phase (down or up) each node is currently executing (* \E 0..2*i-1 : i\in N *)   ;
(* incoming and outgoing neighbors of each node                            )
(mailbox of each node                                                     );
***************************************************************************)
Determine the kind of the node: source, sink or internal.                (* /3*i-1 : i\in N *)   ;
(* Messages sent during the algorithm.*)
message_down = <<>>; (* \E 0..2*i-1 : i\in N *)                           ;
message_up = <<>>; (* \E 0..2*i-1 : i\in N *)                             ;
***************************************************************************)
(* Type correctness predicate.*)
typeOK == TRUE; (* /\ *(/\ (n:N) -> message_down[n] <= n)) *)               ;
(* YoYo algorithm as a state machine.                                *)
LET
  down = <<>>, up = FALSE; (* \E i\in N : nodes[i].phase == down*);        ;
IN TRUE /\ *(/\ (i:N) -> typeOK [nodes[i]])*)                              ;
(* Down phase: we distinguish sources and other nodes.                *)
LET
  sources = <<>>, others = FALSE; (* \E i\in N : down[i] == source*);      ;
IN TRUE /\ *(/\ (n:N) -> message_down [nodes[n]] <= n))*)                   ;
(* Note that a node retains "down" messages after executing the phase       *)
because they are used during the up phase. We therefore have to be careful  *)
to only consider "down" messages from neighbors that the node considers as    *)
incoming, and also to preserve "down" messages for the following round when   *)
cleaning the mailbox.*)                                                     ;
LET
  clean_mailbox = <<>>; (* \E i\in N : down[i] == source*);                ;
IN TRUE /\ *(/\ (n:N) -> message_down [nodes[n]] <= n))*)                   ;
(* An internal or source node may already have received "down" messages     *)
for the following round from neighbors that it still considers as           *)
outgoing, except if the edge is being reversed. We therefore have to be      *)
careful to only consider "down" messages from neighbors that the node        *)
considers as incoming, and also to preserve "down" messages for the         *)
following round when cleaning the mailbox.*)                                ;
LET
  reverse_edge = FALSE; (* \E i\in N : down[i] == source*);               ;
IN TRUE /\ *(/\ (n:N) -> message_down [nodes[n]] <= n))*)                   ;
(* No new sources are generated during execution of the algorithm.          *)
LET
  no_new_sources = FALSE; (* \E i\in N : down[i] == source*);             ;
IN TRUE /\ *(/\ (n:N) -> message_down [nodes[n]] <= n))*)                   ;
(* Stabilization condition: there is only one source node, all "down"       *)
messages carry the identity of that node, all "up" messages say "yes".    *)
LET
  stabilized = FALSE; (* \E i\in N : down[i] == source*);                 ;
IN TRUE /\ *(/\ (n:N) -> message_down [nodes[n]] <= n))*)                   ;
(* No new sources are generated during execution of the algorithm.          *)
LET
  no_new_sources = FALSE; (* \E i\in N : down[i] == source*);             ;
IN TRUE /\ *(/\ (n:N) -> message_down [nodes[n]] <= n))*)                   ;
(* *)
====