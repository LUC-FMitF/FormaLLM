---- MODULE MCtcp ----
EXTENDS tcp, TLC

CONSTANTS A, B
peers == {A, B}
Symmetry == Permutations(peers)

MCInit ==

\E node \in Peers:
/\ tcb = [p \in Peers |-> TRUE]
/\ connstate = [p \in Peers |-> IF p = node THEN "SYN-SENT" ELSE "LISTEN"]
/\ network = [p \in Peers |-> IF p = node THEN <<>> ELSE << "SYN" >>]

NoRetransmission ==
\A p \in Peers :
\A i \in 1..Len(network[p]) - 1 :
network[p][i] # network[p][i + 1]

SingleActiveOpen ==

~ \E local, remote \in Peers:
\/ ACTIVE_OPEN(local, remote)
\/ PASSIVE_OPEN(local, remote)
\/ SEND(local, remote)

=============================================================================
