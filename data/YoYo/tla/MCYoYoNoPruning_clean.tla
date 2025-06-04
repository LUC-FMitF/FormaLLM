--------------------------- MODULE MCYoYoNoPruning ---------------------------
EXTENDS Integers

Nodes == 1 .. 5
Edges == {{1,2}, {1,5}, {3,4}, {3,5}, {4,5}}

VARIABLES phase, incoming, outgoing, mailbox

INSTANCE YoYoNoPruning

==============================================================================
