---------------------------- MODULE MCYoYoPruning ----------------------------
EXTENDS Integers

Nodes == 1 .. 5
Edges == {{1,2}, {1,5}, {3,4}, {3,5}, {4,5}}

VARIABLES active, phase, incoming, outgoing, mailbox

INSTANCE YoYoPruning

==============================================================================
