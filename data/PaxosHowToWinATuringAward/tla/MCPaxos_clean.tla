---- MODULE MCPaxos ----
EXTENDS Paxos, TLC

CONSTANT MaxBallot

CONSTANTS
a1, a2, a3
----

CONSTANTS
v1, v2
----

const_1560336937634605000 ==
{a1, a2, a3}
----

const_1560336937634606000 ==
{v1, v2}
----

const_1560336937634607000 ==
{{a1, a2}, {a1, a3}, {a2, a3}}
----

def_ov_1560336937634609000 ==
0..MaxBallot
----

def_ov_1560336937634610000 ==
0..MaxBallot
----

prop_1560336937635612000 ==
V!Spec
----
=============================================================================
