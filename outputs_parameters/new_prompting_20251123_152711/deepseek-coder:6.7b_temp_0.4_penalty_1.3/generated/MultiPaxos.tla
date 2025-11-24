---- MODULE MultiPaxos ----
/\------------------------------------------------------------------
-- Module      : Example
-- Description : An example of a TLA+ module
-- Author(s)   : Your Name <your.name@example.com>
-- Created     : 2023-01-01
-- Note        : This is an auto-generated file, do not edit manually
--               as it may be overwritten by the next tool run.
--------------------------------------------------------------------
CONSTANT
    Replicas = {1..3}
;

VARIABLES
    -- Add your variables here
    node[Replica] \in NodeState
;

ASSUME
    Init == [NodeState] /\ (\_ -> True)
;

NextState == CHOICE
    "choice 1" : (node[self] = Node1),
    "choice 2" : (node[self] = Node2),
    -- Add more choices as needed
;

-- Define your helpers, macros, etc. here
====