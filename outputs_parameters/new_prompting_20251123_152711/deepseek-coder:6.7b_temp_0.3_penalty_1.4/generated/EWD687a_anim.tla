---- MODULE EWD687a_anim ----

(***************************************************************************)
(* Increasing refX moves the arrowhead to the middle of the line away from    *)
(* the tip. NodeDimension ought to be divisible by 2 for proper alignment     *)
(* of nodes and edges. round (rx=15) if node is active. A solid, black       *)
(* line with an arrow at its tip denotes an edge. %%03d to escape %03d in    *)
(* Java format strings.                                                     *)
(***************************************************************************)
LOCAL INSTANCE YourInstanceName  -- replace this with your instance name
  
\* The set of all processes
Procs == {L, P1, P2, P3, P4, P5}

\* A randomly generate network of processes.
Network == 
LET Edgs == SUBSET [ n \in (NodesOfNetwork \X NodesOfNetwork):  -- No self-loops and L is a source but never a sink
    /\ n[1] # n[2]
    /\ n[2] =/= L ]  
IN TLCEval(RandomElement(Edgs))
ASSUME PrintT(<<"Edges", Edges>>)  -- print the randomly chosen set of edges.

-- replace these with your invariants, actions etc.
CONSTANT Leader <- L
ACTIONS YourActionsName == {active |-> active}  
INVARIANT TypeOK(state) ==  (...)    (* type invariant *) 
OPERATION Spec(s) ==  (...)           (* specification for the module *)
PROPERTY DT2(s, t) ==  (...)          (* property to be checked during TLC run *)
-- replace these with your invariants etc.
\* CountersConsistent == \E x :: LeaderInv(x), ActiveProcs(x) : ...  -- invariant for counters consistency
\* TreeWithRoot == \A s, t :: RootTree(s,t): (...)                   (* property to check if the tree has a root *)
-- replace these with your invariants etc.
INVARIANT NoSuperfluousIdleSteps ==  (\E x : IdleStepInv(x))          -- no idle steps that leave variables unchanged 
\* StableUpEdge == \A s :: UpTree(s) /\ (...)                          (* property to check if the up edge is stable *)
-- replace these with your invariants etc.
OPERATION Alias ==  (\E x : ProcInv(x)) -- alias for process invariant 
CHECK_DEADLOCK FALSE   -- no deadlock in this module
ACTION_CONSTRAINT NoSuperfluousIdleSteps == (...)                      (* action constraint to prevent stuttering *)
\* Animated SVG visualization of the current TLA+ state. This is not a part 
of standard TLA+ and requires additional tools or libraries for rendering, etc.*)
====