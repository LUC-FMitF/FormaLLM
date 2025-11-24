---- MODULE EWD687a_anim ----
EXTENDS TLC

CONSTANTS
    L   = "L"   /\* Leader *\/,
    P1  = "P1",
    P2  = "P2",
    P3  = "P3",
    P4  = "P4",
    P5  = "P5"  /\* Nodes of network *\/;

ASSUME Network == LET Edges == SUBSET { n \in (NodesOfNetwork \X NodesOfNetwork) :
  /* No self-loops */
  n[1] # n[2] 
  /* L is a source and never a sink */
  n[2] # L 
} IN TLCEval(RandomElement(Edges)) /\* Randomly generate network of processes *\/;

LOCAL FUNCTION NodesOfNetwork == {L, P1, P2, P3, P4, P5};

VARIABLES
    active, sentUnacked, rcvdUnacked, msgs, acks /\* ... and other variables *\/;

NEXT(active)    == CASE active \in {TRUE, FALSE} -> !active END;  // assuming process toggles active status
NEXT(sentUnacked) == /* ... and similar for sentUnacked, rcvdUnacked, msgs, acks */;

OPERATOR Table == [ Procs \in NodesOfNetwork |-> {x: Nat, y: Nat} ]; // Operator to map processes to coordinates

SPECIFICATION Spec /\* ... and other specifications *\/; 

INVARIANT TypeOK       == /* type invariants */;
INVARIANT DT1Inv      == /* dynamic type invariant */;
INVARIANT InterestingBehavior == /* interesting behavior invariant */;

PROPERTY DT2        == /* ... and other properties *\/; 
/* PROPERTY CountersConsistent   == ..... */
/* PROPERTY TreeWithRoot       == ..... */
/* PROPERTY StableUpEdge      == ..... */

ALIAS Alias == { active |-> active, /* and similar for other variables */ }; 

CHECK_DEADLOCK FALSE; /\* No deadlock in this module *\/.

ACTION_CONSTRAINT NoSuperfluousIdleSteps == 
    CASE Process \in NodesOfNetwork : (active' = active) /\ (!ProcessChange) -> !(active' \in {TRUE, FALSE}) END; // Avoiding finite stuttering when simulating.
====