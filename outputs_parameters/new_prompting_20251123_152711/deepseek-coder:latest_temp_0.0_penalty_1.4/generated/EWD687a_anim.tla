---- MODULE EWD687a_anim ----
(* TLC Configuration *)
CONSTANTS
    L = L
    P1 = P1
    P2 = P2
    P3 = P3
    P4 = P4
    P5 = P5
    NodesOfNetwork = {L, P1, P2, P3, P4, P5}
    Network = {
        L, P1, P2, P3, P4, P5 // No self-loops
    } IN TLCEval(RandomElement(Network))

SPECIFICATION
    Spec

INVARIANT
    TypeOK
    DT1Inv
    InterestingBehavior

PROPERTY
    DT2
    * CountersConsistent
    * TreeWithRoot
    * StableUpEdge

ALIAS
    Alias

CHECK_DEADLOCK
    FALSE

ACTION_CONSTRAINT
    NoSuperfluousIdleSteps

(* Defines an arrow with plain SVG that is referenced in the def of E below. *)
DEFINE REF Arrow <- <<"Arrow", [x: Nat, y: Nat]>>

(* Legend with four rows of labels (text) whose top-left point is located at BasePos: *)
LOCAL INSTANCE BasePos <- <<"BasePos", [x: Nat, y: Nat]>>
LOCAL INSTANCE Labels <- [
    "Current state ordinal",
    "Action from predecessor state to the current state",
    "Action from current state to the next/successor state",
    "~neutral procs red, round when also active"
]

/* A function from processes to x,y coordinates: [ Procs → [x: Nat, y: Nat] ] */
LOCAL INSTANCE Layout <- <<"Layout", [procs: Procs, options: {base_pos: BasePos, node_dim: Nat}>>

/* An SVG group containing rectangles denoting the graph of processes. Approximately at the center of each node, a text indicates the processes name (Procs). */
LOCAL INSTANCE ProcessesSvg <- <<"ProcessesSvg", [procs: Procs, node_dim: Nat]>>

/* A black square denotes an idle process, a red circle an active one. */
LOCAL INSTANCE ProcessesSvgIdle <- <<"ProcessesSvgIdle", [procs: Procs]>>

/* An SVG group containing lines denoting the (graph) edges. An line, connecting a from and to node, is annotated with three labels: */
LOCAL INSTANCE EdgesSvg <- <<"EdgesSvg", [edges: Set of edges, node_dim: Nat]>>

/* An upEdge is denoted by a dashed, orange line. */
LOCAL INSTANCE UpEdgesSvg <- <<"UpEdgesSvg", [edges: Set of edges, node_dim: Nat]>>

/* Combine the (SVG) definitions, legend, processes, edges, and upEdges into a single (SVG) frame as a visualization of the current TLA+ state. */
LOCAL INSTANCE VisualizationSvg <- <<"VisualizationSvg", [node_dim: Nat]>>

/* Writes the given string str to a file whose name contains the number n. */
LOCAL ACTION WriteToFile <- [str: String, n: Nat]

/* https://animator.tlapl.us (interactively explore the animation) */
LOCAL INSTANCE AnimatorSvg <- <<"AnimatorSvg", [node_dim: Nat]>>

/* The resulting set of EWD687a_anim_???.svg files can be rendered as an animated gif with: */
LOCAL ACTION ConvertToGif <- [file_pattern: String]
====