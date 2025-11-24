---- MODULE YoYoNoPruning ----
EXTENDS ModuleTemplate

CONSTANTS
    Source, Sink, Internal

ASSIGNABLE
    Next, Prev, Phase, Mailbox, Outgoing, Incoming, Neighbors

VARIABLES
    Node, Message, Value

(* Nodes are represented by their integer identities *)
TypeOK == Node IN Naturals

(* The phase each node is currently executing *)
Phase IN {Source, Sink, Internal}

(* Incoming and outgoing neighbors of each node *)
Outgoing, Incoming SUBSET Naturals
Neighbors == Outgoing UNION Incoming

(* Mailbox of each node *)
Mailbox == [Node -> Value]

(* Messages sent during the algorithm *)
Message == [Node -> Value]

(* The kind of the node *)
IsSource == Node IN {n : Nat | [n] -> Source IN Phase}
IsSink == Node IN {n : Nat | [n] -> Sink IN Phase}
IsInternal == Node IN {n : Nat | [n] -> Internal IN Phase}

(* Down phase *)
IsDown == Node IN {n : Nat | [n] -> Source IN Phase OR Sink IN Phase}
IsNotDown == Node IN {n : Nat | [n] -> NOT (Source IN Phase OR Sink IN Phase)}

(* Up phase *)
IsUp == Node IN {n : Nat | [n] -> Sink IN Phase OR Internal IN Phase}
IsNotUp == Node IN {n : Nat | [n] -> NOT (Sink IN Phase OR Internal IN Phase)}

(* The type correctness predicate *)
TypeOK == EVERY Node \in Naturals /\
            Phase[Node] \in {Source, Sink, Internal} /\
            Outgoing[Node] \in Naturals /\
            Incoming[Node] \in Naturals /\
            Mailbox[Node] \in Naturals /\
            EVERY m \in Neighbors[Node] : Mailbox[m] \in Naturals

(* Yo-Yo algorithm as a state machine *)
Init == TypeOK /\ IsDown[Node] /\ EVERY m \in Neighbors[Node] : Mailbox[m] = UNDEFINED
Trans == [Node -> Value] /\ EVERY m \in Neighbors[Node] : Mailbox[m] = MIN {Value[m], Mailbox[m]}

(* Predicate asserting that there will always be at least two source nodes *)
AtLeastTwoSources == EXISTS {n : Nat | [n] -> Source IN Phase}

====
CONSTANTS
    Source = {[Source -> Source]}
    Sink = {[Sink -> Sink]}
    Internal = {[Internal -> Internal]}
====