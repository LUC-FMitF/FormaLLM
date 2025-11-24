---- MODULE YoYoNoPruning ----


CONSTANTS
  Node == {0..}

TypeOK == \E n \in Node : Node = {n}

SPECIFICATION Spec

INVARIANTS
  Inv1 == \A n \in Node : n \in Source \IMPLIES n \in Node
  Inv2 == \A n \in Node : \E m \in Node : m \in Source \IMPLIES m < n

TLC Configuration:
CONSTANTS
  Source == {n \in Node : \E m \in Node : m \in Node[n] \AND m > n}
  Sink == {n \in Node : \A m \in Node : m \in Node[n] \IMPLIES m < n}
  Internal == Node \setminus (Source \cup Sink)
  Neighbor == \Union \{Node[n] : n \in Node\}
  Mailbox == Node \times {down, up}

SPECIFICATION
  Init == Node = {0} /\ Source = {0} /\ Sink = {} /\ Internal = {} /\ Mailbox = {}
  Trans ==
    (Node' = Node \union \{n+1\}, Source' = Source \union \{n+1\}, Sink' = Sink,
     Internal' = Internal, Mailbox' = Mailbox \union \{n+1, down\} /\
     (\A m \in Node[n] : m \in Source \IMPLIES (n, down) \in Mailbox)) /\
     (\A m \in Node[n] \setminus \{n\} : m \in Sink \IMPLIES (n, down) \in Mailbox)) /\
     (\A m \in Node : m \in Internal \IMPLIES (n, down) \in Mailbox)) /\
     (\A m \in Node[n] : m \in Source \IMPLIES (n, up) \in Mailbox)) /\
     (\A m \in Node[n] \setminus \{n\} : m \in Sink \IMPLIES (n, up) \in Mailbox)) /\
     (\A m \in Node : m \in Internal \IMPLIES (n, up) \in Mailbox))

====