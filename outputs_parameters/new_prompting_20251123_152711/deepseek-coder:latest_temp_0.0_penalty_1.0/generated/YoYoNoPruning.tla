---- MODULE YoYoNoPruning ----
-- TLC Configuration:
CONSTANTS 
  Zero = 0
  One = 1
  Naturals = {Zero, ..., One}
  Succeed = 0
  False = 0
  True = 1
  EmptyGraph = <<>>
  SINK_EDGE = -1
  SOURCE_EDGE = 1
INVARIANT NodeKindIsInRange(Node)

-- Definitions:

ALIAS Edge = Int
ALIAS Neighborhood = Set Int
ALIAS Graph = Set (Edge, Neighborhood)
ALIAS Node = Int

-- Invariants:

INVARIANT_SINK(G, n) == FOR_ALL(m ∈ Naturals) ->
  (EXISTS(m' ∈ NEIGHBORHOODS(G, n)) -> m' ≠ n) ->
  (EXISTS(m ∈ NEIGHBORHOODS(G, m')) -> NodeKind(m) ≠ NodeKind(n))

INVARIANT_SOURCE(G, n) == FOR_ALL(m ∈ NATURALS) ->
  (EXISTS(m' ∈ NEIGHBORHOODS(G, n)) -> m' ≠ n) ->
  (EXISTS(m ∈ NEIGHBORHOODS(G, m')) -> NodeKind(m) = NodeKind(n))

INVARIANT_NODE(G, n) ==
  (EXISTS(m ∈ NEIGHBORHOODS(G, n)) -> NodeKind(n) ∈ {Source, Sink})

INVARIANT_EMPTY_GRAPH(G) ==
  (G ≠ EMPTY_GRAPH) ->
  (FOR_ALL(n ∈ NATURALS) ->
    (EXISTS(m ∈ NEIGHBORHOODS(G, n)) -> NodeKind(n) = Sink))

INVARIANT_LEADER(G, n) ==
  (FOR_ALL(m ∈ NEIGHBORHOODS(G, n)) -> NodeKind(n) = NodeKind(m))

INVARIANT_DOWN(G, n, p) ==
  (EXISTS(m ∈ NEIGHBORHOODS(G, n)) ->
    m ∈ NEIGHBORHOODS(G, m) ->
    (EXISTS(m' ∈ NEIGHBORHOODS(G, p)) ->
      m' ∈ NEIGHBORHOODS(G, m) ->
      m ≤ m'))

INVARIANT_UP(G, n, p) ==
  (EXISTS(m ∈ NEIGHBORHOODS(G, n)) ->
    m ∈ NEIGHBORHOODS(G, m) ->
    (EXISTS(m' ∈ NEIGHBORHOODS(G, p)) ->
      m' ∈ NEIGHBORHOODS(G, n) ->
      m ≥ m'))

-- Operations:

ALIAS AddEdge = (λ(G, e, n) => (e, n ∈ NEIGHBORHOODS(G, n)))

ALIAS RemoveEdge = (λ(G, e, n) => (e, n ∉ NEIGHBORHOODS(G, n)))

ALIAS Broadcast = (λ(G, n, v) => (n, v ∈ NEIGHBORHOODS(G, n)))

ALIAS Reply = (λ(G, n, v) => (n, v ∉ NEIGHBORHOODS(G, n)))

ALIAS IsLeader = (λ(G, n) => NodeKind(n) = NodeKind(m))

-- State Transitions:

INIT(G) ==
  (G = EMPTY_GRAPH)

ALIAS Down = (λ(G, n, p) =>
  n ∈ NEIGHBORHOODS(G, p) ->
  (EXISTS(m ∈ NEIGHBORHOODS(G, n)) ->
    (EXISTS(m' ∈ NEIGHBORHOODS(G, p)) -> m ≤ m') ->
    p, n ∈ NEIGHBORHOODS(G, p) ->
    NodeKind(n) = Sink))

ALIAS Up = (λ(G, n, p) =>
  n ∈ NEIGHBORHOODS(G, p) ->
  (EXISTS(m ∈ NEIGHBORHOODS(G, n)) ->
    (EXISTS(m' ∈ NEIGHBORHOODS(G, p)) -> m ≥ m') ->
    p, n ∈ NEIGHBORHOODS(G, p) ->
    NodeKind(n) ∈ {Source, Sink})

ALIAS Leader = (λ(G, n) => NodeKind(n) = NodeKind(m))

ALIAS Stabilize = (λ(G) =>
  (INVARIANT_LEADER(G, m)) ->
  (EXISTS(m ∈ NEIGHBORHOODS(G, m)) ->
    (EXISTS(m' ∈ NEIGHBORHOODS(G, m)) -> m ≠ m') ->
    LEADER(G, m))

ALIAS Termination = (λ(G) =>
  (EXISTS(n ∈ NEIGHBORHOODS(G, n)) ->
    NodeKind(n) ∈ {Source, Sink}) ->
  NODE(G, n))

-- Formulas:

ALIAS MinValue = (λ(G, n) => MIN(n ∈ NEIGHBORHOODS(G, n)))

ALIAS MinValueFromNeighbors = (λ(G, n) => MIN(n ∈ NEIGHBORHOODS(G, m)))

ALIAS SentDown = (λ(G, n, p) =>
  n ∈ NEIGHBORHOODS(G, p) ->
  (EXISTS(m ∈ NEIGHBORHOODS(G, n)) ->
    (EXISTS(m' ∈ NEIGHBORHOODS(G, p)) -> m ≤ m') ->
    p, n ∈ NEIGHBORHOODS(G, p) ->
    NodeKind(n) = Sink)

ALIAS SentUp = (λ(G, n, p) =>
  n ∈ NEIGHBORHOODS(G, p) ->
  (EXISTS(m ∈ NEIGHBORHOODS(G, n)) ->
    (EXISTS(m' ∈ NEIGHBORHOODS(G, p)) -> m ≥ m') ->
    p, n ∈ NEIGHBORHOODS(G, p) ->
    NodeKind(n) ∈ {Source, Sink})

-- Messages:

ALIAS Message = (λ(G, n, v) => (n, v ∈ NEIGHBORHOODS(G, n)))

-- Type correctness predicate:

ALIAS CorrectnessPredicate = (λ(G, n, v) => (n, v ∈ NEIGHBORHOODS(G, n)))
====