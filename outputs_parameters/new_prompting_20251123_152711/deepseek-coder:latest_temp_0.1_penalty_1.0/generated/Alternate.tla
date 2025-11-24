---- MODULE Alternate --------

(***************************************************************************)
(* This specifies a system that alternately performs two actions, which     *)
(* for now I will call A_0 and A_1.  It uses a variable v whose value       *)
(* alternates between 0 and 1, performing an A_0 action when v changes      *)
(* from 0 to 1, and an A_1 action when v changes from 1 to 0.               *)
(* We let the variable x to represent the part of the state that is         *)
(* changed by the A_0 and A_1 actions.  We introduce two constant           *)
(* operators XInit and XAct, where XInit(x) is assumed to assert that x     *)
(* has a correct initial value, and XAct(i, xInit, xNext) is assumed to     *)
(* assert that changing the value of x from xInit to xNext represent an     *)
(* A_i action, for i=0, 1.                                                  *)
(***************************************************************************)

CONSTANTS
  XInit(x)  --  Assert that x has a correct initial value
  XAct(i, xInit, xNext)  --  Assert that changing the value of x from xInit to xNext represent an A_i action, for i=0, 1.

SPECIFICATION Spec

INVARIANTS
  XInit(x)  --  Spec
  XAct(i, xInit, xNext)  --  Spec

LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Naturals
LOCAL INSTANCE Actions

\* The empty state
EmptyState  --  []

\* The set of valid indices for state s
StateIndices(s)  --  {0..(n-1)}

\* The set of all states of elements in S with length n
StateOfLength(S, n)  --  {s ∈ ZSeqOfLength(S, n) : n ∈ Nat}

\* The set of all states of S
State(S)  --  UNION {StateOfLength(S, n) : n ∈ Nat}

\* The variable x in the state
X(s)  --  s[1]

\* The state s after performing an A_0 action
A_0Action(s)  --  [i ∈ StateIndices(s) |-> s[i-1]]

\* The state s after performing an A_1 action
A_1Action(s)  --  [i ∈ StateIndices(s) |-> s[i+1]]

\* The set of all actions
Actions  --  {A_0Action, A_1Action}

\* The next state after performing an action
NextState(s, a)  --  {i ∈ StateIndices(s) |-> A_iAction(s)[i]}

\* The set of all next states
NextStates(s)  --  {n ∈ Nat |-> NextState(s, a) : a ∈ Actions}

\* The initial state
InitState  --  {X(s) |-> s[0]}

\* The set of all initial states
InitStates  --  {InitState : s ∈ State}

\* The set of all states
AllStates  --  {InitStates ∪ NextStates(s) : s ∈ State}

\* The set of all actions
AllActions  --  {A_0Action, A_1Action}

\* The set of all next actions
NextActions  --  {A_iAction : i ∈ Nat}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNextActions  --  {NextActions ∪ PossibleActions}

\* The set of all possible states
PossibleStates  --  {AllStates ∪ PossibleActions}

\* The set of all possible actions
PossibleActions  --  {AllActions ∪ NextActions}

\* The set of all possible next actions
NextNext
====