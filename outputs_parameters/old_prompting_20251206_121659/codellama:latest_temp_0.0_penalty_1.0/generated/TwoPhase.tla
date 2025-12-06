---- MODULE TwoPhase ----

(**************************************************************************)
(* The two-phase handshake, which is a simple but very important hardware  *)
(* protocol by which a Producer process and a Consumer process alternately  *)
(* perform actions, with the Producer going first.  The system is pictured  *)
(* as follows:                                                             *)
(**************************************************************************)

CONSTANTS
  Producer, Consumer, RM
VARIABLES
  ProducerState, ConsumerState, RMState

\* The Producer's state
ProducerState ==
  IF Producer = Consumer
  THEN ConsumerState
  ELSE RMState

\* The Consumer's state
ConsumerState ==
  IF Producer = Consumer
  THEN ProducerState
  ELSE RMState

\* The RM's state
RMState ==
  IF Producer = Consumer
  THEN RMState
  ELSE RMState

\* The Producer's action
ProducerAction ==
  IF Producer = Consumer
  THEN ConsumerAction
  ELSE RMAction

\* The Consumer's action
ConsumerAction ==
  IF Producer = Consumer
  THEN ProducerAction
  ELSE RMAction

\* The RM's action
RMAction ==
  IF Producer = Consumer
  THEN RMAction
  ELSE RMAction

\* The Producer's next state
ProducerNext ==
  IF Producer = Consumer
  THEN ConsumerNext
  ELSE RMNext

\* The Consumer's next state
ConsumerNext ==
  IF Producer = Consumer
  THEN ProducerNext
  ELSE RMNext

\* The RM's next state
RMNext ==
  IF Producer = Consumer
  THEN RMNext
  ELSE RMNext

\* The Producer's postcondition
ProducerPost ==
  IF Producer = Consumer
  THEN ConsumerPost
  ELSE RMPost

\* The Consumer's postcondition
ConsumerPost ==
  IF Producer = Consumer
  THEN ProducerPost
  ELSE RMPost

\* The RM's postcondition
RMPost ==
  IF Producer = Consumer
  THEN RMPost
  ELSE RMPost

\* The Producer's invariant
ProducerInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Consumer's invariant
ConsumerInv ==
  IF Producer = Consumer
  THEN ProducerInv
  ELSE RMInv

\* The RM's invariant
RMInv ==
  IF Producer = Consumer
  THEN RMInv
  ELSE RMInv

\* The Producer's specification
ProducerSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Consumer's specification
ConsumerSpec ==
  IF Producer = Consumer
  THEN ProducerSpec
  ELSE RMSpec

\* The RM's specification
RMSpec ==
  IF Producer = Consumer
  THEN RMSpec
  ELSE RMSpec

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN ConsumerInv
  ELSE RMInv

\* The Producer's specification
TPSpec ==
  IF Producer = Consumer
  THEN ConsumerSpec
  ELSE RMSpec

\* The Producer's invariant
TPInv ==
  IF Producer = Consumer
  THEN Cons
====