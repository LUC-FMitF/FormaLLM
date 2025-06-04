---------------------------- MODULE Age_Channel ----------------------------

EXTENDS Integers, TLC

CONSTANT Messages,
Boxes

VARIABLES inTransit,
inDelivery

Pack_WaitingTime(msgs) == { [ content |-> m, age |-> 0 ] : m \in msgs }

Unpack(boxes) == { m.content : m \in boxes }

Init ==
/\ inTransit = {}
/\ inDelivery = {}

Pickup(msgs) ==
/\ inTransit' = inTransit \cup Pack_WaitingTime(msgs)
/\ inDelivery' = {}

Deliver(rcver) ==
\E boxes \in SUBSET inTransit :
/\ \A box \in boxes : box.content.to = rcver
/\ inDelivery' = Unpack(boxes)
/\ inTransit' = inTransit \ boxes

AttainAge ==
/\ inTransit' = { [ content |-> package.content, age |-> package.age + 1 ]  :
package \in inTransit }
/\ inDelivery' = {}

TypeOK ==
/\ inTransit \subseteq Boxes
/\ inDelivery \subseteq Messages

=============================================================================
