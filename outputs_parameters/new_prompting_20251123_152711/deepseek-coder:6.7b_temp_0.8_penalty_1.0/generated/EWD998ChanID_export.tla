---- MODULE EWD998ChanID_export ----
CONSTANTS Node = {n1, n2, ...}  // Define your node set here
VARIABLES Clock[Node]            // Initialize a vector clock for each node
Init == \A n \in Node : Clock[n] = 0   // All clocks are initialized to zero at the start of simulation.
====