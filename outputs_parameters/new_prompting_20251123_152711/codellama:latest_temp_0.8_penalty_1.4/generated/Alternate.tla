---- MODULE Alternate ----

(*************************************************************************)
(* Generated at Sat Oct 31 02:58:46 PDT 2009                             *)
(**************************************************************************)
CONSTANTS   XInit,     \* The set of all parts whose initial values are correct.
            XAct       \* The set of all actions performed by the alternator system.
VARIABLES   v,         \* A variable representing whether we are in state 0 or state 1 (or equivalently which action to perform next).
            x          \* An arbitrary part whose value is changed each round.

(**************************************************************************)
\EE v : Spec                                                             *)
*)
v == XInit /\ [][Next]_<<x>>       (* All states are initial states and x has the correct initial value  *)
         \/            (* The specification for state 0: change v to 1, perform A_0 on x, then go back to state 1  * /)
          (v = 0 /\ XAct(0, <<x>>, <<v=1; x <- XInit[<<x>>] +XAct(0, <<x>>, <<v=1; x<- NoVal >>) >>) \/ v = 1 /\ [][Next]_< > )
         (* The specification for state 1: change v to 0 and perform A_1 on x. Then go back to the initial state *)
          (v = 1 /\ XAct(1, <<x>>, <<v=0; x <- XInit[<<x>>] +XAct(1, <<x>>, <<v=0; x<- NoVal >>) >>) \/ v = 2 /\ [][Next]_< )
         (* Any other state is an error *)
          (OTHER <> (<>))                               (** TLC Configuration: **)
CONSTANTS   XInit,     * The set of all parts whose initial values are correct.
            XAct       * The set of all actions performed by the alternator system.
VARIABLES   v,         * A variable representing whether we are in state 0 or state 1 (or equivalently which action to perform next).
            x          * An arbitrary part whose value is changed each round.* /)
====