---- MODULE Alternate ----
(***********************************************************************++)
(* This specifies a system that alternately performs two actions, which  *)
* for now I will call A_0 and A_1.                                *       )
*( It uses a variable v whose value              *)
alternates between 0 and 1, performing an A_0 action when v changes from   *)
*)
v == [i \in Nat |-> i % 2 = 0] /\ (A_0(x) => XAct[0](XInit x))                        )
*( to assert that changing the value of    *       )
* x represents an A_1 action, and vice versa.     *)   /*******************************)
\EE v : Spec \/ [][Next]_<<v>>  (Specification with variable hidden)      |                        |||                **)))))***))))))))))))))))))))))))))))))))* * ***    )
====