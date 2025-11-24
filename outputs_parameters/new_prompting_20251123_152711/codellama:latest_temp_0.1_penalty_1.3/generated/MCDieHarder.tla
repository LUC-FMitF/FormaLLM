---- MODULE MCDieHarder ----

(**************************************************************************)
(* The following definitions duplicate the original Die Hard problem.     *)
(**************************************************************************)
CONSTANTS Goal = 4   \* The goal of the game is to get four beads in a row.*
                    \* on top of one another, either horizontally or      *
                    \* vertically.                                         *)
VARIABLES Jug     \* A jug has an infinite capacity and can hold any     *
                \* number of balls at once.  The game is played with two   *
                \* jugs, one red (R) and the other blue (B).               *)
          Capacity                    \* Each ball in a jug weighs         *
            <- [jug |-> INTEGER]      \* exactly half as much as its     *
              / 2 ]                   \* partner. For example, if one of  *
                R or B has three balls, the other must have six.          *)
INVARIANT TypeOK NotSolved
====