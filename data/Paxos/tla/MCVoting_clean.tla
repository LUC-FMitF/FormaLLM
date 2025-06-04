------------------------------ MODULE MCVoting ------------------------------
EXTENDS Voting, TLC

CONSTANTS a1, a2, a3
CONSTANTS v1, v2

MCAcceptor == {a1, a2, a3}
MCValue == {v1, v2}
MCQuorum == {{a1, a2}, {a1, a3}, {a2, a3}}
MCBallot == 0..1
MCSymmetry == Permutations(MCAcceptor) \cup Permutations(MCValue)

ConsensusSpecBar == C!Spec

ASSUME QuorumNonEmpty!:

MCInit == TypeOK

MCSpec == TypeOK /\ [][FALSE]_<<votes, maxBal>>
MCInv == /\ AllSafeAtZero!:
/\ ChoosableThm!:
/\ OneValuePerBallot => OneVote
/\ VotesSafeImpliesConsistency!:
/\ ShowsSafety!:

MCSpecI == Inv /\ [][Next]_<<votes, maxBal>>

=============================================================================
