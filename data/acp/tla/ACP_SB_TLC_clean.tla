------------------------------ MODULE ACP_SB_TLC -------------------------------

EXTENDS ACP_SB, TLC

Perms == Permutations(participants)

--------------------------------------------------------------------------------

AC4_alt == [][ /\ (\A i \in participants : participant[i].decision = commit
=> (participant'[i].decision = commit))
/\ (\A j \in participants : participant[j].decision = abort
=> (participant'[j].decision = abort))]_<<participant>>

================================================================================
