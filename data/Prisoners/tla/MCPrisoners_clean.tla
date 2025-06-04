----------------------------- MODULE MCPrisoners ----------------------------

EXTENDS Prisoners

InductiveInvariant == TypeOK /\ CountInvariant

InvTestSpec == InductiveInvariant /\ [][Next]_vars

=============================================================================
