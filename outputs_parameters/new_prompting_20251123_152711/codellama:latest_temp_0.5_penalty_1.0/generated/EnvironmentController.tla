---- MODULE EnvironmentController ----
CONSTANTS N T d0 SendPoint PredictPoint DELTA PHI
TYPE_INVARIANT TypeOK
PROPERTY StrongCompleteness (Eventually)
  ASSERT TRUE : "Strong Completeness"
SPECIFICATION Spec
====