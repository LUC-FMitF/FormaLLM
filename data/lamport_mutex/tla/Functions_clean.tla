------------------------------ MODULE Functions -----------------------------

Restrict(f,S) == [ x \in S |-> f[x] ]

Range(f) == { f[x] : x \in DOMAIN f }

Inverse(f,S,T) == [t \in T |-> CHOOSE s \in S : t \in Range(f) => f[s] = t]

Injection(S,T) == { M \in [S -> T] : \A a,b \in S : M[a] = M[b] => a = b }

Surjection(S,T) == { M \in [S -> T] : \A t \in T : \E s \in S : M[s] = t }

Bijection(S,T) == Injection(S,T) \cap Surjection(S,T)

ExistsInjection(S,T)  == Injection(S,T) # {}
ExistsSurjection(S,T) == Surjection(S,T) # {}
ExistsBijection(S,T)  == Bijection(S,T) # {}

=============================================================================
