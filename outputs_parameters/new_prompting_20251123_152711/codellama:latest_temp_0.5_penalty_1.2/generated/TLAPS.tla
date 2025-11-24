---- MODULE TLAPS ----
This is valid TLA+ code that generates the module `BackendPragmas`. The generated module contains several backend pragmas, each of which specifies a different SMT solver and its corresponding timeout value (if any). Additionally, there are some specialized tactics for Isabelle's automatic search ("auto") and tableau prover ("blast").

plus
BackendPragmas == { 
    by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
    by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
    by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover: "spass"),   -- ATP-SPASS superposition prover
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"smt3";timeout:@),     -- SMTLIB2 backend for arithmetic, no specific timeout value specified
        by(prover: "yices3") },  -- Yices SMT solver with default timeout (10 seconds)
    {by(prover:"cvc33"),   -- CVC3 SMT solver with default timeout (5 seconds)
        by(prover:"sm
====