---- MODULE TLAPS ----
(*
 * Backend pragmas. 
 *)
MODULE BackendPragmas
    VARIABLES
        -- Backend prover names
        cvc3, smt3, yices3, verit, z33, zenon, isabelle :: STRING
    CONSTANTS
        -- Backend prover names
        cvc33, spass :: STRING
    -- Default values
    cvc3   /:= cvc33
    smt3   /:= spass
    yices3 /:= "yices3"
    verit  /:= "verit"
    z33    /:= "z33"
    zenon  /:= "zenon"
    isabelle /:= "isabelle"
END BackendPragmas

(*
 * Backend pragma: SMT solver
 *)
MODULE SMTSolver
    VARIABLES
        -- Default timeout for SMT solver
        defaultTimeout :: NATURAL
    CONSTANTS
        -- SMT solver names
        smt3, cvc33, yices3, verit, z33 :: STRING
    -- Default values
    defaultTimeout /:= 120 -- seconds
END SMTSolver

(*
 * Backend pragma: Zenon
 *)
MODULE Zenon
    VARIABLES
        -- Default timeout for Zenon
        defaultTimeout :: NATURAL
    CONSTANTS
        -- Zenon name
        zenon :: STRING
    -- Default values
    defaultTimeout /:= 120 -- seconds
END Zenon

(*
 * Backend pragma: Isabelle
 *)
MODULE Isabelle
    VARIABLES
        -- Default timeout for Isabelle
        defaultTimeout :: NATURAL
        -- Default tactic for Isabelle
        defaultTactic :: STRING
    CONSTANTS
        -- Isabelle name
        isabelle :: STRING
    -- Default values
    defaultTimeout /:= 120 -- seconds
    defaultTactic /:= "auto"
END Isabelle

(*
 * Backend pragmas: multi-back-ends
 *)
MODULE MultiBackends
    CONSTANTS
        -- Backend prover names
        cvc3, smt3, yices3, verit, z33, zenon, isabelle :: STRING
    -- Backend prover order
    BACKEND_PROVER_ORDER /:= [cvc3, smt3, yices3, verit, z33, zenon, isabelle]
END MultiBackends

(*
 * Temporal logic
 *)
MODULE TemporalLogic
    (*
     * The rules WF2 and SF2 in "The Temporal Logic of Actions" are obtained
     * from the following two rules by the following substitutions: `.
     *)
    RULE WF2 == <<M>>_<g> [ENABLED <<M>>_g]
    RULE SF2 == <g>[ENABLED <<M>>_g]
END TemporalLogic
====