--------------------------- MODULE LeaderElection ---------------------------
(***************************************************************************)
(* Trabalho Prático 2 - MVSC 2019                                          *)
(*                                                                         *)
(* Realizado por:                                                          *)
(*     João Marques - 48500                                                *)
(*     Vicente Almeida - 47803                                             *)
(***************************************************************************)

EXTENDS Integers, Naturals

CONSTANT PROCESSES

VARIABLES phase, state, max, left

vars == <<phase, state, max>>

-----------------------------------------------------------------------------

TypeInvariant == /\ phase \in [PROCESSES -> Nat]
                 /\ state \in [PROCESSES -> {"active", "waiting", "passive"}]
                 /\ max \in [PROCESSES -> Int]
                 /\ left \in [PROCESSES -> PROCESSES]

-----------------------------------------------------------------------------

Init == /\ phase = [p \in PROCESSES |-> 0]
        /\ state = [p \in PROCESSES |-> "active"]
        /\ max = [p \in PROCESSES |-> CHOOSE v \in Int : TRUE]
        /\ left = [p \in PROCESSES |-> IF p + 1 \in PROCESSES THEN p + 1 ELSE 0]

Next == TRUE

-----------------------------------------------------------------------------

Spec == /\ Init
        /\ [][Next]_vars

=============================================================================
