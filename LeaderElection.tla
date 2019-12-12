---------------------------- MODULE LeaderElection -----------------------------
(******************************************************************************)
(* Trabalho Prático 2 - MVSC 2019                                             *)
(*                                                                            *)
(* Realizado por:                                                             *)
(*     João Marques - 48500                                                   *)
(*     Vicente Almeida - 47803                                                *)
(******************************************************************************)

EXTENDS Integers, Naturals, Sequences, TLC

CONSTANT MAX_PROCESSES

(******************************************************************************)
(* Set of processes, where each process is identified by an integer ranging   *)
(* from 1 to MAX_PROCESSES.                                                   *)
(******************************************************************************)
processes == 1..MAX_PROCESSES

(******************************************************************************)
(* Represents how the different processes are connected in a ring.            *)
(*                                                                            *)
(* The ring is simply a permutation of the processes set, with the additional *)
(* restriction that a node in the ring can not be connected to itself.        *)
(*                                                                            *)
(* In other words, neighbour[p] represents the process to the right of        *)
(* process p, which for obvious reasons, has to be different than p itself.   *)
(******************************************************************************)
neighbour == CHOOSE r \in Permutations(processes): \A p \in processes : r[p] # p

(******************************************************************************)
(* Sets of the messages of type M1 and M2. In the article, M1 is represented  *)
(* as the tuple <<1, i, phase, counter>>, while M2 is represented as          *)
(* <<2, i>>. Since we have a queue for each type of message, we dropped the   *)
(* first element, which identifies the type of message.                       *)
(******************************************************************************)
m1 == Int \X Nat \X Nat \* value, phase, counter
m2 == Int               \* value

--------------------------------------------------------------------------------

VARIABLES
    phase, \* The phase in which each process currently is.
    state, \* State of a process, it can be active, waiting or passive.
    id,    \* The number originally stored by a process.
    max,   \* The accumulated maximum number stored by a process.

    (**************************************************************************)
    (* In the protocol, processes communicate with one another by sending     *)
    (* messages. We represent the message passing mechanism between processes *)
    (* with the variables m1_queue and m2_queue, for messages of type M1 and  *)
    (* M2 respectively. So, mX_queue[p] represents the sequence of messages   *)
    (* of type X received by process p.                                       *)
    (**************************************************************************)
    m1_queue,
    m2_queue

vars == <<phase, state, id, max, m1_queue, m2_queue>>

--------------------------------------------------------------------------------

TypeInvariant == /\ phase \in [processes -> Nat]
                 /\ state \in [processes -> {"active", "waiting", "passive"}]
                 /\ id \in [processes -> Int]
                 /\ max \in [processes -> Int]
                 /\ m1_queue \in [processes -> Seq(m1)]
                 /\ m2_queue \in [processes -> Seq(m2)]

--------------------------------------------------------------------------------

Init == /\ phase = [p \in processes |-> 0]
        /\ state = [p \in processes |-> "active"]
        /\ id = [p \in processes |-> p] \* TODO pick a random int instead of p
        /\ max = id
        /\ m1_queue = [p \in processes |-> << >>]
        /\ m2_queue = [p \in processes |-> << >>]

Next == UNCHANGED vars

--------------------------------------------------------------------------------

Spec == /\ Init
        /\ [][Next]_vars

================================================================================
