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
neighbour == CHOOSE r \in Permutations(processes): \A p \in processes: r[p] # p

(******************************************************************************)
(* Set of all messages. There are two types of messages, M1 and M2. M1        *)
(* messages use all the defined fields, type, number, phase and counter.      *)
(* M2 messages use only the first two fields, type and number.                *)
(******************************************************************************)
messages == [type: {1, 2}, number: Int, phase: Nat, counter: Nat]

--------------------------------------------------------------------------------

VARIABLES
    phase, \* The phase in which each process currently is.
    state, \* State of a process, it can be active, waiting or passive.
    id,    \* The number originally stored by a process.
    max,   \* The accumulated maximum number stored by a process.

    (**************************************************************************)
    (* In the protocol, processes communicate with one another by sending     *)
    (* messages. We represent the message passing mechanism between processes *)
    (* with the variable queue.                                               *)
    (*                                                                        *)
    (* So, queue[p] represents the sequence of messages (preserves order)     *)
    (* that process p has received from its neighbour.                        *)
    (**************************************************************************)
    queue

vars == <<phase, state, id, max, queue>>

--------------------------------------------------------------------------------

TypeInvariant ==
    /\ phase \in [processes -> Nat]
    /\ state \in [processes -> {"active", "waiting", "passive"}]
    /\ id \in [processes -> Int]
    /\ max \in [processes -> Int]
    /\ queue \in [processes -> Seq(messages)]

--------------------------------------------------------------------------------

Init ==
    /\ phase = [p \in processes |-> 0]
    /\ state = [p \in processes |-> "active"]
    /\ id = [p \in processes |-> p] \* TODO pick a random int instead of p
    /\ max = id
    /\ queue = [p \in processes |-> << >>]
        
ActiveSendM1(p) ==
    /\ state[p] = "active"
    /\ LET msg == [
               type    |-> 1,
               number  |-> max[p],
               phase   |-> phase[p],
               counter |-> 2^(phase[p])
           ]
       IN queue' = [queue EXCEPT ![neighbour[p]] = Append(@, msg)]
    /\ UNCHANGED <<phase, state, id, max>>

ActiveReceiveM1(p) ==
    /\ state[p] = "active"
    /\ Len(queue[p]) > 0 /\ Head(queue[p]).type = 1
    /\ LET m1 == Head(queue[p])
       IN IF m1.number > max[p] THEN
              /\ max' = [max EXCEPT ![p] = m1.number]
              /\ state' = [state EXCEPT ![p] = "waiting"]
              /\ queue' = [queue EXCEPT ![p] = Tail(@)]
              /\ UNCHANGED <<phase, id, queue>>
          ELSE
              /\ state' = [state EXCEPT ![p] = "passive"]
              /\ LET m2 == [type |-> 2, number |-> max[p]]
                 IN queue' = [queue EXCEPT ![p] = Tail(@), ![neighbour[p]] = Append(@, m2)]
              /\ UNCHANGED <<phase, id, max>>

Next ==
    \/ \E p \in processes: ActiveSendM1(p)
    \/ \E p \in processes: ActiveReceiveM1(p)

--------------------------------------------------------------------------------

Fairness ==
    /\ \A p \in processes: WF_vars(ActiveSendM1(p))
    /\ \A p \in processes: SF_vars(ActiveReceiveM1(p))

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness

================================================================================
