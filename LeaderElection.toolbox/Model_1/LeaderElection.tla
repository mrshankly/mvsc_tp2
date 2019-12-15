---------------------------- MODULE LeaderElection -----------------------------
(******************************************************************************)
(* Trabalho Prático 2 - MVSC 2019                                             *)
(*                                                                            *)
(* Realizado por:                                                             *)
(*     João Marques - 48500,                                                  *)
(*     Vicente Almeida - 47803                                                *)
(******************************************************************************)

EXTENDS FiniteSets, Integers, Naturals, Sequences

CONSTANT MAX_PROCESSES, ID

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
neighbour(p) == 1 + (p % MAX_PROCESSES)

(******************************************************************************)
(* Sets of all messages of type 1 and type 2.                                 *)
(******************************************************************************)
message1 == [type: {1}, number: Int, phase: Nat, counter: Nat]
message2 == [type: {2}, number: Int]

--------------------------------------------------------------------------------

VARIABLES
    phase,      \* The phase in which each process currently is.
    started,    \* Indicates whether an active process has sent the initial M1
                \* message or not.
    state,      \* State of a process, it can be active, waiting or passive.
    id,         \* The number originally stored by a process.
    max,        \* The accumulated maximum number stored by a process.

    (**************************************************************************)
    (* In the protocol, processes communicate with one another by sending     *)
    (* messages. We represent the message passing mechanism between processes *)
    (* with the variable queue.                                               *)
    (*                                                                        *)
    (* So, queue[p] represents the sequence of messages (preserves order)     *)
    (* that process p has received from its neighbour.                        *)
    (**************************************************************************)
    queue

vars == <<phase, started, state, id, max, queue>>

--------------------------------------------------------------------------------

TypeInvariant ==
    /\ phase \in [processes -> Nat]
    /\ started \in [processes -> BOOLEAN]
    /\ state \in [processes -> {"active", "waiting", "passive"}]
    /\ id \in [processes -> Int]
    /\ max \in [processes -> Int]
    /\ queue \in [processes -> Seq(message1 \union message2)]

--------------------------------------------------------------------------------

Init ==
    /\ phase = [p \in processes |-> 0]
    /\ started = [p \in processes |-> FALSE]
    /\ state = [p \in processes |-> "active"]
    /\ id = [p \in processes |-> ID[p]]
    /\ max = id
    /\ queue = [p \in processes |-> <<>>]

ActiveSendM1(p) ==
    /\ state[p] = "active" /\ started[p] = FALSE
    /\ started' = [started EXCEPT ![p] = TRUE]
    /\ LET msg == [
               type    |-> 1,
               number  |-> max[p],
               phase   |-> phase[p],
               counter |-> 2^(phase[p])
           ]
       IN queue' = [queue EXCEPT ![neighbour(p)] = Append(@, msg)]
    /\ UNCHANGED <<phase, state, id, max>>

ActiveReceiveM1(p) ==
    /\ state[p] = "active" /\ started[p] = TRUE
    /\ Len(queue[p]) > 0 /\ Head(queue[p]).type = 1
    /\ LET m1 == Head(queue[p])
       IN IF m1.number > max[p] THEN
              /\ max' = [max EXCEPT ![p] = m1.number]
              /\ state' = [state EXCEPT ![p] = "waiting"]
              /\ queue' = [queue EXCEPT ![p] = Tail(@)]
              /\ UNCHANGED <<phase, started, id>>
          ELSE
              /\ state' = [state EXCEPT ![p] = "passive"]
              /\ LET msg == [type |-> 2, number |-> max[p]]
                 IN queue' = [queue EXCEPT ![p] = Tail(@),
                                           ![neighbour(p)] = Append(@, msg)]
              /\ UNCHANGED <<phase, started, id, max>>

WaitingReceiveM1(p) ==
    /\ state[p] = "waiting"
    /\ Len(queue[p]) > 0 /\ Head(queue[p]).type = 1
    /\ state' = [state EXCEPT ![p] = "passive"]
    /\ UNCHANGED <<phase, started, id, max, queue>>

WaitingReceiveM2(p) ==
    /\ state[p] = "waiting"
    /\ Len(queue[p]) > 0 /\ Head(queue[p]).type = 2
    /\ LET m2 == Head(queue[p])
       IN /\ m2.number = max[p]
          /\ phase' = [phase EXCEPT ![p] = @ + 1]
          /\ state' = [state EXCEPT ![p] = "active"]
          /\ started' = [started EXCEPT ![p] = FALSE]
          /\ queue' = [queue EXCEPT ![p] = Tail(@)]
          /\ UNCHANGED <<id, max>>

PassiveReceiveM1(p) ==
    /\ state[p] = "passive"
    /\ Len(queue[p]) > 0 /\ Head(queue[p]).type = 1
    /\ LET m1 == Head(queue[p])
       IN IF m1.number >= max[p] /\ m1.counter >= 1 THEN
              /\ max' = [max EXCEPT ![p] = m1.number]
              /\ IF m1.counter > 1 THEN
                     /\ LET msg == [m1 EXCEPT !.counter = @ - 1]
                        IN queue' = [queue EXCEPT ![p] = Tail(@),
                                                  ![neighbour(p)] = Append(@, msg)]
                     /\ UNCHANGED <<phase, started, state, id>>
                 ELSE
                     /\ state' = [state EXCEPT ![p] = "waiting"]
                     /\ phase' = [phase EXCEPT ![p] = m1.phase]
                     /\ LET msg == [m1 EXCEPT !.counter = 0]
                        IN queue' = [queue EXCEPT ![p] = Tail(@),
                                                  ![neighbour(p)] = Append(@, msg)]
                     /\ UNCHANGED <<started, id>>
          ELSE
              /\ LET msg == [m1 EXCEPT !.counter = 0]
                 IN queue' = [queue EXCEPT ![p] = Tail(@),
                                           ![neighbour(p)] = Append(@, msg)]
              /\ UNCHANGED <<phase, started, id, max, state>>

PassiveReceiveM2(p) ==
    /\ state[p] = "passive"
    /\ Len(queue[p]) > 0 /\ Head(queue[p]).type = 2
    /\ LET m2 == Head(queue[p])
       IN IF m2.number < max[p] THEN
              /\ queue' = [queue EXCEPT ![p] = Tail(@)]
              /\ UNCHANGED <<phase, started, state, id, max>>
          ELSE
              /\ queue' = [queue EXCEPT ![p] = Tail(@),
                                        ![neighbour(p)] = Append(@, m2)]
              /\ UNCHANGED <<phase, started, state, id, max>>

Next ==
    \E p \in processes: \/ ActiveSendM1(p)
                        \/ ActiveReceiveM1(p)
                        \/ WaitingReceiveM1(p)
                        \/ WaitingReceiveM2(p)
                        \/ PassiveReceiveM1(p)
                        \/ PassiveReceiveM2(p)

--------------------------------------------------------------------------------

(******************************************************************************)
(* The algorithm should finish within a finite time once the leader is        *)
(* selected.                                                                  *)
(******************************************************************************)
Termination == [](TRUE)

(******************************************************************************)
(* There is exactly one process that considers itself as leader.              *)
(******************************************************************************)
Uniqueness ==
    <>[](\E l \in processes: /\ max[l] = id[l]
                             /\ \A p \in processes \ {l}: max[p] # id[p])

(******************************************************************************)
(* All processes know who the leader is.                                      *)
(******************************************************************************)
Agreement ==
    \A p1, p2 \in processes: <>[](max[p1] = max[p2])

--------------------------------------------------------------------------------

Fairness ==
    \A p \in processes: /\ WF_vars(ActiveSendM1(p))
                        /\ SF_vars(ActiveReceiveM1(p))
                        /\ SF_vars(WaitingReceiveM1(p))
                        /\ SF_vars(WaitingReceiveM2(p))
                        /\ SF_vars(PassiveReceiveM1(p))
                        /\ SF_vars(PassiveReceiveM2(p))

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness

================================================================================
