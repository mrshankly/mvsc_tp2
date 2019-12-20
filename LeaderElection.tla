---------------------------- MODULE LeaderElection -----------------------------
(******************************************************************************)
(* Trabalho Prático 2 - MVSC 2019                                            *)
(*                                                                            *)
(* Realizado por:                                                             *)
(*     João Marques - 48500,                                                 *)
(*     Vicente Almeida - 47803                                                *)
(******************************************************************************)

EXTENDS FiniteSets, Integers, Naturals, Sequences

CONSTANT MAX_PROCESSES, ID

(******************************************************************************)
(* Set of processes, where each process is identified by an integer ranging   *)
(* from 1 to MAX_PROCESSES.                                                   *)
(******************************************************************************)
processes == 1..MAX_PROCESSES

ASSUME
    MAX_PROCESSES > 1

ASSUME
    ID \in Seq(Int) /\ Len(ID) = MAX_PROCESSES

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
                \* message to its neighbour.
    state,      \* State of a process, it can be active, waiting or passive.
    id,         \* The number originally stored by a process.
    max,        \* The accumulated maximum number stored by a process.
    terminated, \* Flag indicating if the algorithm has terminated or not.

    (**************************************************************************)
    (* In the protocol, processes communicate with one another by sending     *)
    (* messages. We represent the message passing mechanism between processes *)
    (* with the variable queue.                                               *)
    (*                                                                        *)
    (* So, queue[p] represents the sequence of messages (preserves order)     *)
    (* that process p has received from its neighbour.                        *)
    (**************************************************************************)
    queue

vars == <<phase, started, state, id, max, queue, terminated>>

--------------------------------------------------------------------------------

TypeInvariant ==
    /\ phase \in [processes -> Nat]
    /\ started \in [processes -> BOOLEAN]
    /\ state \in [processes -> {"active", "waiting", "passive"}]
    /\ id \in [processes -> Int]
    /\ max \in [processes -> Int]
    /\ queue \in [processes -> Seq(message1 \union message2)]
    /\ terminated \in BOOLEAN

--------------------------------------------------------------------------------

Init ==
    /\ phase = [p \in processes |-> 0]
    /\ started = [p \in processes |-> FALSE]
    /\ state = [p \in processes |-> "active"]
    /\ id = [p \in processes |-> ID[p]]
    /\ max = id
    /\ queue = [p \in processes |-> <<>>]
    /\ terminated = FALSE

(***************************************************************************)
(* The process "p" sends an M1 type message to it's neighbour.             *)
(* - Only active processes can perform this action.                        *)
(* - Only one M1 message should be sent by the process, per phase.         *)
(***************************************************************************)
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
    /\ UNCHANGED <<phase, state, id, max, terminated>>

(***************************************************************************)
(* The active process "p" receives a M1 type message "m1".                 *)
(* - If the number "n" contained within m1 is equal to p's id, then all    *)
(* processes have agreed that p is the leader and the algorithm should     *)
(* terminate.                                                              *)
(* - If that n is larger than p's current maximum number then n shall      *)
(* become p's new maximum number. After receiving this message p is now    *)
(* waiting for another message.                                            *)
(* - If n is smaller than p's maximum number then p will send an M2 type   *)
(* message to it's neighbor, transmiting p's maximum number. After doing   *)
(* so, p becomes passive.                                                  *)
(***************************************************************************)
ActiveReceiveM1(p) ==
    /\ state[p] = "active" /\ started[p] = TRUE
    /\ Len(queue[p]) > 0 /\ Head(queue[p]).type = 1
    /\ LET m1 == Head(queue[p])
       IN IF m1.number = id[p] THEN
              /\ terminated' = TRUE
              /\ UNCHANGED <<phase, started, state, id, max, queue>>
          ELSE IF m1.number > max[p] THEN
              /\ max' = [max EXCEPT ![p] = m1.number]
              /\ state' = [state EXCEPT ![p] = "waiting"]
              /\ queue' = [queue EXCEPT ![p] = Tail(@)]
              /\ UNCHANGED <<phase, started, id, terminated>>
          ELSE
              /\ state' = [state EXCEPT ![p] = "passive"]
              /\ LET msg == [type |-> 2, number |-> max[p]]
                 IN queue' = [queue EXCEPT ![p] = Tail(@),
                                           ![neighbour(p)] = Append(@, msg)]
              /\ UNCHANGED <<phase, started, id, max, terminated>>



(***************************************************************************)
(* The waiting process "p" receives an M1 type message, becoming passive.  *)
(***************************************************************************)
WaitingReceiveM1(p) ==
    /\ state[p] = "waiting"
    /\ Len(queue[p]) > 0 /\ Head(queue[p]).type = 1
    /\ state' = [state EXCEPT ![p] = "passive"]
    /\ UNCHANGED <<phase, started, id, max, queue, terminated>>

(***************************************************************************)
(* The waiting process "p" receives an M2 type message. This signals the   *)
(* begginging of a new phase for p, so it becomes active once again.       *)
(***************************************************************************)
WaitingReceiveM2(p) ==
    /\ state[p] = "waiting"
    /\ Len(queue[p]) > 0 /\ Head(queue[p]).type = 2
    /\ LET m2 == Head(queue[p])
       IN /\ m2.number = max[p]
          /\ phase' = [phase EXCEPT ![p] = @ + 1]
          /\ state' = [state EXCEPT ![p] = "active"]
          /\ started' = [started EXCEPT ![p] = FALSE]
          /\ queue' = [queue EXCEPT ![p] = Tail(@)]
          /\ UNCHANGED <<id, max, terminated>>

(***************************************************************************)
(* The passive process "p" receives an M1 type message "m".                *)
(* - If m's number is higher or equal to p's maximum and m's counter is    *)
(* higher than 1, then p simply forwards m to it's neighbor, decrementing  *)
(* m's counter                                                             *)
(* - If m's number is higher or equal to p's maximum and m's counter is    *)
(* lower or equal to one, then p stops being passive and starts waiting    *)
(* for a message to become active or passive again. p's phase jumps to the *)
(* one contained within m and p forwards the m to it's neighbor, with      *)
(* counter at 0                                                            *)
(* - If non of the previous conditions are met, p forwards the m to it's   *)
(* neighbor, with counter at 0                                             *)
(***************************************************************************)
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
                     /\ UNCHANGED <<phase, started, state, id, terminated>>
                 ELSE
                     /\ state' = [state EXCEPT ![p] = "waiting"]
                     /\ phase' = [phase EXCEPT ![p] = m1.phase]
                     /\ LET msg == [m1 EXCEPT !.counter = 0]
                        IN queue' = [queue EXCEPT ![p] = Tail(@),
                                                  ![neighbour(p)] = Append(@, msg)]
                     /\ UNCHANGED <<started, id, terminated>>
          ELSE
              /\ LET msg == [m1 EXCEPT !.counter = 0]
                 IN queue' = [queue EXCEPT ![p] = Tail(@),
                                           ![neighbour(p)] = Append(@, msg)]
              /\ UNCHANGED <<phase, started, id, max, state, terminated>>

(***************************************************************************)
(* The passive process "p" receives a M2 type message "m".                 *)
(* - If m's number is lower than p's maximum, then the message is ignored  *)
(* - If m's number is higher than p's maximum, then p forwards the message *)
(* to it's neighbor                                                        *)
(***************************************************************************)
PassiveReceiveM2(p) ==
    /\ state[p] = "passive"
    /\ Len(queue[p]) > 0 /\ Head(queue[p]).type = 2
    /\ LET m2 == Head(queue[p])
       IN IF m2.number < max[p] THEN
              /\ queue' = [queue EXCEPT ![p] = Tail(@)]
              /\ UNCHANGED <<phase, started, state, id, max, terminated>>
          ELSE
              /\ queue' = [queue EXCEPT ![p] = Tail(@),
                                        ![neighbour(p)] = Append(@, m2)]
              /\ UNCHANGED <<phase, started, state, id, max, terminated>>

--------------------------------------------------------------------------------

(******************************************************************************)
(* Looses a message from queue q.                                             *)
(******************************************************************************)
Lose(p) ==
    LET
        q == queue[p]
    IN
        /\ q # <<>>
        /\ \E i \in 1..Len(q) : \* removes the ith message from queue[p] 
               queue' = [queue EXCEPT ![p] = 
                   [j \in 1..(Len(q)-1) |-> IF j < i THEN q[j] ELSE q[j+1]]
               ]
        /\ UNCHANGED<<phase, started, state, id, max, terminated>>

--------------------------------------------------------------------------------

Next ==
    /\ terminated = FALSE
    /\ \E p \in processes: \/ ActiveSendM1(p)
                           \/ ActiveReceiveM1(p)
                           \/ WaitingReceiveM1(p)
                           \/ WaitingReceiveM2(p)
                           \/ PassiveReceiveM1(p)
                           \/ PassiveReceiveM2(p)
                           
NextLoseMsg ==
    /\ terminated = FALSE
    /\ \E p \in processes: \/ ActiveSendM1(p)
                           \/ ActiveReceiveM1(p)
                           \/ WaitingReceiveM1(p)
                           \/ WaitingReceiveM2(p)
                           \/ PassiveReceiveM1(p)
                           \/ PassiveReceiveM2(p)
                           \/ Lose(p)

--------------------------------------------------------------------------------

(******************************************************************************)
(* The algorithm should finish within a finite time once the leader is        *)
(* selected.                                                                  *)
(******************************************************************************)
Termination == <>[](terminated = TRUE)

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


(***************************************************************************)
(* We tested this specifications under the following conditions:           *)
(*     Behaviour Spec: Temporal formula - Spec                             *)
(*     Constant Values: MAX_PROCESSES <- 3, ID <- <<-1, 10, 4>>            *)
(*     Invariants: TypeInvariant                                           *)
(*     Properties: Agreement, Uniqueness, Termination                      *)
(***************************************************************************)
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness


(***************************************************************************)
(* We tested this specifications under the following conditions:           *)
(*     Behaviour Spec: Temporal formula - SpecLoseMsg                      *)
(*     Constant Values: MAX_PROCESSES <- 3, ID <- <<-1, 10, 4>>            *)
(*     Invariants: TypeInvariant                                           *)
(*     Properties: Agreement, Uniqueness, Termination                      *)
(***************************************************************************)
SpecLoseMsg ==
    /\ Init
    /\ [][NextLoseMsg]_vars
    /\ Fairness

================================================================================
