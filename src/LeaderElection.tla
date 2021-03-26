---- MODULE LeaderElection ----
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANTS 
    N, \* Number of processes
    STOP \* Max number of rounds for finite search space
ASSUME N \in Nat
Processes == 1..N

(* --algorithm LeaderElection
{

    variable
        mailbox = [p \in Processes |-> {}]; (*** TODO: Initialise all processes with an empty mailbox***)
        leader = [p \in Processes |-> 0];  \* all have not elected any leader
        round = [p \in Processes |-> 0];    \* all are at round 0
        elected = [p \in Processes |-> FALSE]

    define {
        (*** TODO: Pick the highest value in S ***)
        Max(S) == CHOOSE x \in S: \A y \in S: y <= x
    }
    
    fair process (p \in Processes)
    variables recv={};
        
    {
P:   while (round[self] < STOP) {
        recv := Processes;
Bcast:  while (recv # {}) {
            with (p \in recv) {
                (*** TODO: Send 'self' to all processes ***)
                mailbox[p] := mailbox[p] \union {self};
                recv := recv \ {p};
            };
        };  
        round[self] := round[self] + 1;(*** TODO: Advance to the next round ***)
        \* print mailbox;
        
Sync:   await \A pid \in Processes: round[pid] >= round[self];(*** TODO: Wait for processes to be in next round***)
        if (\A pid \in Processes: elected[pid] = TRUE) {
            goto END;
           } else {
            leader[self] := Max(mailbox[self]);(*** TODO: Choose leader ***)
            mailbox[self] := {};
            elected[self] := TRUE;}

    };
END: skip;
    } \* end process


}

*)
\* BEGIN TRANSLATION (chksum(pcal) = "c28704aa" /\ chksum(tla) = "2f1e1e40")
VARIABLES mailbox, leader, round, elected, pc

(* define statement *)
Max(S) == CHOOSE x \in S: \A y \in S: y <= x

VARIABLE recv

vars == << mailbox, leader, round, elected, pc, recv >>

ProcSet == (Processes)

Init == (* Global variables *)
        /\ mailbox = [p \in Processes |-> {}]
        /\ leader = [p \in Processes |-> 0]
        /\ round = [p \in Processes |-> 0]
        /\ elected = [p \in Processes |-> FALSE]
        (* Process p *)
        /\ recv = [self \in Processes |-> {}]
        /\ pc = [self \in ProcSet |-> "P"]

P(self) == /\ pc[self] = "P"
           /\ IF round[self] < STOP
                 THEN /\ recv' = [recv EXCEPT ![self] = Processes]
                      /\ pc' = [pc EXCEPT ![self] = "Bcast"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "END"]
                      /\ recv' = recv
           /\ UNCHANGED << mailbox, leader, round, elected >>

Bcast(self) == /\ pc[self] = "Bcast"
               /\ IF recv[self] # {}
                     THEN /\ \E p \in recv[self]:
                               /\ mailbox' = [mailbox EXCEPT ![p] = mailbox[p] \union {self}]
                               /\ recv' = [recv EXCEPT ![self] = recv[self] \ {p}]
                          /\ pc' = [pc EXCEPT ![self] = "Bcast"]
                          /\ round' = round
                     ELSE /\ round' = [round EXCEPT ![self] = round[self] + 1]
                          /\ pc' = [pc EXCEPT ![self] = "Sync"]
                          /\ UNCHANGED << mailbox, recv >>
               /\ UNCHANGED << leader, elected >>

Sync(self) == /\ pc[self] = "Sync"
              /\ \A pid \in Processes: round[pid] >= round[self]
              /\ IF \A pid \in Processes: elected[pid] = TRUE
                    THEN /\ pc' = [pc EXCEPT ![self] = "END"]
                         /\ UNCHANGED << mailbox, leader, elected >>
                    ELSE /\ leader' = [leader EXCEPT ![self] = Max(mailbox[self])]
                         /\ mailbox' = [mailbox EXCEPT ![self] = {}]
                         /\ elected' = [elected EXCEPT ![self] = TRUE]
                         /\ pc' = [pc EXCEPT ![self] = "P"]
              /\ UNCHANGED << round, recv >>

END(self) == /\ pc[self] = "END"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "Done"]
             /\ UNCHANGED << mailbox, leader, round, elected, recv >>

p(self) == P(self) \/ Bcast(self) \/ Sync(self) \/ END(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Processes: p(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Processes : WF_vars(p(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
\* Current problem, since we elect the leader in different speed. there would be cases such that different value has different leader- this is thus making the Agreement property harder to implement. 
Agreement == \A m, n \in Processes: (elected[m] = TRUE /\ elected[n] = TRUE) => leader[m] = leader[n]
\*Agreement == \A m, n \in Processes: (/\ (\A p1 \in Processes: pc[p1] = "Sync") /\ \A r1, r2 \in Processes: round[r1] = round[r2]) => leader[m] = leader[n]
EventualAgreement ==  <>(\A m, n \in Processes: leader[m] = leader[n])
Completness == <>(\A m \in Processes: leader[m] # 0)

====
