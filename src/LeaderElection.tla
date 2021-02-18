---- MODULE LeaderElectionCrash ----
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANTS 
    N, \* Number of processes
    STOP \* Max number of rounds for finite search space
ASSUME N \in Nat
Processes == 1..N

(* --algorithm LeaderElection
{

    variable
        mailbox = (*** TODO: Initialise all processes with an empty mailbox***)
        leader = [p \in Processes |-> 0];  \* all have not elected any leader
        round = [p \in Processes |-> 0];    \* all are at round 0

    define {
        Max(S) == (*** TODO: Pick the highest value in S ***)
    }
    
    fair process (p \in Processes)
    variable recv={};
    {
P:   while (round[self] < STOP) {
        recv := Processes;
Bcast:  while (recv # {}) {
            with (p \in recv) {
                (*** TODO: Send 'self' to all processes ***)
            };
        };  
        (*** TODO: Advance to the next round ***)
Sync:   (*** TODO: Wait for processes to be in next round***)
        leader[self] := (*** TODO: Choose leader ***);
    };
    } \* end process

}

*)

====
