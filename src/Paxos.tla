------------------------------- MODULE Paxos -------------------------------
EXTENDS Integers, Sequences, FiniteSets
CONSTANT M, N, STOP, MAXB
ASSUME M \in Nat /\ N \in Nat /\ M<=N
Proposer == 0..M-1
Acceptor == M..N
\* \* M Proposers, and N-M+1 acceptors
Slots == 1..STOP
Ballots == 0..MAXB
\* \* In the model, use M=2, N=3, STOP=3 (number of slots), MAXB=10

(*--algorithm Paxos
 { variable AccMsg={}, PMsg={}; \* AccMsg: all Acceptor's receiving channel and PMsg: All Proposers' recv channel 

   define{
   ExtractValSet(S) == {m.valSet : m \in S} 
   MaxVal(S,s) == (*** TODO: Pick the tuple <<s,b,v>> from S that has the given slot s and highest ballot b ***)

   SentAccMsgs(t,b) == (*** TODO: Get all the msgs in AccMsg that has type t and ballot b***)
   SentPMsgs(t,b) == (*** TODO: Same as above but with PMsg***)
   SentPMsgs2(t,b,s) == (*** TODO: Same as above but match slot s as well ***)
   
   ExistMsg(C, t, b) == \E m \in C: m.type=t /\ m.bal = b (*** Checks if there exists a msg with type t and ballot b in C ***)
   LostLeadership (*** TODO: Macro that checks if leadership has been lost ***) 
   }
   
\* \* Proposer calls this to send prepare msg to acceptors
   macro SendPrepare (b) 
   {
     AccMsg:=AccMsg \union {[type |->"prepare", bal |-> b]};
   }

\* \* acceptor calls this to reply with a promise msg to Proposer
   macro ReplyPrepare (b)
   {
    await (b> maxBal) /\ (SentAccMsgs("prepare",b) #{});
    maxBal:=b;
    (*** TODO: Send Promise of this ballot ***)
   }

\* \* Proposer calls this to collect promise msgs from acceptors
   macro CollectPromises (b) 
   {
    await \/ (*** TODO: Wait for either getting a majority of promises from acceptors ***) 
          \/ (\E B \in Ballots: B>b /\ ExistMsg(LMsg, "promise",B));    (*** OR we lost leadership i.e. another proposer has overtaken us as leader ***)
    if (~ LostLeadership(*** TODO: arguments for macro ***)) {
       elected:=TRUE;
       pVal:=UNION ExtractValSet(SentPMsgs("promise",b));
    }  
   }


\* \* Proposer calls this to send accept msg to acceptors
   macro SendAccept (b,s) 
   {
    if (Cardinality({pv \in pVal: pv[1]=s})=0)
         AccMsg:=AccMsg \union {[type |-> "accept", bal |-> b, slot |-> s, val |-> <<s,b,self>> ]};
    else AccMsg:=AccMsg \union {[type |-> "accept", bal |-> b, slot |-> s, val |->MaxVal(pVal,s)]};  
   }

\* \* acceptor calls this to reply with a accepted msg to Proposer
   macro ReplyAccept (b) 
   {
    await (b>= maxBal); 
    with (m \in SentAccMsgs("accept",b)){
      maxBal:=b; 
      acceptedValues:= acceptedValues \union {m.val}; \* update val heard with message of maxBal so far
      PMsg:=PMsg \union {[type |->"accepted", acc |-> self, bal |-> b, slot|-> m.slot, vv |->m.val[3] ]};
    }
   }

\* \* Proposer calls this to collect promise msgs from acceptors
   macro CollectAccepted (b,s) 
   {
    await \/ (*** TODO: Wait for either getting a majority of promises from acceptors ***) 
          \/ (\E B \in Ballots: B>b /\ ExistMsg(LMsg, "promise",B));    (*** OR we lost leadership i.e. another proposer has overtaken us as leader ***)
    if (LostLeadership(*** TODO: arguments for macro ***)) {
       elected:=FALSE;
    else with (m \in SentPMsgs("accepted",b)) {lv:=m.vv;}   
   }

\* \* Proposer calls this to finalize decision for slot s
   macro SendDecide (b,s) 
   {
    AccMsg := AccMsg \union {[type |-> "decide", bal |-> b, slot |-> s, dcd |->lv ]};
   }

\* \* acceptor calls this to finalize decision for slot 
   macro RcvDecide (b) 
   {
    await (b>= maxBal); 
    with (m \in SentAccMsgs("decide",b)){
      maxBal:=b;
      decided[m.slot]:= decided[m.slot] \union {m.dcd};
    }
   }
   
\* \* Acceptor process actions
   fair process (a \in Acceptor)
   variable maxBal=-1, acceptedValues={<<-1,-1,-1>>}, \* \* <<s,b,v>>
            decided=[i \in Slots |-> {}];
   {
    A:  while (TRUE) {
            with (ba \in Ballots) {
                either ReplyPrepare(ba)
                or ReplyAccept(ba)
                or RcvDecide(ba)
            }
        }
   } 


\* \* Proposer process
   fair process (p \in Proposer)
   variable b=self, s=1, elected=FALSE, lv=-1, pVal={<<-1,-1,-1>>}; \* \* <<s,b,v>> 
   {
    L:  while (s \in Slots /\ b \in Ballots) {
        \*\* Try to get elected as Leader first
        P1L:  while (elected # TRUE) { 
                b:=b+M; \*\* guarantees unique ballot num
                SendPrepare(b);
        CP1L:     CollectPromises(b);
        }; 
        \*\* Move to phase2          
        P2L:  SendAccept(b,s);
        CP2L: CollectAccepted(b,s); 
        \*\* Move to phase 3      
        P3L:  if (elected=TRUE){ \*\* Proposer may have been overthrown in P2
                SendDecide (b,s); 
                s:=s+1;
            };
        } 
   } 

}
*)

====
