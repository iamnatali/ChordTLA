------------------------------- MODULE actor -------------------------------
EXTENDS TLC, Integers, Sequences, ChannelsReliable

between01(n1, nb, n2) == (nb >= 0) /\ (((n1 < n2) /\ ((n1 < nb) /\ (nb <= n2))) \/ ((n1 >= n2) /\ ((n1 < nb) \/ (nb <= n2))))
between00(n1, nb, n2) == (nb >= 0) /\ (((n1 < n2) /\ ((n1 < nb) /\ (nb < n2))) \/ ((n1 >= n2) /\ ((n1 < nb) \/ (nb < n2))))

CONSTANTS m, bm

Clients == {0, 1, 3}

(*--fair algorithm ActorStuff {
variables triggered = FALSE;
          Channels = InitChannels(Clients);
          fingerTables =  (0 :> ((1 :> 1) @@ (2 :> 3) @@ (4 :> 0))) 
          @@ (1 :> ((2 :> 3) @@ (3 :> 5) @@ (5 :> 0)))
          @@ (3 :> ((4 :> 0) @@ (5 :> 0) @@ (7 :> 0)));

\*<<"FindPredecessor", id, asker>>
          
\*procedure trigger(trigger_content="?") {
\*    triggerLabel:
\*      triggered := TRUE;
\*      return;
\*}

fair process (actor \in Clients)
variables currentMessage = <<"?", -1, -1>>;
  kind = "?";
  id = -1;
  asker = -1;
  i;
  my_wrapped_msg;
{
 StartSend:
 if (self = 1){
 Channels := Send(Channels, self, 0, <<"FindPredecessor", 6, 0>>,
                 "FindPredcessor60",
                 "Start");
 };
 Wait:
 await HasMessage(Channels, self);
 ProcessMes:
 with (wrapped_msg \in NextMessages(Channels, self)){
  with (mes = Payload(wrapped_msg)){
    currentMessage := mes;
    kind := Head(currentMessage);
    my_wrapped_msg := wrapped_msg;
    };
    };
    if (kind = "FindPredecessor") {
           id := currentMessage[2];
           asker := currentMessage[3];
           if (between01(self, id, fingerTables[self][(self + 1)%bm])){
           Channels := Send(Channels, self, asker, <<"Predecessor", self>>,
                 "Predecessor",
                 "End");
           } else {
            i := m;
            FindFirstSuitableI:
             while (i > 0 /\ ~((self + (2^(i-1)))%bm \in DOMAIN fingerTables[self])){
              i := i - 1;
             };
            MainLoop:
             while (i > 0 /\ ~(between00(self, fingerTables[self][(self + (2^(i-1)))%bm], id))){
              i := i - 1;
              FindSuitableI:
              while (i > 0 /\ ~((self + (2^(i-1)))%bm \in DOMAIN fingerTables[self])){
               i:= i - 1;
              };
             };
            if (i = 0){
            Channels := Send(Channels, self, fingerTables[self][(self + (2^(m-1)))%bm], currentMessage,
                 "Transit",
                 "Transit");
             }else{
             Channels := Send(Channels, self, fingerTables[self][(self + (2^(i-1)))%bm], currentMessage,
                 "Transit",
                 "Transit");
             }
           }
         }else{
          if (kind = "Predecessor" /\ currentMessage[2] = 3){
           \* call trigger(content);
           triggered := TRUE;
          }
         };
         Mark:
         Channels := MarkMessageReceived(Channels, self, my_wrapped_msg, "Received");
}
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "635a2e0a" /\ chksum(tla) = "30915de4")
CONSTANT defaultInitValue
VARIABLES triggered, Channels, fingerTables, pc, currentMessage, kind, id, 
          asker, i, my_wrapped_msg

vars == << triggered, Channels, fingerTables, pc, currentMessage, kind, id, 
           asker, i, my_wrapped_msg >>

ProcSet == (Clients)

Init == (* Global variables *)
        /\ triggered = FALSE
        /\ Channels = InitChannels(Clients)
        /\ fingerTables =                 (0 :> ((1 :> 1) @@ (2 :> 3) @@ (4 :> 0)))
                          @@ (1 :> ((2 :> 3) @@ (3 :> 5) @@ (5 :> 0)))
                          @@ (3 :> ((4 :> 0) @@ (5 :> 0) @@ (7 :> 0)))
        (* Process actor *)
        /\ currentMessage = [self \in Clients |-> <<"?", -1, -1>>]
        /\ kind = [self \in Clients |-> "?"]
        /\ id = [self \in Clients |-> -1]
        /\ asker = [self \in Clients |-> -1]
        /\ i = [self \in Clients |-> defaultInitValue]
        /\ my_wrapped_msg = [self \in Clients |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> "StartSend"]

StartSend(self) == /\ pc[self] = "StartSend"
                   /\ IF self = 1
                         THEN /\ Channels' = Send(Channels, self, 0, <<"FindPredecessor", 6, 0>>,
                                                 "FindPredcessor60",
                                                 "Start")
                         ELSE /\ TRUE
                              /\ UNCHANGED Channels
                   /\ pc' = [pc EXCEPT ![self] = "Wait"]
                   /\ UNCHANGED << triggered, fingerTables, currentMessage, 
                                   kind, id, asker, i, my_wrapped_msg >>

Wait(self) == /\ pc[self] = "Wait"
              /\ HasMessage(Channels, self)
              /\ pc' = [pc EXCEPT ![self] = "ProcessMes"]
              /\ UNCHANGED << triggered, Channels, fingerTables, 
                              currentMessage, kind, id, asker, i, 
                              my_wrapped_msg >>

ProcessMes(self) == /\ pc[self] = "ProcessMes"
                    /\ \E wrapped_msg \in NextMessages(Channels, self):
                         LET mes == Payload(wrapped_msg) IN
                           /\ currentMessage' = [currentMessage EXCEPT ![self] = mes]
                           /\ kind' = [kind EXCEPT ![self] = Head(currentMessage'[self])]
                           /\ my_wrapped_msg' = [my_wrapped_msg EXCEPT ![self] = wrapped_msg]
                    /\ IF kind'[self] = "FindPredecessor"
                          THEN /\ id' = [id EXCEPT ![self] = currentMessage'[self][2]]
                               /\ asker' = [asker EXCEPT ![self] = currentMessage'[self][3]]
                               /\ IF between01(self, id'[self], fingerTables[self][(self + 1)%bm])
                                     THEN /\ Channels' =       Send(Channels, self, asker'[self], <<"Predecessor", self>>,
                                                         "Predecessor",
                                                         "End")
                                          /\ pc' = [pc EXCEPT ![self] = "Mark"]
                                          /\ i' = i
                                     ELSE /\ i' = [i EXCEPT ![self] = m]
                                          /\ pc' = [pc EXCEPT ![self] = "FindFirstSuitableI"]
                                          /\ UNCHANGED Channels
                               /\ UNCHANGED triggered
                          ELSE /\ IF kind'[self] = "Predecessor" /\ currentMessage'[self][2] = 3
                                     THEN /\ triggered' = TRUE
                                     ELSE /\ TRUE
                                          /\ UNCHANGED triggered
                               /\ pc' = [pc EXCEPT ![self] = "Mark"]
                               /\ UNCHANGED << Channels, id, asker, i >>
                    /\ UNCHANGED fingerTables

FindFirstSuitableI(self) == /\ pc[self] = "FindFirstSuitableI"
                            /\ IF i[self] > 0 /\ ~((self + (2^(i[self]-1)))%bm \in DOMAIN fingerTables[self])
                                  THEN /\ i' = [i EXCEPT ![self] = i[self] - 1]
                                       /\ pc' = [pc EXCEPT ![self] = "FindFirstSuitableI"]
                                  ELSE /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                                       /\ i' = i
                            /\ UNCHANGED << triggered, Channels, fingerTables, 
                                            currentMessage, kind, id, asker, 
                                            my_wrapped_msg >>

MainLoop(self) == /\ pc[self] = "MainLoop"
                  /\ IF i[self] > 0 /\ ~(between00(self, fingerTables[self][(self + (2^(i[self]-1)))%bm], id[self]))
                        THEN /\ i' = [i EXCEPT ![self] = i[self] - 1]
                             /\ pc' = [pc EXCEPT ![self] = "FindSuitableI"]
                             /\ UNCHANGED Channels
                        ELSE /\ IF i[self] = 0
                                   THEN /\ Channels' =        Send(Channels, self, fingerTables[self][(self + (2^(m-1)))%bm], currentMessage[self],
                                                       "Transit",
                                                       "Transit")
                                   ELSE /\ Channels' =         Send(Channels, self, fingerTables[self][(self + (2^(i[self]-1)))%bm], currentMessage[self],
                                                       "Transit",
                                                       "Transit")
                             /\ pc' = [pc EXCEPT ![self] = "Mark"]
                             /\ i' = i
                  /\ UNCHANGED << triggered, fingerTables, currentMessage, 
                                  kind, id, asker, my_wrapped_msg >>

FindSuitableI(self) == /\ pc[self] = "FindSuitableI"
                       /\ IF i[self] > 0 /\ ~((self + (2^(i[self]-1)))%bm \in DOMAIN fingerTables[self])
                             THEN /\ i' = [i EXCEPT ![self] = i[self] - 1]
                                  /\ pc' = [pc EXCEPT ![self] = "FindSuitableI"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                                  /\ i' = i
                       /\ UNCHANGED << triggered, Channels, fingerTables, 
                                       currentMessage, kind, id, asker, 
                                       my_wrapped_msg >>

Mark(self) == /\ pc[self] = "Mark"
              /\ Channels' = MarkMessageReceived(Channels, self, my_wrapped_msg[self], "Received")
              /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ UNCHANGED << triggered, fingerTables, currentMessage, kind, 
                              id, asker, i, my_wrapped_msg >>

actor(self) == StartSend(self) \/ Wait(self) \/ ProcessMes(self)
                  \/ FindFirstSuitableI(self) \/ MainLoop(self)
                  \/ FindSuitableI(self) \/ Mark(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Clients: actor(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in Clients : WF_vars(actor(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

Triggered == triggered = TRUE

Liveness == <>[]Triggered

\*LenStateConstraint == Len(actorInboxes[0])<=1 /\ Len(actorInboxes[1])<=1 /\ Len(actorInboxes[3])<=1

=============================================================================
\* Modification History
\* Last modified Sun Feb 20 23:58:07 YEKT 2022 by pervu
\* Created Sun Jan 30 18:34:11 YEKT 2022 by pervu
