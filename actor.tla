------------------------------- MODULE actor -------------------------------
EXTENDS TLC, Integers, Sequences, ChannelsReliable

between01(n1, nb, n2) == (nb >= 0) /\ (((n1 < n2) /\ ((n1 < nb) /\ (nb <= n2))) \/ ((n1 >= n2) /\ ((n1 < nb) \/ (nb <= n2))))
between00(n1, nb, n2) == (nb >= 0) /\ (((n1 < n2) /\ ((n1 < nb) /\ (nb < n2))) \/ ((n1 >= n2) /\ ((n1 < nb) \/ (nb < n2))))

CONSTANTS m, bm

\*Clients == {0, 1, 3}

(*--fair algorithm ActorStuff {
variables triggered = FALSE;
          fingerTables =  (0 :> ((1 :> 1) @@ (2 :> 3) @@ (4 :> 0))) 
          @@ (1 :> ((2 :> 3) @@ (3 :> 5) @@ (5 :> 0)))
          @@ (3 :> ((4 :> 0) @@ (5 :> 0) @@ (7 :> 0)));
          \*Channels = InitChannels(Clients);

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
{
 (*Channels := Send(Channels, 1, 0, <<"FindPredecessor", 6, 0>>,
                 "FindPredcessor60",
                 "Start");*)
  \*await HasMessage(Channels, self);
  HEY:
  with (wrapped \in NextMessages(Channels, self)) do
   with currentMessage = Payload(wrapped_msg) do
    kind := Head(currentMessage);
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
   end with;
  Channels := MarkMessageReceived(Channels, self, wrapped_msg, "Received")
  end with;
}
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "afae019c" /\ chksum(tla) = "5415e04a")
CONSTANT defaultInitValue
VARIABLES actorInboxes, triggered, fingerTables, pc, currentMessage, kind, id, 
          asker, i

vars == << actorInboxes, triggered, fingerTables, pc, currentMessage, kind, 
           id, asker, i >>

ProcSet == ({0, 1, 3})

Init == (* Global variables *)
        /\ actorInboxes = (0 :>  << <<"FindPredecessor", 6, 0>> >>) @@ (1 :>  <<>>) @@ (3 :> <<>>)
        /\ triggered = FALSE
        /\ fingerTables =                 (0 :> ((1 :> 1) @@ (2 :> 3) @@ (4 :> 0)))
                          @@ (1 :> ((2 :> 3) @@ (3 :> 5) @@ (5 :> 0)))
                          @@ (3 :> ((4 :> 0) @@ (5 :> 0) @@ (7 :> 0)))
        (* Process actor *)
        /\ currentMessage = [self \in {0, 1, 3} |-> <<"?", -1, -1>>]
        /\ kind = [self \in {0, 1, 3} |-> "?"]
        /\ id = [self \in {0, 1, 3} |-> -1]
        /\ asker = [self \in {0, 1, 3} |-> -1]
        /\ i = [self \in {0, 1, 3} |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> "WaitForMessages"]

WaitForMessages(self) == /\ pc[self] = "WaitForMessages"
                         /\ IF actorInboxes[self] /= <<>>
                               THEN /\ currentMessage' = [currentMessage EXCEPT ![self] = Head(actorInboxes[self])]
                                    /\ kind' = [kind EXCEPT ![self] = Head(currentMessage'[self])]
                                    /\ actorInboxes' = [actorInboxes EXCEPT ![self] = Tail(actorInboxes[self])]
                               ELSE /\ TRUE
                                    /\ UNCHANGED << actorInboxes, 
                                                    currentMessage, kind >>
                         /\ pc' = [pc EXCEPT ![self] = "ProcessMessage"]
                         /\ UNCHANGED << triggered, fingerTables, id, asker, i >>

ProcessMessage(self) == /\ pc[self] = "ProcessMessage"
                        /\ IF kind[self] = "FindPredecessor"
                              THEN /\ id' = [id EXCEPT ![self] = currentMessage[self][2]]
                                   /\ asker' = [asker EXCEPT ![self] = currentMessage[self][3]]
                                   /\ IF between01(self, id'[self], fingerTables[self][(self + 1)%bm])
                                         THEN /\ actorInboxes' = [actorInboxes EXCEPT ![asker'[self]] = Append(actorInboxes[asker'[self]], <<"Predecessor", self>>)]
                                              /\ pc' = [pc EXCEPT ![self] = "DefaultsBack"]
                                              /\ i' = i
                                         ELSE /\ i' = [i EXCEPT ![self] = m]
                                              /\ pc' = [pc EXCEPT ![self] = "FindFirstSuitableI"]
                                              /\ UNCHANGED actorInboxes
                                   /\ UNCHANGED triggered
                              ELSE /\ IF kind[self] = "Predecessor" /\ currentMessage[self][2] = 3
                                         THEN /\ triggered' = TRUE
                                         ELSE /\ TRUE
                                              /\ UNCHANGED triggered
                                   /\ pc' = [pc EXCEPT ![self] = "DefaultsBack"]
                                   /\ UNCHANGED << actorInboxes, id, asker, i >>
                        /\ UNCHANGED << fingerTables, currentMessage, kind >>

FindFirstSuitableI(self) == /\ pc[self] = "FindFirstSuitableI"
                            /\ IF i[self] > 0 /\ ~((self + (2^(i[self]-1)))%bm \in DOMAIN fingerTables[self])
                                  THEN /\ i' = [i EXCEPT ![self] = i[self] - 1]
                                       /\ pc' = [pc EXCEPT ![self] = "FindFirstSuitableI"]
                                  ELSE /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                                       /\ i' = i
                            /\ UNCHANGED << actorInboxes, triggered, 
                                            fingerTables, currentMessage, kind, 
                                            id, asker >>

MainLoop(self) == /\ pc[self] = "MainLoop"
                  /\ IF i[self] > 0 /\ ~(between00(self, fingerTables[self][(self + (2^(i[self]-1)))%bm], id[self]))
                        THEN /\ i' = [i EXCEPT ![self] = i[self] - 1]
                             /\ pc' = [pc EXCEPT ![self] = "FindSuitableI"]
                             /\ UNCHANGED actorInboxes
                        ELSE /\ IF i[self] = 0
                                   THEN /\ actorInboxes' = [actorInboxes EXCEPT ![fingerTables[self][(self + (2^(m-1)))%bm]] = Append(actorInboxes[fingerTables[self][(self + (2^(m-1)))%bm]], currentMessage[self])]
                                   ELSE /\ actorInboxes' = [actorInboxes EXCEPT ![fingerTables[self][(self + (2^(i[self]-1)))%bm]] = Append(actorInboxes[fingerTables[self][(self + (2^(i[self]-1)))%bm]], currentMessage[self])]
                             /\ pc' = [pc EXCEPT ![self] = "DefaultsBack"]
                             /\ i' = i
                  /\ UNCHANGED << triggered, fingerTables, currentMessage, 
                                  kind, id, asker >>

FindSuitableI(self) == /\ pc[self] = "FindSuitableI"
                       /\ IF i[self] > 0 /\ ~((self + (2^(i[self]-1)))%bm \in DOMAIN fingerTables[self])
                             THEN /\ i' = [i EXCEPT ![self] = i[self] - 1]
                                  /\ pc' = [pc EXCEPT ![self] = "FindSuitableI"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                                  /\ i' = i
                       /\ UNCHANGED << actorInboxes, triggered, fingerTables, 
                                       currentMessage, kind, id, asker >>

DefaultsBack(self) == /\ pc[self] = "DefaultsBack"
                      /\ currentMessage' = [currentMessage EXCEPT ![self] = <<"?", -1, -1>>]
                      /\ kind' = [kind EXCEPT ![self] = "?"]
                      /\ id' = [id EXCEPT ![self] = -1]
                      /\ asker' = [asker EXCEPT ![self] = -1]
                      /\ pc' = [pc EXCEPT ![self] = "WaitForMessages"]
                      /\ UNCHANGED << actorInboxes, triggered, fingerTables, i >>

actor(self) == WaitForMessages(self) \/ ProcessMessage(self)
                  \/ FindFirstSuitableI(self) \/ MainLoop(self)
                  \/ FindSuitableI(self) \/ DefaultsBack(self)

Next == (\E self \in {0, 1, 3}: actor(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in {0, 1, 3} : WF_vars(actor(self)) /\ SF_vars(WaitForMessages(self))

\* END TRANSLATION 

Triggered == triggered = TRUE

Liveness == <>[]Triggered

LenStateConstraint == Len(actorInboxes[0])<=1 /\ Len(actorInboxes[1])<=1 /\ Len(actorInboxes[3])<=1

=============================================================================
\* Modification History
\* Last modified Sun Feb 20 23:20:58 YEKT 2022 by pervu
\* Created Sun Jan 30 18:34:11 YEKT 2022 by pervu
