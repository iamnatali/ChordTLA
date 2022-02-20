------------------------------- MODULE actor -------------------------------
EXTENDS TLC, Integers, Sequences

between01(n1, nb, n2) == ((n1 < n2) /\ ((n1 < nb) /\ (nb <= n2))) \/ ((n1 >= n2) /\ ((n1 < nb) \/ (nb <= n2))) 
between00(n1, nb, n2) == ((n1 < n2) /\ ((n1 < nb) /\ (nb < n2))) \/ ((n1 >= n2) /\ ((n1 < nb) \/ (nb < n2)))

CONSTANTS m, bm, fingerTables

(*--fair algorithm ActorStuff {
variables actorInboxes = (0 :>  << <<"FindPredecessor", 6, 0>> >>) @@ (1 :>  <<>>) @@ (3 :> <<>>);
          triggered = FALSE;

\*<<"FindPredecessor", id, asker>>
          
\*procedure trigger(trigger_content="?") {
\*    triggerLabel:
\*      triggered := TRUE;
\*      return;
\*}


fair process (actor \in {0, 1, 3})
variables currentMessage = <<"?", -1, -1>>;
  kind = "?";
  \*content = "no_content";
  id;
  asker;
  i;
{
\*  Send:
\*    actorInboxes["actor"] := Append(actorInboxes["actor"], <<"trigger", "foo">>);
  WaitForMessages:+
    while (TRUE) {
      if (actorInboxes[self] /= <<>>) {
         currentMessage := Head(actorInboxes[self]);               
         \*content := Head(Tail(currentMessage));
         kind := Head(currentMessage);
         actorInboxes[self] := Tail(actorInboxes[self]);
        };
        ProcessMessage:
         if (kind = "FindPredecessor") {
           id := currentMessage[2];
           asker := currentMessage[3];
           if (between01(self, id, fingerTables[self][(self + 1)%bm])){
            actorInboxes[asker] := Append(actorInboxes[asker], <<"Predecessor", self>>);
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
             actorInboxes[fingerTables[self][(self + (2^(m-1)))%bm]] := 
              Append(actorInboxes[fingerTables[self][(self + (2^(m-1)))%bm]], currentMessage);
             }else{
             actorInboxes[fingerTables[self][(self + (2^(i-1)))%bm]] := 
               Append(actorInboxes[fingerTables[self][(self + (2^(i-1)))%bm]], currentMessage);
             }
           }
         }else{
          if (kind = "Predecessor"){
           \* call trigger(content);
           triggered := TRUE;
          }
         }
    }
}
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "8843d64f" /\ chksum(tla) = "79f2a8b")
CONSTANT defaultInitValue
VARIABLES actorInboxes, triggered, pc, currentMessage, kind, id, asker, i

vars == << actorInboxes, triggered, pc, currentMessage, kind, id, asker, i >>

ProcSet == ({0, 1, 3})

Init == (* Global variables *)
        /\ actorInboxes = (0 :>  << <<"FindPredecessor", 6, 0>> >>) @@ (1 :>  <<>>) @@ (3 :> <<>>)
        /\ triggered = FALSE
        (* Process actor *)
        /\ currentMessage = [self \in {0, 1, 3} |-> <<"?", -1, -1>>]
        /\ kind = [self \in {0, 1, 3} |-> "?"]
        /\ id = [self \in {0, 1, 3} |-> defaultInitValue]
        /\ asker = [self \in {0, 1, 3} |-> defaultInitValue]
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
                         /\ UNCHANGED << triggered, id, asker, i >>

ProcessMessage(self) == /\ pc[self] = "ProcessMessage"
                        /\ IF kind[self] = "FindPredecessor"
                              THEN /\ id' = [id EXCEPT ![self] = currentMessage[self][2]]
                                   /\ asker' = [asker EXCEPT ![self] = currentMessage[self][3]]
                                   /\ IF between01(self, id'[self], fingerTables[self][(self + 1)%bm])
                                         THEN /\ actorInboxes' = [actorInboxes EXCEPT ![asker'[self]] = Append(actorInboxes[asker'[self]], <<"Predecessor", self>>)]
                                              /\ pc' = [pc EXCEPT ![self] = "WaitForMessages"]
                                              /\ i' = i
                                         ELSE /\ i' = [i EXCEPT ![self] = m]
                                              /\ pc' = [pc EXCEPT ![self] = "FindFirstSuitableI"]
                                              /\ UNCHANGED actorInboxes
                                   /\ UNCHANGED triggered
                              ELSE /\ IF kind[self] = "Predecessor"
                                         THEN /\ triggered' = TRUE
                                         ELSE /\ TRUE
                                              /\ UNCHANGED triggered
                                   /\ pc' = [pc EXCEPT ![self] = "WaitForMessages"]
                                   /\ UNCHANGED << actorInboxes, id, asker, i >>
                        /\ UNCHANGED << currentMessage, kind >>

FindFirstSuitableI(self) == /\ pc[self] = "FindFirstSuitableI"
                            /\ IF i[self] > 0 /\ ~((self + (2^(i[self]-1)))%bm \in DOMAIN fingerTables[self])
                                  THEN /\ i' = [i EXCEPT ![self] = i[self] - 1]
                                       /\ pc' = [pc EXCEPT ![self] = "FindFirstSuitableI"]
                                  ELSE /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                                       /\ i' = i
                            /\ UNCHANGED << actorInboxes, triggered, 
                                            currentMessage, kind, id, asker >>

MainLoop(self) == /\ pc[self] = "MainLoop"
                  /\ IF i[self] > 0 /\ ~(between00(self, fingerTables[self][(self + (2^(i[self]-1)))%bm], id[self]))
                        THEN /\ i' = [i EXCEPT ![self] = i[self] - 1]
                             /\ pc' = [pc EXCEPT ![self] = "FindSuitableI"]
                             /\ UNCHANGED actorInboxes
                        ELSE /\ IF i[self] = 0
                                   THEN /\ actorInboxes' = [actorInboxes EXCEPT ![fingerTables[self][(self + (2^(m-1)))%bm]] = Append(actorInboxes[fingerTables[self][(self + (2^(m-1)))%bm]], currentMessage[self])]
                                   ELSE /\ actorInboxes' = [actorInboxes EXCEPT ![fingerTables[self][(self + (2^(i[self]-1)))%bm]] = Append(actorInboxes[fingerTables[self][(self + (2^(i[self]-1)))%bm]], currentMessage[self])]
                             /\ pc' = [pc EXCEPT ![self] = "WaitForMessages"]
                             /\ i' = i
                  /\ UNCHANGED << triggered, currentMessage, kind, id, asker >>

FindSuitableI(self) == /\ pc[self] = "FindSuitableI"
                       /\ IF i[self] > 0 /\ ~((self + (2^(i[self]-1)))%bm \in DOMAIN fingerTables[self])
                             THEN /\ i' = [i EXCEPT ![self] = i[self] - 1]
                                  /\ pc' = [pc EXCEPT ![self] = "FindSuitableI"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                                  /\ i' = i
                       /\ UNCHANGED << actorInboxes, triggered, currentMessage, 
                                       kind, id, asker >>

actor(self) == WaitForMessages(self) \/ ProcessMessage(self)
                  \/ FindFirstSuitableI(self) \/ MainLoop(self)
                  \/ FindSuitableI(self)

Next == (\E self \in {0, 1, 3}: actor(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in {0, 1, 3} : WF_vars(actor(self)) /\ SF_vars(WaitForMessages(self))

\* END TRANSLATION 

Triggered == triggered = TRUE

Liveness == <>[]Triggered

=============================================================================
\* Modification History
\* Last modified Sun Feb 20 13:40:40 YEKT 2022 by pervu
\* Created Sun Jan 30 18:34:11 YEKT 2022 by pervu
