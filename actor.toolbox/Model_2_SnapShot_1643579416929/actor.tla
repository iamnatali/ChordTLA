------------------------------- MODULE actor -------------------------------
EXTENDS TLC, Integers, Sequences

between01(n1, nb, n2) == ((n1 < n2) => ((n1 < nb) \cap (nb <= n2))) \cup ((n1 >= n2) => ((n1 < nb) \cup (nb <= n2))) 
between00(n1, nb, n2) == ((n1 < n2) => ((n1 < nb) \cap (nb < n2))) \cup ((n1 >= n2) => ((n1 < nb) \cup (nb < n2)))

(*--fair algorithm ActorStuff {
variables actorInboxes = (0 :>  << <<"FindPredecessor", 6, 0>> >>) @@ (1 :>  <<>>) @@ (3 :> <<>>);
          fingerTables = (0 :> (1 :> 1) @@ (2 :> 3) @@ (4 :> 0)) 
          @@ (1 :> (2 :> 3) @@ (3 :> 5) @@ (5 :> 0))
          @@ (3 :> (4 :> 0) @@ (5 :> 0) @@ (7 :> 0));
          triggered = FALSE;
          m = 3;

          
procedure trigger(trigger_content="?") {
    triggerLabel:
      triggered := TRUE;
      return;
}

\* нет mod
fair process (actor \in {0, 1, 3})
variables currentMessage = <<"?", "no_content">>;
  kind = "?";
  content = "no_content";
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
         content := Head(Tail(currentMessage));
         kind := Head(currentMessage);
         actorInboxes[self] := Tail(actorInboxes[self]);
        };
        ProcessMessage:
         if (kind = "FindPredecessor") {
           id := content[1];
           asker := content[2]; 
           if (between01(self, id, fingerTables[self][self + 1])){
            actorInboxes[asker] := Append(actorInboxes[asker], <<"Predecessor", self>>);
           } else {
            i := m;
            LOOP: 
             while (i > 0 \cap ~(between00(self, fingerTables[self][self + (2^(i-1))], id))){
              i:= i - 1;
             };
            if (i = 0){
            actorInboxes[fingerTables[self][self + (2^(m-1))]] := 
               Append(actorInboxes[fingerTables[self][self + (2^(m-1))]], currentMessage);
            }else{
            actorInboxes[fingerTables[self][self + (2^(i-1))]] := 
             Append(actorInboxes[fingerTables[self][self + (2^(i-1))]], currentMessage);
            }
            
           }
         }else{
          if (kind = "Predecessor"){
           call trigger(content);
          }
         }
    }
}
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "1bd65266" /\ chksum(tla) = "cfb8b6c9")
CONSTANT defaultInitValue
VARIABLES actorInboxes, fingerTables, triggered, m, pc, stack, 
          trigger_content, currentMessage, kind, content, id, asker, i

vars == << actorInboxes, fingerTables, triggered, m, pc, stack, 
           trigger_content, currentMessage, kind, content, id, asker, i >>

ProcSet == ({0, 1, 3})

Init == (* Global variables *)
        /\ actorInboxes = (0 :>  << <<"FindPredecessor", 6, 0>> >>) @@ (1 :>  <<>>) @@ (3 :> <<>>)
        /\ fingerTables =                (0 :> (1 :> 1) @@ (2 :> 3) @@ (4 :> 0))
                          @@ (1 :> (2 :> 3) @@ (3 :> 5) @@ (5 :> 0))
                          @@ (3 :> (4 :> 0) @@ (5 :> 0) @@ (7 :> 0))
        /\ triggered = FALSE
        /\ m = 3
        (* Procedure trigger *)
        /\ trigger_content = [ self \in ProcSet |-> "?"]
        (* Process actor *)
        /\ currentMessage = [self \in {0, 1, 3} |-> <<"?", "no_content">>]
        /\ kind = [self \in {0, 1, 3} |-> "?"]
        /\ content = [self \in {0, 1, 3} |-> "no_content"]
        /\ id = [self \in {0, 1, 3} |-> defaultInitValue]
        /\ asker = [self \in {0, 1, 3} |-> defaultInitValue]
        /\ i = [self \in {0, 1, 3} |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "WaitForMessages"]

triggerLabel(self) == /\ pc[self] = "triggerLabel"
                      /\ triggered' = TRUE
                      /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                      /\ trigger_content' = [trigger_content EXCEPT ![self] = Head(stack[self]).trigger_content]
                      /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                      /\ UNCHANGED << actorInboxes, fingerTables, m, 
                                      currentMessage, kind, content, id, asker, 
                                      i >>

trigger(self) == triggerLabel(self)

WaitForMessages(self) == /\ pc[self] = "WaitForMessages"
                         /\ IF actorInboxes[self] /= <<>>
                               THEN /\ currentMessage' = [currentMessage EXCEPT ![self] = Head(actorInboxes[self])]
                                    /\ content' = [content EXCEPT ![self] = Head(Tail(currentMessage'[self]))]
                                    /\ kind' = [kind EXCEPT ![self] = Head(currentMessage'[self])]
                                    /\ actorInboxes' = [actorInboxes EXCEPT ![self] = Tail(actorInboxes[self])]
                               ELSE /\ TRUE
                                    /\ UNCHANGED << actorInboxes, 
                                                    currentMessage, kind, 
                                                    content >>
                         /\ pc' = [pc EXCEPT ![self] = "ProcessMessage"]
                         /\ UNCHANGED << fingerTables, triggered, m, stack, 
                                         trigger_content, id, asker, i >>

ProcessMessage(self) == /\ pc[self] = "ProcessMessage"
                        /\ IF kind[self] = "FindPredecessor"
                              THEN /\ id' = [id EXCEPT ![self] = content[self][1]]
                                   /\ asker' = [asker EXCEPT ![self] = content[self][2]]
                                   /\ IF between01(self, id'[self], fingerTables[self][self + 1])
                                         THEN /\ actorInboxes' = [actorInboxes EXCEPT ![asker'[self]] = Append(actorInboxes[asker'[self]], <<"Predecessor", self>>)]
                                              /\ pc' = [pc EXCEPT ![self] = "WaitForMessages"]
                                              /\ i' = i
                                         ELSE /\ i' = [i EXCEPT ![self] = m]
                                              /\ pc' = [pc EXCEPT ![self] = "LOOP"]
                                              /\ UNCHANGED actorInboxes
                                   /\ UNCHANGED << stack, trigger_content >>
                              ELSE /\ IF kind[self] = "Predecessor"
                                         THEN /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "trigger",
                                                                                          pc        |->  "WaitForMessages",
                                                                                          trigger_content |->  trigger_content[self] ] >>
                                                                                      \o stack[self]]
                                                 /\ trigger_content' = [trigger_content EXCEPT ![self] = content[self]]
                                              /\ pc' = [pc EXCEPT ![self] = "triggerLabel"]
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "WaitForMessages"]
                                              /\ UNCHANGED << stack, 
                                                              trigger_content >>
                                   /\ UNCHANGED << actorInboxes, id, asker, i >>
                        /\ UNCHANGED << fingerTables, triggered, m, 
                                        currentMessage, kind, content >>

LOOP(self) == /\ pc[self] = "LOOP"
              /\ IF i[self] > 0 \cap ~(between00(self, fingerTables[self][self + (2^(i[self]-1))], id[self]))
                    THEN /\ i' = [i EXCEPT ![self] = i[self] - 1]
                         /\ pc' = [pc EXCEPT ![self] = "LOOP"]
                         /\ UNCHANGED actorInboxes
                    ELSE /\ IF i[self] = 0
                               THEN /\ actorInboxes' = [actorInboxes EXCEPT ![fingerTables[self][self + (2^(m-1))]] = Append(actorInboxes[fingerTables[self][self + (2^(m-1))]], currentMessage[self])]
                               ELSE /\ actorInboxes' = [actorInboxes EXCEPT ![fingerTables[self][self + (2^(i[self]-1))]] = Append(actorInboxes[fingerTables[self][self + (2^(i[self]-1))]], currentMessage[self])]
                         /\ pc' = [pc EXCEPT ![self] = "WaitForMessages"]
                         /\ i' = i
              /\ UNCHANGED << fingerTables, triggered, m, stack, 
                              trigger_content, currentMessage, kind, content, 
                              id, asker >>

actor(self) == WaitForMessages(self) \/ ProcessMessage(self) \/ LOOP(self)

Next == (\E self \in ProcSet: trigger(self))
           \/ (\E self \in {0, 1, 3}: actor(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in {0, 1, 3} : /\ WF_vars(actor(self))
                                   /\ SF_vars(WaitForMessages(self))
                                   /\ WF_vars(trigger(self))

\* END TRANSLATION 

Triggered == triggered = TRUE

Liveness == <>Triggered

=============================================================================
\* Modification History
\* Last modified Mon Jan 31 02:48:58 YEKT 2022 by pervu
\* Created Sun Jan 30 18:34:11 YEKT 2022 by pervu
