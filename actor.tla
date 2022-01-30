------------------------------- MODULE actor -------------------------------
EXTENDS TLC, Integers, Sequences

(*--fair algorithm ActorStuff {
variables actorInboxes = ("actor1" :>  <<>>) @@ ("actor2" :>  << <<"OthersJoin", "actor1">> >>);
          triggered = FALSE;
          
procedure trigger(trigger_content="?") {
    triggerLabel:
      triggered := TRUE;
      return;
}

fair process (actor \in {"actor1", "actor2"})
variables currentMessage = <<"?", "no_content">>;
  kind = "?";
  content = "no_content";
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
         if (kind = "OthersJoin") {
           call trigger(content);
         }
    }
}
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "1ce3a16a" /\ chksum(tla) = "d68b17d6")
VARIABLES actorInboxes, triggered, pc, stack, trigger_content, currentMessage, 
          kind, content

vars == << actorInboxes, triggered, pc, stack, trigger_content, 
           currentMessage, kind, content >>

ProcSet == ({"actor1", "actor2"})

Init == (* Global variables *)
        /\ actorInboxes = ("actor1" :>  <<>>) @@ ("actor2" :>  << <<"OthersJoin", "actor1">> >>)
        /\ triggered = FALSE
        (* Procedure trigger *)
        /\ trigger_content = [ self \in ProcSet |-> "?"]
        (* Process actor *)
        /\ currentMessage = [self \in {"actor1", "actor2"} |-> <<"?", "no_content">>]
        /\ kind = [self \in {"actor1", "actor2"} |-> "?"]
        /\ content = [self \in {"actor1", "actor2"} |-> "no_content"]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "WaitForMessages"]

triggerLabel(self) == /\ pc[self] = "triggerLabel"
                      /\ triggered' = TRUE
                      /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                      /\ trigger_content' = [trigger_content EXCEPT ![self] = Head(stack[self]).trigger_content]
                      /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                      /\ UNCHANGED << actorInboxes, currentMessage, kind, 
                                      content >>

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
                         /\ UNCHANGED << triggered, stack, trigger_content >>

ProcessMessage(self) == /\ pc[self] = "ProcessMessage"
                        /\ IF kind[self] = "OthersJoin"
                              THEN /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "trigger",
                                                                               pc        |->  "WaitForMessages",
                                                                               trigger_content |->  trigger_content[self] ] >>
                                                                           \o stack[self]]
                                      /\ trigger_content' = [trigger_content EXCEPT ![self] = content[self]]
                                   /\ pc' = [pc EXCEPT ![self] = "triggerLabel"]
                              ELSE /\ pc' = [pc EXCEPT ![self] = "WaitForMessages"]
                                   /\ UNCHANGED << stack, trigger_content >>
                        /\ UNCHANGED << actorInboxes, triggered, 
                                        currentMessage, kind, content >>

actor(self) == WaitForMessages(self) \/ ProcessMessage(self)

Next == (\E self \in ProcSet: trigger(self))
           \/ (\E self \in {"actor1", "actor2"}: actor(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in {"actor1", "actor2"} : /\ WF_vars(actor(self))
                                              /\ SF_vars(WaitForMessages(self))
                                              /\ WF_vars(trigger(self))

\* END TRANSLATION 

Triggered == triggered = TRUE

Liveness == <>Triggered

=============================================================================
\* Modification History
\* Last modified Sun Jan 30 19:36:45 YEKT 2022 by pervu
\* Created Sun Jan 30 18:34:11 YEKT 2022 by pervu
