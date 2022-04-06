------------------------------- MODULE tick2 -------------------------------
EXTENDS Reals 
VARIABLE now, test

RTBound(A, v, D, E) == 
  LET TNext(t)  ==  t' = IF <<A>>_v \/ ~(ENABLED <<A>>_v)'
                           THEN 0 
                           ELSE t + (now'-now)

      Timer(t) == (t=0)  /\  [][TNext(t)]_<<t, v, now>>

      MaxTime(t) == [](t \leq E) 

      MinTime(t) == [][A => t \geq D]_v 
  IN \EE t : Timer(t) /\ MaxTime(t) /\ MinTime(t)
  
RTnow(v) == LET NowNext == /\ now' \in {r \in Real : r > now} 
                           /\ UNCHANGED v
            IN  /\ now \in Real 
                /\ [][NowNext]_now
                /\ \A r \in Real : WF_now(NowNext /\ (now'>r))

Init == test = TRUE

Next == test' = FALSE

=============================================================================
\* Modification History
\* Last modified Wed Apr 06 20:43:25 YEKT 2022 by pervu
\* Created Wed Apr 06 20:41:53 YEKT 2022 by pervu
