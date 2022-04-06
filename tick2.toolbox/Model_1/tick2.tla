------------------------------- MODULE tick2 -------------------------------
EXTENDS Reals
VARIABLE now, hr, t
CONSTANT Rho 
ASSUME (Rho \in Real) /\  (Rho > 0)

HCini  ==  hr \in (1 .. 12)
HCnxt  ==  hr' = IF hr # 12 THEN hr + 1 ELSE 1
HC  ==  HCini /\ [][HCnxt]_hr

TNext == t' = IF HCnxt THEN 0 ELSE t+(now'-now) 
Timer   == (t = 0)  /\  [][TNext]_<<t,hr, now>>
MaxTime == [](t \leq  3600 + Rho)  
MinTime == [][HCnxt => t \geq 3600 - Rho]_hr
HCTime  == Timer /\ MaxTime /\ MinTime

NowNext == /\ now' \in {r \in Real : r > now} 
           /\ UNCHANGED hr  

RTnow == /\ now \in Real 
         /\ [][NowNext]_now 
         /\ \A r \in Real : WF_now(NowNext /\ (now'>r))

RTHC == HC  /\  RTnow /\ HCTime

=============================================================================
\* Modification History
\* Last modified Wed Apr 06 21:04:15 YEKT 2022 by pervu
\* Created Wed Apr 06 20:41:53 YEKT 2022 by pervu
