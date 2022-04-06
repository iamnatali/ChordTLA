-------------------------------- MODULE tick --------------------------------
EXTENDS RealTime

    -------------------------------- MODULE inner --------------------------------
    
    VARIABLES checked1, checked2, res
    
    Init == /\ checked1 = FALSE 
            /\ checked2 = FALSE
            /\ res = FALSE
    
    Action == /\ res' = IF checked1 /\ checked2 THEN res ELSE TRUE
              /\ UNCHANGED<< checked1, checked2 >>
    
    Action1 == (checked1 = FALSE) /\ (checked1' = TRUE)
    
    Action2 == (checked2 = FALSE) /\ (checked2' = TRUE)
    
    Next == Action1 /\ Action2 /\ Action
    
    ISpec == /\ Init  
            /\ [][Next]_<<checked1, checked2>>
            /\ RTBound(Action1, checked1, 0, 5)
            /\ RTBound(Action2, checked2, 0, 5)
            /\ RTnow(<<checked1, checked2>>)
    
    Triggered == res = TRUE
    
    Liveness == <>[]Triggered
    =============================================================================

inner(checked1, checked2, res) == INSTANCE inner

Spec == \EE checked1, checked2, res: inner(checked1, checked2, res)!ISpec

=============================================================================
\* Modification History
\* Last modified Wed Apr 06 20:20:24 YEKT 2022 by pervu
\* Created Wed Apr 06 18:12:21 YEKT 2022 by pervu
