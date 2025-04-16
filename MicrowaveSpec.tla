---- MODULE MicrowaveSpec ----
EXTENDS Naturals

VARIABLES state

Init == state = "idle"

Next ==
    \/ /\ state = "idle" /\ state' = "cooking"
    \/ /\ state = "cooking" /\ state' = "idle"
    \/ /\ state' = state

Spec == Init /\ [][Next]_<<state>>
====
