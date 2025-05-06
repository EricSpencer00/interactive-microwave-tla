---------------------------- MODULE MicrowaveSpec ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

VARIABLES timer, state

vars == <<timer, state>>

TypeOK == timer \in Nat /\ state \in {"DOOR_OPEN", "DOOR_CLOSED", "COOKING", "PAUSED"}

Init == timer = 0 /\ state = "DOOR_CLOSED"

OpenDoor == state = "DOOR_CLOSED" /\ state' = "DOOR_OPEN" /\ timer' = timer
CloseDoor == state = "DOOR_OPEN" /\ state' = "DOOR_CLOSED" /\ timer' = timer
StartCooking == state = "DOOR_CLOSED" /\ timer > 0 /\ state' = "COOKING" /\ timer' = timer
StopClock == state = "COOKING" /\ state' = "PAUSED" /\ timer' = timer
Tick == state = "COOKING" /\ timer > 0 /\ timer' = timer - 1 /\ state' = IF timer' = 0 THEN "DOOR_CLOSED" ELSE "COOKING"
ResetClock == state \in {"COOKING", "PAUSED"} /\ state' = "DOOR_CLOSED" /\ timer' = 0
AddTime == state \in {"DOOR_CLOSED", "PAUSED"} /\ timer' = timer + 10 /\ state' = state

Next == OpenDoor \/ CloseDoor \/ StartCooking \/ StopClock \/ Tick \/ ResetClock \/ AddTime

Spec == Init /\ [][Next]_vars

============================================================================= 