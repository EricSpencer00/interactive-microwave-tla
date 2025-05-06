----------------------------- MODULE MicrowaveTrullPaper -----------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS MaxTime \in Nat

VARIABLES door, power, timer, light, event

vars == <<door, power, timer, light, event>>

DoorStates == {"open", "closed"}
PowerStates == {"off", "low", "high"}
OnOff == {"on", "off"}
Events == {"OpenDoor", "CloseDoor", "SetPowerLow", "SetPowerHigh", "SetTimer", "Start", "Stop", "Tick"}

TypeOK ==
    /\ door \in DoorStates
    /\ power \in PowerStates
    /\ timer \in 0..MaxTime
    /\ light \in OnOff
    /\ event \in Events

Init ==
    /\ door = "closed"
    /\ power = "off"
    /\ timer = 0
    /\ light = "off"
    /\ event = "Stop"

OpenDoor ==
    /\ event = "OpenDoor"
    /\ door = "closed"
    /\ door' = "open"
    /\ light' = "on"
    /\ power' = power
    /\ timer' = timer
    /\ UNCHANGED <<event>>

CloseDoor ==
    /\ event = "CloseDoor"
    /\ door = "open"
    /\ door' = "closed"
    /\ light' = IF timer > 0 THEN "on" ELSE "off"
    /\ power' = power
    /\ timer' = timer
    /\ UNCHANGED <<event>>

SetPowerLow ==
    /\ event = "SetPowerLow"
    /\ power' = "low"
    /\ UNCHANGED <<door, timer, light, event>>

SetPowerHigh ==
    /\ event = "SetPowerHigh"
    /\ power' = "high"
    /\ UNCHANGED <<door, timer, light, event>>

SetTimer ==
    \E t \in 1..MaxTime:
      /\ event = "SetTimer"
      /\ timer' = t
      /\ UNCHANGED <<door, power, light, event>>

Start ==
    /\ event = "Start"
    /\ door = "closed"
    /\ timer > 0
    /\ power # "off"
    /\ light' = "on"
    /\ UNCHANGED <<door, power, timer, event>>

Stop ==
    /\ event = "Stop"
    /\ light' = IF timer > 0 THEN "on" ELSE "off"
    /\ UNCHANGED <<door, power, timer, event>>

Tick ==
    /\ event = "Tick"
    /\ timer > 0
    /\ timer' = timer - 1
    /\ IF timer' = 0 THEN <<light'>> = <<"off">> ELSE <<light'>> = <<light>>
    /\ UNCHANGED <<door, power, event>>

Next ==
    \/ OpenDoor
    \/ CloseDoor
    \/ SetPowerLow
    \/ SetPowerHigh
    \/ SetTimer
    \/ Start
    \/ Stop
    \/ Tick

Spec == Init /\ [][Next]_vars

(* Safety: Microwave never runs with door open *)
Safety == door = "open" => light = "off"

(* Liveness: If started, eventually stops *)
Liveness == (<>((timer > 0) /\ light = "on")) => (<>(timer = 0 \/ door = "open"))

============================================================================= 