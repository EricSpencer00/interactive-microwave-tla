----------------------------- MODULE MicrowaveSpecDream -----------------------------
EXTENDS Naturals, TLC

CONSTANTS MaxTime \in Nat

VARIABLES door, timer, radiation, light

vars == <<door, timer, radiation, light>>

(* Door can be "open" or "closed" *)
DoorStates == {"open", "closed"}
(* Radiation and light can be "on" or "off" *)
OnOff == {"on", "off"}

TypeOK == 
    /\ door \in DoorStates
    /\ timer \in 0..MaxTime
    /\ radiation \in OnOff
    /\ light \in OnOff

Init ==
    /\ door = "closed"
    /\ timer = 0
    /\ radiation = "off"
    /\ light = "off"

OpenDoor ==
    /\ door = "closed"
    /\ door' = "open"
    /\ radiation' = "off"
    /\ light' = "on"
    /\ UNCHANGED timer

CloseDoor ==
    /\ door = "open"
    /\ door' = "closed"
    /\ light' = IF timer > 0 THEN "on" ELSE "off"
    /\ UNCHANGED <<timer, radiation>>

Start ==
    /\ door = "closed"
    /\ timer > 0
    /\ radiation = "off"
    /\ radiation' = "on"
    /\ light' = "on"
    /\ UNCHANGED <<door, timer>>

Stop ==
    /\ radiation = "on"
    /\ radiation' = "off"
    /\ light' = IF timer > 0 THEN "on" ELSE "off"
    /\ UNCHANGED <<door, timer>>

AddTime ==
    \E t \in 1..MaxTime:
      /\ timer + t <= MaxTime
      /\ timer' = timer + t
      /\ UNCHANGED <<door, radiation, light>>

Tick ==
    /\ timer > 0
    /\ timer' = timer - 1
    /\ IF timer' = 0 THEN <<radiation', light'>> = <<"off", "off">> ELSE <<radiation', light'>> = <<radiation, light>>
    /\ UNCHANGED door

Reset ==
    /\ timer > 0
    /\ timer' = 0
    /\ radiation' = "off"
    /\ light' = "off"
    /\ UNCHANGED door

Next ==
    \/ OpenDoor
    \/ CloseDoor
    \/ Start
    \/ Stop
    \/ AddTime
    \/ Tick
    \/ Reset

Spec == Init /\ [][Next]_vars

(* Safety: Radiation is never on when door is open *)
Safety == door = "open" => radiation = "off"

(* Liveness: If started, eventually timer reaches 0 or door is opened *)
Liveness == (<>((timer > 0) /\ radiation = "on")) => (<>(timer = 0 \/ door = "open"))

============================================================================= 