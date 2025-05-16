---- MODULE Microwave ----
EXTENDS Integers, TLC

VARIABLES door, time, radiation, power

CONSTANTS OPEN, CLOSED, ON, OFF

Init ==
/\ door = CLOSED
/\ time = 0
/\ radiation = OFF
/\ power = OFF

TogglePower ==
/\ UNCHANGED <<door, time, radiation>>
/\ power' = IF power = ON THEN OFF ELSE ON

IncrementTime ==
/\ UNCHANGED <<door, radiation, power>>
/\ time' = time + 3

Start ==
/\ time > 0
/\ door = CLOSED
/\ power = ON
/\ radiation' = ON
/\ UNCHANGED <<door, time, power>>

Tick ==
/\ time > 0
/\ time' = time - 1
/\ UNCHANGED <<door, power>>
/\ radiation' = IF time' = 0 THEN OFF ELSE radiation

Cancel ==
/\ time' = 0
/\ radiation' = OFF
/\ UNCHANGED <<door, power>>

CloseDoor ==
/\ door = OPEN
/\ door' = CLOSED
/\ UNCHANGED <<time, radiation, power>>

OpenDoor ==
/\ door = CLOSED
/\ door' = OPEN
/\ radiation' = OFF
/\ UNCHANGED <<time, power>>

Next == TogglePower \/ IncrementTime \/ Start \/ Tick \/ Cancel \/ CloseDoor \/ OpenDoor

Safe == ~(radiation = ON /\ door = OPEN)

Spec == Init /\ [][Next]_<<door,time,radiation,power>>

(* Trace of states from execution - last 20 states only *)
Trace ==
  /\ door = CLOSED
     /\ time = 0
     /\ radiation = OFF
     /\ power = OFF

  \/ /\ door = CLOSED
     /\ time = 0
     /\ radiation = OFF
     /\ power = ON

  \/ /\ door = CLOSED
     /\ time = 3
     /\ radiation = OFF
     /\ power = ON

  \/ /\ door = CLOSED
     /\ time = 3
     /\ radiation = ON
     /\ power = ON

  \/ /\ door = CLOSED
     /\ time = 2
     /\ radiation = ON
     /\ power = ON

  \/ /\ door = CLOSED
     /\ time = 1
     /\ radiation = ON
     /\ power = ON

  \/ /\ door = CLOSED
     /\ time = 0
     /\ radiation = OFF
     /\ power = ON

====
