---- MODULE Microwave ----
EXTENDS Integers, TLC

VARIABLES door, time, radiation, power

Init ==
/\ door = "CLOSED"
/\ time = 0
/\ radiation = "OFF"
/\ power = "OFF"

TogglePower ==
/\ UNCHANGED <<door, time, radiation>>
/\ power' = IF power = "ON" THEN "OFF" ELSE "ON"

IncrementTime ==
/\ UNCHANGED <<door, radiation, power>>
/\ time' = time + 3

Start ==
/\ time > 0
/\ radiation' = "ON"
/\ UNCHANGED <<door, time, power>>

Tick ==
/\ time > 0
/\ time' = time - 1
/\ UNCHANGED <<door, power>>
/\ radiation' = IF time' = 0 THEN "OFF" ELSE radiation

Cancel ==
/\ time' = 0
/\ radiation' = "OFF"
/\ UNCHANGED <<door, power>>

Next ==
TogglePower \/ IncrementTime \/ Start \/ Tick \/ Cancel

Safe == ~(radiation = "ON" /\ door = "OPEN")

Spec == Init /\ [][Next]_<<door,time,radiation,power>>

THEOREM Spec => []Safe 