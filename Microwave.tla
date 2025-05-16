
(* Trace of states from execution *)
Trace ==
  /\ door = CLOSED
     /\ time = 0
     /\ radiation = OFF
     /\ power = OFF

  \/ /\ door = CLOSED
     /\ time = 0
     /\ radiation = OFF
     /\ power = ON

  \/ /\ door = OPEN
     /\ time = 0
     /\ radiation = OFF
     /\ power = ON

  \/ /\ door = CLOSED
     /\ time = 0
     /\ radiation = OFF
     /\ power = ON

  \/ /\ door = CLOSED
     /\ time = 3
     /\ radiation = OFF
     /\ power = ON

  \/ /\ door = CLOSED
     /\ time = 6
     /\ radiation = OFF
     /\ power = ON

  \/ /\ door = CLOSED
     /\ time = 6
     /\ radiation = ON
     /\ power = ON

  \/ /\ door = CLOSED
     /\ time = 5
     /\ radiation = ON
     /\ power = ON

  \/ /\ door = CLOSED
     /\ time = 4
     /\ radiation = ON
     /\ power = ON

  \/ /\ door = CLOSED
     /\ time = 3
     /\ radiation = ON
     /\ power = ON

  \/ /\ door = OPEN
     /\ time = 3
     /\ radiation = OFF
     /\ power = ON

====
