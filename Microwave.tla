
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

  \/ /\ door = OPEN
     /\ time = 0
     /\ radiation = ON
     /\ power = ON

  \/ /\ door = OPEN
     /\ time = 0
     /\ radiation = ON
     /\ power = ON

  \/ /\ door = OPEN
     /\ time = 0
     /\ radiation = ON
     /\ power = ON

  \/ /\ door = OPEN
     /\ time = 0
     /\ radiation = ON
     /\ power = ON

  \/ /\ door = CLOSED
     /\ time = 0
     /\ radiation = ON
     /\ power = ON

  \/ /\ door = CLOSED
     /\ time = 0
     /\ radiation = ON
     /\ power = ON

  \/ /\ door = OPEN
     /\ time = 0
     /\ radiation = ON
     /\ power = ON

  \/ /\ door = CLOSED
     /\ time = 0
     /\ radiation = ON
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
     /\ time = 9
     /\ radiation = OFF
     /\ power = ON

  \/ /\ door = CLOSED
     /\ time = 12
     /\ radiation = OFF
     /\ power = ON

  \/ /\ door = OPEN
     /\ time = 12
     /\ radiation = OFF
     /\ power = ON

  \/ /\ door = OPEN
     /\ time = 12
     /\ radiation = ON
     /\ power = ON

  \/ /\ door = OPEN
     /\ time = 11
     /\ radiation = ON
     /\ power = ON

  \/ /\ door = OPEN
     /\ time = 10
     /\ radiation = ON
     /\ power = ON

  \/ /\ door = OPEN
     /\ time = 9
     /\ radiation = ON
     /\ power = ON

  \/ /\ door = OPEN
     /\ time = 8
     /\ radiation = ON
     /\ power = ON

  \/ /\ door = OPEN
     /\ time = 7
     /\ radiation = ON
     /\ power = ON

  \/ /\ door = OPEN
     /\ time = 6
     /\ radiation = ON
     /\ power = ON

  \/ /\ door = OPEN
     /\ time = 5
     /\ radiation = ON
     /\ power = ON

  \/ /\ door = OPEN
     /\ time = 4
     /\ radiation = ON
     /\ power = ON

  \/ /\ door = OPEN
     /\ time = 3
     /\ radiation = ON
     /\ power = ON

  \/ /\ door = OPEN
     /\ time = 2
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

  \/ /\ door = OPEN
     /\ time = 0
     /\ radiation = OFF
     /\ power = ON

====
