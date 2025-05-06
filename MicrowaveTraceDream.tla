----------------------------- MODULE MicrowaveTraceDream -----------------------------
EXTENDS MicrowaveSpecDream, Sequences

CONSTANTS MaxTime

(* Example trace: Each element is <<door, timer, radiation, light>> *)
Trace == <<
  <<"closed", 10, "off", "off">>,
  <<"closed", 10, "on", "on">>,
  <<"closed", 9, "on", "on">>,
  <<"open", 9, "off", "on">>,
  <<"open", 9, "off", "on">>,
  <<"closed", 9, "off", "on">>,
  <<"closed", 8, "on", "on">>,
  <<"closed", 0, "off", "off">>
>>

VARIABLES door, timer, radiation, light, i

vars == <<door, timer, radiation, light>>

(* Read the i-th record from the trace *)
Read ==
  LET rec == Trace[i] IN
    /\ door = rec[1]
    /\ timer = rec[2]
    /\ radiation = rec[3]
    /\ light = rec[4]

ReadNext ==
  LET rec == Trace[i'] IN
    /\ door' = rec[1]
    /\ timer' = rec[2]
    /\ radiation' = rec[3]
    /\ light' = rec[4]

InitTrace ==
  /\ i = 1
  /\ Read

NextTrace ==
  /\ i < Len(Trace)
  /\ i' = i + 1
  /\ ReadNext

TraceBehavior == InitTrace /\ [][NextTrace]_<<i, door, timer, radiation, light>>

(* Compose with the original spec as in the paper *)
Compose(NextA, varsA, NextB, varsB) ==
  \/ NextA /\ NextB
  \/ UNCHANGED varsA /\ NextB
  \/ UNCHANGED varsB /\ NextA

ComposedSpec ==
  /\ Init
  /\ InitTrace
  /\ [][Compose(Next, vars, NextTrace, <<i>>)]_<<door, timer, radiation, light, i>>

TraceFinished == i >= Len(Trace)

============================================================================= 