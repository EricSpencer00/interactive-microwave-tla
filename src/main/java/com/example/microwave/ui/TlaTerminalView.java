package com.example.microwave.ui;

import com.vaadin.flow.component.button.Button;
import com.vaadin.flow.component.textfield.TextArea;
import com.vaadin.flow.component.orderedlayout.VerticalLayout;
import com.example.microwave.service.TlaSpecService;

public class TlaTerminalView extends VerticalLayout {
    
    private final TlaSpecService tlaSpecService;
    
    public TlaTerminalView(TlaSpecService tlaSpecService) {
        this.tlaSpecService = tlaSpecService;
        
        TextArea tlaInput = new TextArea("TLA+ Spec");
        tlaInput.setWidth("800px");
        tlaInput.setHeight("300px");
        tlaInput.setValue(loadDefaultSpec());
        
        TextArea cfgInput = new TextArea("Config File");
        cfgInput.setWidth("800px");
        cfgInput.setHeight("150px");
        cfgInput.setValue(loadDefaultCfg());
        
        TextArea result = new TextArea("TLC Output");
        result.setWidth("800px");
        result.setHeight("250px");
        result.setReadOnly(true);
        
        Button runChecker = new Button("Run TLC", e -> {
            String output = tlaSpecService.runTLC(tlaInput.getValue(), cfgInput.getValue());
            result.setValue(output);
        });
        
        add(tlaInput, cfgInput, runChecker, result);
    }
    
    private String loadDefaultSpec() {
        return "-------------------------- MODULE MicrowaveSpec  --------------------------\n" +
               "\n" +
               "EXTENDS TLC, Integers\n" +
               "\n" +
               "CONSTANTS\n" +
               "  \\* Flag for enabling safety check upon starting radiation\n" +
               "  ImplementStartSafety,\n" +
               "  \\* Flag for enabling safety check upon opening door\n" +
               "  ImplementOpenDoorSafety\n" +
               "\n" +
               "VARIABLES\n" +
               "  \\* See TypeOK below for type constraints\n" +
               "  door,\n" +
               "  radiation,\n" +
               "  timeRemaining\n" +
               "\n" +
               "\\* Tuple of all variables\n" +
               "vars == << door, radiation, timeRemaining >>\n" +
               "\n" +
               "\\* Symbolic names for significant strings\n" +
               "OFF == \"off\"\n" +
               "ON == \"on\"\n" +
               "CLOSED == \"closed\"\n" +
               "OPEN == \"open\"\n" +
               "\n" +
               "\\* Dynamic type invariant\n" +
               "TypeOK == \n" +
               "  /\\ door \\in { CLOSED, OPEN }\n" +
               "  /\\ radiation \\in { OFF, ON }\n" +
               "  /\\ timeRemaining \\in Nat\n" +
               "\n" +
               "MaxTime == 60\n" +
               "\n" +
               "\\* Valid initial state(s)\n" +
               "Init ==\n" +
               "  /\\ door \\in { OPEN, CLOSED }\n" +
               "  /\\ radiation = OFF\n" +
               "  /\\ timeRemaining = 0\n" +
               "\n" +
               "\\* Increment remaining time by one second\n" +
               "IncTime ==\n" +
               "  /\\ radiation = OFF\n" +
               "  /\\ timeRemaining' = timeRemaining + 1\n" +
               "  /\\ timeRemaining' <= MaxTime\n" +
               "  /\\ UNCHANGED << door, radiation >>\n" +
               "\n" +
               "\\* Start radiation and time countdown\n" +
               "Start ==\n" +
               "  /\\ radiation = OFF\n" +
               "  /\\ ImplementStartSafety => door = CLOSED\n" +
               "  /\\ timeRemaining > 0\n" +
               "  /\\ radiation' = ON\n" +
               "  /\\ UNCHANGED << door, timeRemaining >>\n" +
               "\n" +
               "\\* Cancel radiation and reset remaining time\n" +
               "Cancel ==\n" +
               "  /\\ radiation' = OFF\n" +
               "  /\\ timeRemaining' = 0\n" +
               "  /\\ UNCHANGED << door >>\n" +
               "\n" +
               "\\* Internal clock tick for time countdown\n" +
               "Tick ==\n" +
               "  /\\ radiation = ON\n" +
               "  /\\ timeRemaining' = timeRemaining - 1\n" +
               "  /\\ timeRemaining' >= 0\n" +
               "  /\\ IF timeRemaining' = 0\n" +
               "     THEN radiation' = OFF\n" +
               "     ELSE UNCHANGED << radiation >>\n" +
               "  /\\ UNCHANGED << door >>\n" +
               "\n" +
               "\\* Open door\n" +
               "OpenDoor ==\n" +
               "  /\\ door' = OPEN\n" +
               "  /\\ IF ImplementOpenDoorSafety\n" +
               "     THEN radiation' = OFF\n" +
               "     ELSE UNCHANGED << radiation >>\n" +
               "  /\\ UNCHANGED << timeRemaining >>\n" +
               "\n" +
               "\\* Close door\n" +
               "CloseDoor ==\n" +
               "  /\\ door' = CLOSED\n" +
               "  /\\ UNCHANGED << radiation, timeRemaining >>\n" +
               "\n" +
               "\\* All valid actions (state transitions)\n" +
               "Next ==\n" +
               "  \\/ IncTime\n" +
               "  \\/ Start\n" +
               "  \\/ Cancel\n" +
               "  \\/ OpenDoor\n" +
               "  \\/ CloseDoor\n" +
               "  \\/ Tick\n" +
               "\n" +
               "\\* All valid system behaviors starting from the initial state\n" +
               "Spec == Init /\\ [][Next]_vars\n" +
               "\n" +
               "\\* Valid system behaviors with weak fairness to disallow stuttering\n" +
               "FSpec == Spec /\\ WF_vars(Tick)\n" +
               "\n" +
               "\\* Safety check to detect radiation with door open\n" +
               "DoorSafety == door = OPEN => radiation = OFF\n" +
               "\n" +
               "\\* Temporal check to detect indefinite radiation\n" +
               "HeatLiveness == radiation = ON ~> radiation = OFF\n" +
               "\n" +
               "RunsUntilDoneOrInterrupted == \n" +
               "  [][radiation = ON => radiation' = ON \\/ timeRemaining' = 0 \\/ door' = OPEN]_vars\n" +
               "\n" +
               "====\n" +
               "\n" +
               "(* other possible events\n" +
               "    action := \"10min\"\n" +
               "    action := \"1min\"\n" +
               "    action := \"10sec\"\n" +
               "    action := \"power\"\n" +
               "    action := \"timer\"\n" +
               "*)\n" +
               "\n" +
               "\\* DoorSafety == RequireSafety => radiation = ON => door = CLOSED";
    }

    private String loadDefaultCfg() {
        return "CONSTANTS\n" +
               "  ImplementStartSafety = FALSE\n" +
               "  ImplementOpenDoorSafety = FALSE\n" +
               "\n" +
               "SPECIFICATION \n" +
               "  Spec\n" +
               "  \\* FSpec\n" +
               "\n" +
               "INVARIANTS \n" +
               "  TypeOK\n" +
               "  \\* DoorSafety\n" +
               "\n" +
               "PROPERTIES \n" +
               "  \\* HeatLiveness\n" +
               "  \\* RunsUntilDoneOrInterrupted\n";
    }
    
    
}
