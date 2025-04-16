package com.example.microwave.ui;

import com.example.microwave.fsm.MicrowaveFSM;
import com.example.microwave.service.TlaSpecService;
import com.vaadin.flow.component.button.Button;
import com.vaadin.flow.component.textfield.NumberField;
import com.vaadin.flow.component.orderedlayout.VerticalLayout;
import com.vaadin.flow.component.html.Span;

public class MicrowaveControlView extends VerticalLayout {
    
    private MicrowaveFSM microwaveFSM;
    private TlaSpecService tlaSpecService;
    
    private Span stateDisplay;
    private Span timerDisplay;
    private Span lightDisplay;
    private Span radiationDisplay;
    private Span messageDisplay;
    private Span tlaValidationDisplay;
    
    public MicrowaveControlView(TlaSpecService tlaSpecService) {
        this.tlaSpecService = tlaSpecService;
        microwaveFSM = new MicrowaveFSM();
        
        stateDisplay = new Span("State: " + microwaveFSM.getState());
        timerDisplay = new Span("Timer: " + microwaveFSM.getTimer() + " sec");
        lightDisplay = new Span("Light: " + (microwaveFSM.isLightOn() ? "On" : "Off"));
        radiationDisplay = new Span("Radiation: " + (microwaveFSM.isRadiationOn() ? "On" : "Off"));
        messageDisplay = new Span("");
        tlaValidationDisplay = new Span("TLA Check: (waiting...)");
        
        // Create buttons; note that the associated TLA action name is passed to the validator.
        Button toggleDoorButton = new Button("Toggle Door", e -> {
            String tlaAction;
            if (microwaveFSM.getState() == MicrowaveFSM.State.DOOR_OPEN) {
                // Attempt to close the door; assume action name is CloseDoor.
                tlaAction = "CloseDoor";
                String msg = microwaveFSM.closeDoor();
                messageDisplay.setText(msg);
            } else {
                // Attempt to open the door; action name: OpenDoor.
                tlaAction = "OpenDoor";
                String msg = microwaveFSM.openDoor();
                messageDisplay.setText(msg);
            }
            // Validate the attempted transition with TLC.
            String tlaOutput = tlaSpecService.validateTransition(tlaAction, microwaveFSM);
            tlaValidationDisplay.setText("TLA Check:\n" + tlaOutput);
            updateDisplays();
        });
        
        Button startCookingButton = new Button("Start Cooking", e -> {
            String tlaAction = "Start";
            String msg = microwaveFSM.startCooking();
            messageDisplay.setText(msg);
            String tlaOutput = tlaSpecService.validateTransition(tlaAction, microwaveFSM);
            tlaValidationDisplay.setText("TLA Check:\n" + tlaOutput);
            updateDisplays();
        });
        
        Button addTimeButton = new Button("Add 3 sec", e -> {
            String tlaAction = "IncTime";  // For this simple integration we assume add time uses IncTime.
            String msg = microwaveFSM.addTime(3);
            messageDisplay.setText(msg);
            String tlaOutput = tlaSpecService.validateTransition(tlaAction, microwaveFSM);
            tlaValidationDisplay.setText("TLA Check:\n" + tlaOutput);
            updateDisplays();
        });
        
        NumberField customTimeField = new NumberField("Add Custom Time (sec)");
        customTimeField.setPlaceholder("Enter seconds");
        Button addCustomTimeButton = new Button("Add Custom Time", e -> {
            Double val = customTimeField.getValue();
            if (val != null) {
                String tlaAction = "IncTime";
                String msg = microwaveFSM.addTime(val.intValue());
                messageDisplay.setText(msg);
                String tlaOutput = tlaSpecService.validateTransition(tlaAction, microwaveFSM);
                tlaValidationDisplay.setText("TLA Check:\n" + tlaOutput);
                updateDisplays();
            } else {
                messageDisplay.setText("Please enter a valid time.");
            }
        });
        
        Button stopClockButton = new Button("Stop Clock", e -> {
            // Here we assume stopping the clock corresponds to a Cancel action.
            String tlaAction = "Cancel";
            String msg = microwaveFSM.stopClock();
            messageDisplay.setText(msg);
            String tlaOutput = tlaSpecService.validateTransition(tlaAction, microwaveFSM);
            tlaValidationDisplay.setText("TLA Check:\n" + tlaOutput);
            updateDisplays();
        });
        
        Button resetClockButton = new Button("Reset Clock", e -> {
            // Reset could be considered Cancel as well.
            String tlaAction = "Cancel";
            String msg = microwaveFSM.resetClock();
            messageDisplay.setText(msg);
            String tlaOutput = tlaSpecService.validateTransition(tlaAction, microwaveFSM);
            tlaValidationDisplay.setText("TLA Check:\n" + tlaOutput);
            updateDisplays();
        });
        
        Button tickButton = new Button("Tick", e -> {
            // Tick represents a time decrement.
            String tlaAction = "Tick";
            String msg = microwaveFSM.tick();
            messageDisplay.setText(msg);
            String tlaOutput = tlaSpecService.validateTransition(tlaAction, microwaveFSM);
            tlaValidationDisplay.setText("TLA Check:\n" + tlaOutput);
            updateDisplays();
        });
        
        add(stateDisplay, timerDisplay, lightDisplay, radiationDisplay, messageDisplay, tlaValidationDisplay,
            toggleDoorButton, startCookingButton, addTimeButton, customTimeField, addCustomTimeButton,
            stopClockButton, resetClockButton, tickButton);
        
        updateDisplays();
    }
    
    private void updateDisplays() {
        stateDisplay.setText("State: " + microwaveFSM.getState());
        timerDisplay.setText("Timer: " + microwaveFSM.getTimer() + " sec");
        lightDisplay.setText("Light: " + (microwaveFSM.isLightOn() ? "On" : "Off"));
        radiationDisplay.setText("Radiation: " + (microwaveFSM.isRadiationOn() ? "On" : "Off"));
    }
}
