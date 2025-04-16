package com.example.microwave.ui;

import com.example.microwave.fsm.MicrowaveFSM;
import com.vaadin.flow.component.button.Button;
import com.vaadin.flow.component.textfield.NumberField;
import com.vaadin.flow.component.orderedlayout.VerticalLayout;
import com.vaadin.flow.component.html.Span;

public class MicrowaveControlView extends VerticalLayout {
    
    private MicrowaveFSM microwaveFSM;
    
    private Span stateDisplay;
    private Span timerDisplay;
    private Span lightDisplay;
    private Span radiationDisplay;
    private Span messageDisplay;
    
    public MicrowaveControlView() {
        microwaveFSM = new MicrowaveFSM();
        
        stateDisplay = new Span("State: " + microwaveFSM.getState());
        timerDisplay = new Span("Timer: " + microwaveFSM.getTimer() + " sec");
        lightDisplay = new Span("Light: " + (microwaveFSM.isLightOn() ? "On" : "Off"));
        radiationDisplay = new Span("Radiation: " + (microwaveFSM.isRadiationOn() ? "On" : "Off"));
        messageDisplay = new Span("");
        
        // Controls for microwave actions.
        Button toggleDoorButton = new Button("Toggle Door", e -> toggleDoor());
        Button startCookingButton = new Button("Start Cooking", e -> startCooking());
        Button addTimeButton = new Button("Add 3 sec", e -> addTime(3));
        NumberField customTimeField = new NumberField("Add Custom Time (sec)");
        customTimeField.setPlaceholder("Enter seconds");
        Button addCustomTimeButton = new Button("Add Custom Time", e -> {
            Double val = customTimeField.getValue();
            if (val != null) {
                addTime(val.intValue());
            } else {
                messageDisplay.setText("Please enter a valid time.");
            }
        });
        Button stopClockButton = new Button("Stop Clock", e -> stopClock());
        Button resetClockButton = new Button("Reset Clock", e -> resetClock());
        Button tickButton = new Button("Tick", e -> tick());
        
        add(stateDisplay, timerDisplay, lightDisplay, radiationDisplay, messageDisplay,
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
    
    private void toggleDoor() {
        String msg;
        if (microwaveFSM.getState() == MicrowaveFSM.State.DOOR_OPEN) {
            msg = microwaveFSM.closeDoor();
        } else {
            msg = microwaveFSM.openDoor();
        }
        messageDisplay.setText(msg);
        updateDisplays();
    }
    
    private void addTime(int seconds) {
        String msg = microwaveFSM.addTime(seconds);
        messageDisplay.setText(msg);
        updateDisplays();
    }
    
    private void startCooking() {
        String msg = microwaveFSM.startCooking();
        messageDisplay.setText(msg);
        updateDisplays();
    }
    
    private void stopClock() {
        String msg = microwaveFSM.stopClock();
        messageDisplay.setText(msg);
        updateDisplays();
    }
    
    private void resetClock() {
        String msg = microwaveFSM.resetClock();
        messageDisplay.setText(msg);
        updateDisplays();
    }
    
    private void tick() {
        String msg = microwaveFSM.tick();
        messageDisplay.setText(msg);
        updateDisplays();
    }
}
