package com.example.microwave.ui;

import com.example.microwave.fsm.MicrowaveFSM;
import com.example.microwave.service.TlaSpecService;
import com.vaadin.flow.component.button.Button;
import com.vaadin.flow.component.html.Div;
import com.vaadin.flow.component.html.Span;
import com.vaadin.flow.component.orderedlayout.VerticalLayout;

public class MicrowaveControlView extends VerticalLayout {
    
    private MicrowaveFSM microwaveFSM;
    private TlaSpecService tlaSpecService;
    
    private Span stateDisplay;
    private Span timerDisplay;
    private Span lightDisplay;
    private Span radiationDisplay;
    private Span messageDisplay;
    private Span tlaValidationDisplay;
    
    private Div microwaveDiv;
    private Div doorDiv;
    private Div handleDiv;
    private Div displayDiv;
    private Div lightDiv;
    private Div cookingDiv;
    private Div controlsDiv;
    private Span timerLabel;
    
    public MicrowaveControlView(TlaSpecService tlaSpecService) {
        this.tlaSpecService = tlaSpecService;
        microwaveFSM = new MicrowaveFSM();
        
        stateDisplay = new Span("State: " + microwaveFSM.getState());
        timerDisplay = new Span("Timer: " + microwaveFSM.getTimer() + " sec");
        lightDisplay = new Span("Light: " + (microwaveFSM.isLightOn() ? "On" : "Off"));
        radiationDisplay = new Span("Radiation: " + (microwaveFSM.isRadiationOn() ? "On" : "Off"));
        messageDisplay = new Span("");
        tlaValidationDisplay = new Span("TLA Check: (waiting...)");
        
        // --- Microwave Visual Structure ---
        microwaveDiv = new Div();
        microwaveDiv.addClassName("microwave");
        microwaveDiv.getStyle().set("position", "relative");
        microwaveDiv.getStyle().set("width", "400px");
        microwaveDiv.getStyle().set("height", "220px");
        microwaveDiv.getStyle().set("background", "#f0f0f0");
        microwaveDiv.getStyle().set("border", "2px solid #ccc");
        microwaveDiv.getStyle().set("border-radius", "10px");
        microwaveDiv.getStyle().set("margin", "50px auto");
        microwaveDiv.getStyle().set("display", "flex");
        microwaveDiv.getStyle().set("flex-direction", "row");
        microwaveDiv.getStyle().set("box-shadow", "2px 2px 10px #bbb");

        // Door
        doorDiv = new Div();
        doorDiv.addClassName("microwave-door");
        doorDiv.getStyle().set("width", "220px");
        doorDiv.getStyle().set("height", "180px");
        doorDiv.getStyle().set("background", "#e0e0e0");
        doorDiv.getStyle().set("border", "2px solid #aaa");
        doorDiv.getStyle().set("border-radius", "6px");
        doorDiv.getStyle().set("margin", "20px 0 0 20px");
        doorDiv.getStyle().set("position", "relative");
        doorDiv.getStyle().set("transition", "transform 0.4s");

        // Door handle (clickable)
        handleDiv = new Div();
        handleDiv.addClassName("microwave-handle");
        handleDiv.getStyle().set("width", "16px");
        handleDiv.getStyle().set("height", "60px");
        handleDiv.getStyle().set("background", "#bbb");
        handleDiv.getStyle().set("border-radius", "8px");
        handleDiv.getStyle().set("position", "absolute");
        handleDiv.getStyle().set("right", "-18px");
        handleDiv.getStyle().set("top", "60px");
        handleDiv.getStyle().set("cursor", "pointer");
        handleDiv.getStyle().set("box-shadow", "1px 1px 4px #888");
        handleDiv.addClickListener(e -> {
            String tlaAction;
            if (microwaveFSM.getState() == MicrowaveFSM.State.DOOR_OPEN) {
                tlaAction = "CloseDoor";
                String msg = microwaveFSM.closeDoor();
                messageDisplay.setText(msg);
            } else {
                tlaAction = "OpenDoor";
                String msg = microwaveFSM.openDoor();
                messageDisplay.setText(msg);
            }
            String tlaOutput = tlaSpecService.validateTransition(tlaAction, microwaveFSM);
            tlaValidationDisplay.setText("TLA Check:\n" + tlaOutput);
            updateDisplays();
        });
        doorDiv.add(handleDiv);

        // Display (timer)
        displayDiv = new Div();
        displayDiv.addClassName("microwave-display");
        displayDiv.getStyle().set("width", "80px");
        displayDiv.getStyle().set("height", "40px");
        displayDiv.getStyle().set("background", "#222");
        displayDiv.getStyle().set("color", "#0f0");
        displayDiv.getStyle().set("font-family", "monospace");
        displayDiv.getStyle().set("font-size", "2em");
        displayDiv.getStyle().set("display", "flex");
        displayDiv.getStyle().set("align-items", "center");
        displayDiv.getStyle().set("justify-content", "center");
        displayDiv.getStyle().set("position", "absolute");
        displayDiv.getStyle().set("top", "20px");
        displayDiv.getStyle().set("left", "60px");
        timerLabel = new Span();
        displayDiv.add(timerLabel);
        doorDiv.add(displayDiv);

        // Light indicator
        lightDiv = new Div();
        lightDiv.addClassName("microwave-light");
        lightDiv.getStyle().set("width", "20px");
        lightDiv.getStyle().set("height", "20px");
        lightDiv.getStyle().set("border-radius", "50%");
        lightDiv.getStyle().set("position", "absolute");
        lightDiv.getStyle().set("bottom", "20px");
        lightDiv.getStyle().set("left", "30px");
        doorDiv.add(lightDiv);

        // Cooking (radiation) indicator
        cookingDiv = new Div();
        cookingDiv.addClassName("microwave-cooking");
        cookingDiv.getStyle().set("width", "20px");
        cookingDiv.getStyle().set("height", "20px");
        cookingDiv.getStyle().set("border-radius", "50%");
        cookingDiv.getStyle().set("position", "absolute");
        cookingDiv.getStyle().set("bottom", "20px");
        cookingDiv.getStyle().set("right", "30px");
        doorDiv.add(cookingDiv);

        // --- Controls Panel ---
        controlsDiv = new Div();
        controlsDiv.addClassName("microwave-controls");
        controlsDiv.getStyle().set("width", "120px");
        controlsDiv.getStyle().set("height", "180px");
        controlsDiv.getStyle().set("background", "#d0d0d0");
        controlsDiv.getStyle().set("border", "1px solid #999");
        controlsDiv.getStyle().set("border-radius", "6px");
        controlsDiv.getStyle().set("margin", "20px 0 0 20px");
        controlsDiv.getStyle().set("display", "flex");
        controlsDiv.getStyle().set("flex-direction", "column");
        controlsDiv.getStyle().set("align-items", "center");
        controlsDiv.getStyle().set("justify-content", "space-around");
        controlsDiv.getStyle().set("padding", "10px 0");

        // --- Controls (Buttons/Knobs) ---
        Button startCookingButton = new Button("Start");
        startCookingButton.addClickListener(e -> {
            String tlaAction = "Start";
            String msg = microwaveFSM.startCooking();
            messageDisplay.setText(msg);
            String tlaOutput = tlaSpecService.validateTransition(tlaAction, microwaveFSM);
            tlaValidationDisplay.setText("TLA Check:\n" + tlaOutput);
            updateDisplays();
        });
        Button addTimeButton = new Button("+10s");
        addTimeButton.addClickListener(e -> {
            String tlaAction = "IncTime";
            String msg = microwaveFSM.addTime(10);
            messageDisplay.setText(msg);
            String tlaOutput = tlaSpecService.validateTransition(tlaAction, microwaveFSM);
            tlaValidationDisplay.setText("TLA Check:\n" + tlaOutput);
            updateDisplays();
        });
        Button stopClockButton = new Button("Stop");
        stopClockButton.addClickListener(e -> {
            String tlaAction = "Pause";
            String msg = microwaveFSM.stopClock();
            messageDisplay.setText(msg);
            String tlaOutput = tlaSpecService.validateTransition(tlaAction, microwaveFSM);
            tlaValidationDisplay.setText("TLA Check:\n" + tlaOutput);
            updateDisplays();
        });
        Button tickButton = new Button("Tick");
        tickButton.addClickListener(e -> {
            String tlaAction = "Tick";
            String msg = microwaveFSM.tick();
            messageDisplay.setText(msg);
            String tlaOutput = tlaSpecService.validateTransition(tlaAction, microwaveFSM);
            tlaValidationDisplay.setText("TLA Check:\n" + tlaOutput);
            updateDisplays();
        });
        controlsDiv.add(startCookingButton, addTimeButton, stopClockButton, tickButton);

        // --- Assemble Microwave ---
        microwaveDiv.add(doorDiv, controlsDiv);
        add(microwaveDiv, tlaValidationDisplay, messageDisplay);
        updateDisplays();
    }
    
    private void updateDisplays() {
        // Door open/close visual
        if (microwaveFSM.getState() == MicrowaveFSM.State.DOOR_OPEN) {
            doorDiv.getStyle().set("transform", "rotateY(-60deg)");
        } else {
            doorDiv.getStyle().set("transform", "rotateY(0deg)");
        }
        // Timer display
        timerLabel.setText(String.format("%02d:%02d", microwaveFSM.getTimer() / 60, microwaveFSM.getTimer() % 60));
        // Light indicator
        if (microwaveFSM.isLightOn()) {
            lightDiv.getStyle().set("background", "#ff0");
            lightDiv.getStyle().set("box-shadow", "0 0 10px 4px #ff0");
        } else {
            lightDiv.getStyle().set("background", "#888");
            lightDiv.getStyle().set("box-shadow", "none");
        }
        // Cooking (radiation) indicator
        if (microwaveFSM.isRadiationOn()) {
            cookingDiv.getStyle().set("background", "#f33");
            cookingDiv.getStyle().set("box-shadow", "0 0 10px 4px #f33");
        } else {
            cookingDiv.getStyle().set("background", "#888");
            cookingDiv.getStyle().set("box-shadow", "none");
        }
    }
}
