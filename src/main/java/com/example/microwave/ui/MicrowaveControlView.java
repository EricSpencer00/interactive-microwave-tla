package com.example.microwave.ui;

import com.example.microwave.fsm.MicrowaveFSM;
import com.example.microwave.service.TlaSpecService;
import com.vaadin.flow.component.button.Button;
import com.vaadin.flow.component.html.Div;
import com.vaadin.flow.component.html.Span;
import com.vaadin.flow.component.orderedlayout.FlexComponent.Alignment;
import com.vaadin.flow.component.orderedlayout.FlexComponent.JustifyContentMode;
import com.vaadin.flow.component.orderedlayout.HorizontalLayout;

public class MicrowaveControlView extends HorizontalLayout {
    private final MicrowaveFSM microwaveFSM;
    private final TlaSpecService tlaSpecService;

    private final Div microwaveDiv;
    private final Div doorDiv = new Div();
    private final Div controlsDiv;
    private final Span messageDisplay;
    private final Span tlaValidationDisplay;

    public MicrowaveControlView(TlaSpecService tlaSpecService) {
        this.tlaSpecService = tlaSpecService;
        this.microwaveFSM = new MicrowaveFSM();

        setWidthFull();
        setAlignItems(Alignment.CENTER);
        setJustifyContentMode(JustifyContentMode.CENTER);

        // Left: graphical microwave
        microwaveDiv = buildMicrowaveGraphic();

        // Right: controls and status
        controlsDiv = new Div();
        controlsDiv.getStyle().set("display", "flex");
        controlsDiv.getStyle().set("flexDirection", "column");
        controlsDiv.getStyle().set("padding", "1rem");
        controlsDiv.getStyle().set("gap", "0.5rem");

        Button openCloseBtn = new Button("Toggle Door", e -> handleAction(
            microwaveFSM.getState() == MicrowaveFSM.State.DOOR_OPEN ? "CloseDoor" : "OpenDoor",
            microwaveFSM.getState() == MicrowaveFSM.State.DOOR_OPEN ? microwaveFSM.closeDoor() : microwaveFSM.openDoor()
        ));
        Button add10Btn = new Button("+10s", e -> handleAction(
            "IncTime", microwaveFSM.addTime(10)
        ));
        Button startBtn = new Button("Start", e -> handleAction(
            "Start", microwaveFSM.startCooking()
        ));
        Button stopBtn = new Button("Pause", e -> handleAction(
            "Pause", microwaveFSM.stopClock()
        ));
        Button tickBtn = new Button("Tick", e -> handleAction(
            "Tick", microwaveFSM.tick()
        ));
        Button resetBtn = new Button("Reset", e -> handleAction(
            "Cancel", microwaveFSM.resetClock()
        ));

        messageDisplay = new Span();
        tlaValidationDisplay = new Span("TLA Check: (waiting...)");
        tlaValidationDisplay.getStyle().set("white-space", "pre-wrap");
        tlaValidationDisplay.getStyle().set("marginTop", "1rem");

        controlsDiv.add(openCloseBtn, add10Btn, startBtn, stopBtn, tickBtn, resetBtn,
            messageDisplay, tlaValidationDisplay);

        add(microwaveDiv, controlsDiv);
        updateGraphic();
    }

    private Div buildMicrowaveGraphic() {
        Div container = new Div();
        container.getStyle().set("position", "relative");
        container.getStyle().set("width", "400px");
        container.getStyle().set("height", "220px");
        container.getStyle().set("background", "#f0f0f0");
        container.getStyle().set("border", "2px solid #ccc");
        container.getStyle().set("borderRadius", "8px");

        doorDiv.getStyle().set("width", "220px");
        doorDiv.getStyle().set("height", "180px");
        doorDiv.getStyle().set("background", "#e0e0e0");
        doorDiv.getStyle().set("border", "2px solid #aaa");
        doorDiv.getStyle().set("borderRadius", "6px");
        doorDiv.getStyle().set("position", "absolute");
        doorDiv.getStyle().set("top", "20px");
        doorDiv.getStyle().set("left", "20px");
        doorDiv.getStyle().set("transition", "transform 0.4s");

        Span display = new Span();
        display.getStyle().set("position", "absolute");
        display.getStyle().set("top", "30px");
        display.getStyle().set("left", "40px");
        display.getClassNames().add("timer-display");
        doorDiv.add(display);

        container.add(doorDiv);
        return container;
    }

    private void handleAction(String tlaAction, String msg) {
        messageDisplay.setText(msg);
        String out = tlaSpecService.validateTransition(tlaAction, microwaveFSM);
        
        // Format TLA output to be more concise
        String[] lines = out.split("\n");
        StringBuilder formattedOutput = new StringBuilder();
        
        // Add the action message
        formattedOutput.append(msg).append("\n\n");
        
        // Add TLA Check header
        formattedOutput.append("TLA Check:\n");
        
        // Extract and format the key information
        for (String line : lines) {
            if (line.contains("states generated") || 
                line.contains("distinct states found") ||
                line.contains("depth of the complete state graph") ||
                line.contains("Finished in")) {
                formattedOutput.append(line).append("\n");
            }
        }
        
        tlaValidationDisplay.setText(formattedOutput.toString());
        updateGraphic();
    }

    private void updateGraphic() {
        // door angle
        if (microwaveFSM.getState() == MicrowaveFSM.State.DOOR_OPEN) {
            doorDiv.getStyle().set("transform", "rotateY(-60deg)");
        } else {
            doorDiv.getStyle().remove("transform");
        }
        // update timer text
        Span disp = (Span) doorDiv.getChildren()
            .filter(c -> c.getClassNames().contains("timer-display"))
            .findFirst().get();
        int t = microwaveFSM.getTimer();
        disp.setText(String.format("%02d:%02d", t/60, t%60));
    }
}
