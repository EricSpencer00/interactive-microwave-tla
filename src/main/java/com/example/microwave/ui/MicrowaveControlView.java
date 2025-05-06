package com.example.microwave.ui;

import com.example.microwave.fsm.MicrowaveFSM;
import com.example.microwave.service.TlaSpecService;
import com.vaadin.flow.component.button.Button;
import com.vaadin.flow.component.html.Div;
import com.vaadin.flow.component.html.Span;
import com.vaadin.flow.component.orderedlayout.FlexComponent.Alignment;
import com.vaadin.flow.component.orderedlayout.FlexComponent.JustifyContentMode;
import com.vaadin.flow.component.orderedlayout.HorizontalLayout;
import com.vaadin.flow.component.orderedlayout.VerticalLayout;

public class MicrowaveControlView extends HorizontalLayout {
    private final MicrowaveFSM microwaveFSM;
    private final TlaSpecService tlaSpecService;

    private final Div microwaveDiv;
    private final Div doorDiv = new Div();
    private Span messageDisplay;
    private Span tlaValidationDisplay;

    private String lastTlaFullOutput = "";
    private boolean tlaExpanded = false;

    public MicrowaveControlView(TlaSpecService tlaSpecService) {
        this.tlaSpecService = tlaSpecService;
        this.microwaveFSM = new MicrowaveFSM();

        setWidthFull();
        setAlignItems(Alignment.CENTER);
        setJustifyContentMode(JustifyContentMode.CENTER);

        // Microwave graphic
        microwaveDiv = buildMicrowaveGraphic();
        add(microwaveDiv);

        // Status and TLA output centered below microwave
        VerticalLayout statusLayout = new VerticalLayout();
        statusLayout.setWidth("400px");
        statusLayout.setAlignItems(Alignment.CENTER);
        statusLayout.setJustifyContentMode(JustifyContentMode.CENTER);
        statusLayout.setPadding(false);
        statusLayout.setSpacing(false);
        statusLayout.setMargin(false);
        statusLayout.getStyle().set("marginTop", "1.5rem");

        messageDisplay = new Span();
        tlaValidationDisplay = new Span("TLA Check:");
        tlaValidationDisplay.getStyle().set("white-space", "pre-wrap");
        tlaValidationDisplay.getStyle().set("marginTop", "0.5rem");
        tlaValidationDisplay.getStyle().set("background", "#fff3e0");
        tlaValidationDisplay.getStyle().set("borderLeft", "4px solid orange");
        tlaValidationDisplay.getStyle().set("padding", "0.5rem 1rem");
        tlaValidationDisplay.getStyle().set("borderRadius", "4px");
        tlaValidationDisplay.getStyle().set("fontSize", "0.95rem");

        // Expandable full TLA output
        Span expandLink = new Span("Show Full TLA Output");
        expandLink.getStyle().set("color", "#ff9800");
        expandLink.getStyle().set("cursor", "pointer");
        expandLink.getStyle().set("marginLeft", "0.5rem");
        Span fullTlaOutput = new Span();
        fullTlaOutput.setVisible(false);
        fullTlaOutput.getStyle().set("white-space", "pre-wrap");
        fullTlaOutput.getStyle().set("background", "#fff3e0");
        fullTlaOutput.getStyle().set("borderLeft", "4px solid orange");
        fullTlaOutput.getStyle().set("padding", "0.5rem 1rem");
        fullTlaOutput.getStyle().set("borderRadius", "4px");
        fullTlaOutput.getStyle().set("fontSize", "0.9rem");
        expandLink.addClickListener(e -> {
            tlaExpanded = !tlaExpanded;
            fullTlaOutput.setVisible(tlaExpanded);
            expandLink.setText(tlaExpanded ? "Hide Full TLA Output" : "Show Full TLA Output");
        });
        statusLayout.add(messageDisplay, tlaValidationDisplay, expandLink, fullTlaOutput);
        add(statusLayout);
        updateGraphic();
    }

    private Div buildMicrowaveGraphic() {
        // Microwave dimensions
        int mwWidth = 400;
        int mwHeight = 220;
        Div container = new Div();
        container.getStyle().set("position", "relative");
        container.getStyle().set("width", mwWidth + "px");
        container.getStyle().set("height", mwHeight + "px");
        container.getStyle().set("background", "#f0f0f0");
        container.getStyle().set("border", "4px solid orange");
        container.getStyle().set("borderRadius", "12px");
        container.getStyle().set("boxShadow", "0 4px 24px #ff980033");

        // Door
        int doorWidth = (int)(mwWidth * 0.55); // 220px
        int doorHeight = (int)(mwHeight * 0.82); // 180px
        doorDiv.getStyle().set("width", doorWidth + "px");
        doorDiv.getStyle().set("height", doorHeight + "px");
        doorDiv.getStyle().set("background", "#e0e0e0");
        doorDiv.getStyle().set("border", "2px solid #ff9800");
        doorDiv.getStyle().set("borderRadius", "6px");
        doorDiv.getStyle().set("position", "absolute");
        doorDiv.getStyle().set("top", (int)(mwHeight*0.09) + "px"); // 20px
        doorDiv.getStyle().set("left", (int)(mwWidth*0.05) + "px"); // 20px
        doorDiv.getStyle().set("transition", "transform 0.5s cubic-bezier(.4,2,.6,1)");
        doorDiv.getStyle().set("transformOrigin", "left center");
        doorDiv.getStyle().set("boxShadow", "0 2px 12px #ff980055");
        // Food (simple orange circle)
        Div food = new Div();
        int foodSize = (int)(doorHeight * 0.22); // 40px
        food.getStyle().set("width", foodSize + "px");
        food.getStyle().set("height", foodSize + "px");
        food.getStyle().set("background", "orange");
        food.getStyle().set("borderRadius", "50%");
        food.getStyle().set("position", "absolute");
        food.getStyle().set("bottom", (int)(doorHeight*0.11) + "px"); // 20px
        food.getStyle().set("left", (int)(doorWidth*0.41) + "px"); // 90px
        food.getStyle().set("boxShadow", "0 2px 8px #ff980055");
        food.setId("food-item");
        doorDiv.add(food);

        // Timer display
        Span display = new Span();
        display.getStyle().set("position", "absolute");
        display.getStyle().set("top", (int)(doorHeight*0.17) + "px"); // 30px
        display.getStyle().set("left", (int)(doorWidth*0.18) + "px"); // 40px
        display.getStyle().set("fontWeight", "bold");
        display.getStyle().set("fontSize", "1.5rem");
        display.getClassNames().add("timer-display");
        doorDiv.add(display);

        container.add(doorDiv);

        // Button panel (inside microwave, right side)
        Div panel = new Div();
        int panelWidth = (int)(mwWidth * 0.3); // 120px
        int panelHeight = (int)(mwHeight * 0.73); // 160px
        panel.getStyle().set("position", "absolute");
        panel.getStyle().set("top", (int)(mwHeight*0.14) + "px"); // 30px
        panel.getStyle().set("right", (int)(mwWidth*0.075) + "px"); // 30px
        panel.getStyle().set("width", panelWidth + "px");
        panel.getStyle().set("height", panelHeight + "px");
        panel.getStyle().set("background", "#fff3e0");
        panel.getStyle().set("borderRadius", "8px");
        panel.getStyle().set("boxShadow", "0 2px 8px #ff980033");
        panel.getStyle().set("display", "flex");
        panel.getStyle().set("flexDirection", "column");
        panel.getStyle().set("alignItems", "center");
        panel.getStyle().set("justifyContent", "center");
        panel.getStyle().set("gap", (int)(panelHeight*0.04) + "px"); // 6px

        // Button sizes as a ratio of panel
        int btnWidth = (int)(panelWidth * 0.75); // 90px
        int btnHeight = (int)(panelHeight * 0.15); // 24px
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
        for (Button b : new Button[]{openCloseBtn, add10Btn, startBtn, stopBtn, tickBtn, resetBtn}) {
            b.getStyle().set("background", "#ff9800");
            b.getStyle().set("color", "white");
            b.getStyle().set("fontWeight", "bold");
            b.getStyle().set("border", "none");
            b.getStyle().set("borderRadius", "4px");
            b.getStyle().set("boxShadow", "0 1px 4px #ff980033");
            b.getStyle().set("width", btnWidth + "px");
            b.getStyle().set("height", btnHeight + "px");
            b.getStyle().set("fontSize", "1rem");
        }
        panel.add(openCloseBtn, add10Btn, startBtn, stopBtn, tickBtn, resetBtn);
        container.add(panel);
        return container;
    }

    private void handleAction(String tlaAction, String msg) {
        messageDisplay.setText(msg);
        String out = tlaSpecService.validateTransition(tlaAction, microwaveFSM);
        lastTlaFullOutput = out;
        // Format TLA output to be more concise
        String[] lines = out.split("\n");
        StringBuilder formattedOutput = new StringBuilder();
        formattedOutput.append("TLA Check:\n");
        for (String line : lines) {
            if (line.contains("states generated") || 
                line.contains("distinct states found") ||
                line.contains("depth of the complete state graph") ||
                line.contains("Finished in")) {
                formattedOutput.append(line).append("\n");
            }
        }
        tlaValidationDisplay.setText(formattedOutput.toString());
        // Update full output if expanded
        Span fullTlaOutput = (Span) ((VerticalLayout) ((Div) microwaveDiv).getChildren().filter(c -> c instanceof VerticalLayout).findFirst().get()).getComponentAt(3);
        fullTlaOutput.setText(lastTlaFullOutput);
        updateGraphic();
    }

    private void updateGraphic() {
        // door angle
        if (microwaveFSM.getState() == MicrowaveFSM.State.DOOR_OPEN) {
            doorDiv.getStyle().set("transform", "rotateY(-80deg)");
            // Show food when door is open
            doorDiv.getChildren().filter(c -> "food-item".equals(c.getId().orElse(""))).findFirst().ifPresent(f -> f.setVisible(true));
        } else {
            doorDiv.getStyle().set("transform", "none");
            // Hide food when door is closed
            doorDiv.getChildren().filter(c -> "food-item".equals(c.getId().orElse(""))).findFirst().ifPresent(f -> f.setVisible(false));
        }
        // update timer text
        Span disp = (Span) doorDiv.getChildren()
            .filter(c -> c.getClassNames().contains("timer-display"))
            .findFirst().get();
        int t = microwaveFSM.getTimer();
        disp.setText(String.format("%02d:%02d", t/60, t%60));
    }
}
