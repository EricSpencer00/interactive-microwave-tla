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
import com.vaadin.flow.component.UI;
import java.util.Timer;
import java.util.TimerTask;
import java.util.ArrayList;
import java.util.List;

public class MicrowaveControlView extends HorizontalLayout {
    private final MicrowaveFSM microwaveFSM;
    private final TlaSpecService tlaSpecService;

    private final Div microwaveDiv;
    private final Div doorDiv = new Div();
    private Span messageDisplay;
    private Span tlaValidationDisplay;
    private Span fullTlaOutput;

    private String lastTlaFullOutput = "";
    private boolean tlaExpanded = false;
    private Timer autoTickTimer;

    private Div timerDisplayBox;
    private Div lightIndicator;
    private Div[] radiationWaves = new Div[3];

    private List<MicrowaveTraceEntry> trace = new ArrayList<>();

    public MicrowaveControlView(TlaSpecService tlaSpecService) {
        this.tlaSpecService = tlaSpecService;
        this.microwaveFSM = new MicrowaveFSM();
        this.autoTickTimer = null;

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
        fullTlaOutput = new Span();
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

        // Add Verify Trace button below the microwave
        Button verifyTraceBtn = new Button("Verify Trace", e -> verifyTrace());
        verifyTraceBtn.getStyle().set("background", "#ff9800");
        verifyTraceBtn.getStyle().set("color", "white");
        verifyTraceBtn.getStyle().set("fontWeight", "bold");
        verifyTraceBtn.getStyle().set("border", "none");
        verifyTraceBtn.getStyle().set("borderRadius", "4px");
        verifyTraceBtn.getStyle().set("boxShadow", "0 1px 4px #ff980033");
        verifyTraceBtn.getStyle().set("width", "160px");
        verifyTraceBtn.getStyle().set("height", "40px");
        verifyTraceBtn.getStyle().set("fontSize", "1.1rem");
        add(verifyTraceBtn);

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

        // Timer display (on box, above button panel)
        timerDisplayBox = new Div();
        timerDisplayBox.getStyle().set("position", "absolute");
        timerDisplayBox.getStyle().set("top", "18px");
        timerDisplayBox.getStyle().set("right", "50px");
        timerDisplayBox.getStyle().set("width", "80px");
        timerDisplayBox.getStyle().set("height", "36px");
        timerDisplayBox.getStyle().set("background", "#222");
        timerDisplayBox.getStyle().set("color", "#fff");
        timerDisplayBox.getStyle().set("display", "flex");
        timerDisplayBox.getStyle().set("alignItems", "center");
        timerDisplayBox.getStyle().set("justifyContent", "center");
        timerDisplayBox.getStyle().set("fontWeight", "bold");
        timerDisplayBox.getStyle().set("fontSize", "1.5rem");
        timerDisplayBox.getStyle().set("borderRadius", "8px");
        timerDisplayBox.getStyle().set("boxShadow", "0 1px 6px #0002");
        timerDisplayBox.setText("00:00");
        container.add(timerDisplayBox);

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
        container.add(doorDiv);

        // Light indicator (yellow circle, inside microwave, visible when door is open)
        lightIndicator = new Div();
        lightIndicator.getStyle().set("position", "absolute");
        lightIndicator.getStyle().set("top", (int)(mwHeight*0.18) + "px");
        lightIndicator.getStyle().set("left", (int)(mwWidth*0.18) + "px");
        lightIndicator.getStyle().set("width", "36px");
        lightIndicator.getStyle().set("height", "36px");
        lightIndicator.getStyle().set("background", "radial-gradient(circle, #ffe066 60%, #ffeb3b 100%)");
        lightIndicator.getStyle().set("borderRadius", "50%");
        lightIndicator.getStyle().set("boxShadow", "0 0 24px 8px #ffe06699");
        lightIndicator.setVisible(false);
        container.add(lightIndicator);

        // Radiation waves (3 orange waves, visible when cooking)
        for (int i = 0; i < 3; i++) {
            Div wave = new Div();
            wave.getStyle().set("position", "absolute");
            wave.getStyle().set("top", (int)(mwHeight*0.35 + i*18) + "px");
            wave.getStyle().set("left", (int)(mwWidth*0.23 + i*10) + "px");
            wave.getStyle().set("width", "36px");
            wave.getStyle().set("height", "16px");
            wave.getStyle().set("borderRadius", "50% 50% 50% 50% / 60% 60% 40% 40%");
            wave.getStyle().set("background", "linear-gradient(90deg, #ff9800 60%, #fff0 100%)");
            wave.getStyle().set("opacity", "0.85");
            wave.setVisible(false);
            container.add(wave);
            radiationWaves[i] = wave;
        }

        // Button panel (inside microwave, right side, below timer)
        Div panel = new Div();
        int panelWidth = (int)(mwWidth * 0.3); // 120px
        int panelHeight = (int)(mwHeight * 0.73); // 160px
        panel.getStyle().set("position", "absolute");
        panel.getStyle().set("top", (int)(mwHeight*0.32) + "px"); // moved down to fit timer
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
        Button openCloseBtn = new Button("Door", e -> handleAction(
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
        // Record trace entry
        trace.add(new MicrowaveTraceEntry(microwaveFSM.getState().name(), microwaveFSM.getTimer(), tlaAction));
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
        fullTlaOutput.setText(lastTlaFullOutput);
        updateGraphic();
        handleAutoTick();
    }

    private void handleAutoTick() {
        // Cancel any previous timer
        if (autoTickTimer != null) {
            autoTickTimer.cancel();
            autoTickTimer = null;
        }
        // If cooking, start a new timer
        if (microwaveFSM.getState() == MicrowaveFSM.State.COOKING && microwaveFSM.getTimer() > 0) {
            autoTickTimer = new Timer();
            autoTickTimer.scheduleAtFixedRate(new TimerTask() {
                @Override
                public void run() {
                    UI.getCurrent().access(() -> {
                        if (microwaveFSM.getState() == MicrowaveFSM.State.COOKING && microwaveFSM.getTimer() > 0) {
                            handleAction("Tick", microwaveFSM.tick());
                        } else {
                            autoTickTimer.cancel();
                        }
                    });
                }
            }, 1000, 1000);
        }
    }

    private void updateGraphic() {
        // door angle and width
        if (microwaveFSM.getState() == MicrowaveFSM.State.DOOR_OPEN) {
            doorDiv.getStyle().set("transform", "rotateY(135deg)");
            // Show food when door is open
            doorDiv.getChildren().filter(c -> "food-item".equals(c.getId().orElse(""))).findFirst().ifPresent(f -> f.setVisible(true));
            // Show light
            lightIndicator.setVisible(true);
        } else {
            doorDiv.getStyle().set("transform", "none");
            // Hide food when door is closed
            doorDiv.getChildren().filter(c -> "food-item".equals(c.getId().orElse(""))).findFirst().ifPresent(f -> f.setVisible(false));
            // Hide light
            lightIndicator.setVisible(false);
        }
        // update timer text (on box)
        int t = microwaveFSM.getTimer();
        timerDisplayBox.setText(String.format("%02d:%02d", t/60, t%60));
        // Radiation waves
        boolean radiationOn = (microwaveFSM.getState() == MicrowaveFSM.State.COOKING);
        for (Div wave : radiationWaves) {
            wave.setVisible(radiationOn);
        }
    }

    private void verifyTrace() {
        // Export trace as TLA+ sequence
        String tlaTrace = exportTraceAsTLA();
        // Generate composed TLA+ spec
        String composedSpec = generateComposedTlaSpec(tlaTrace);
        // Run TLC on composed spec
        String result = tlaSpecService.runTLC(composedSpec, "");
        // Show result in the UI
        fullTlaOutput.setVisible(true);
        fullTlaOutput.setText(result);
    }

    private String exportTraceAsTLA() {
        StringBuilder sb = new StringBuilder();
        sb.append("Trace == <<\n");
        for (MicrowaveTraceEntry entry : trace) {
            sb.append(String.format("  [state |-> \"%s\", timer |-> %d, action |-> \"%s\"],\n", entry.state, entry.timer, entry.action));
        }
        sb.append(">>\n");
        return sb.toString();
    }

    private String generateComposedTlaSpec(String tlaTrace) {
        // This is a simplified version. In a real implementation, you would compose the trace and the spec as in the paper.
        // For now, just append the trace to the spec for demonstration.
        String baseSpec = tlaSpecService.loadDefaultSpec();
        return baseSpec + "\n" + tlaTrace;
    }

    private static class MicrowaveTraceEntry {
        String state;
        int timer;
        String action;
        MicrowaveTraceEntry(String state, int timer, String action) {
            this.state = state;
            this.timer = timer;
            this.action = action;
        }
    }
}
