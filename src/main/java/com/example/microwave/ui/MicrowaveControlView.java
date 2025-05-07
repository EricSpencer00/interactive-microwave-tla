package com.example.microwave.ui;

import java.util.ArrayList;
import java.util.List;
import java.util.Timer;
import java.util.TimerTask;

import com.example.microwave.fsm.MicrowaveFSM;
import com.example.microwave.service.TlaSpecService;
import com.vaadin.flow.component.UI;
import com.vaadin.flow.component.button.Button;
import com.vaadin.flow.component.html.Div;
import com.vaadin.flow.component.html.Span;
import com.vaadin.flow.component.orderedlayout.FlexComponent.Alignment;
import com.vaadin.flow.component.orderedlayout.FlexComponent.JustifyContentMode;
import com.vaadin.flow.component.orderedlayout.HorizontalLayout;
import com.vaadin.flow.component.orderedlayout.VerticalLayout;
import com.vaadin.flow.component.textfield.TextArea;

/**
 * An improved UI for the microwave control, with safety/liveness labels outside,
 * the microwave graphic centered, controls beneath, and the TLC check area under all.
 */
public class MicrowaveControlView extends VerticalLayout {
    private final MicrowaveFSM microwaveFSM;
    private final TlaSpecService tlaSpecService;
    private final TextArea tlaValidationArea;
    private final TextArea fullTlaOutput;
    private Timer autoTickTimer;
    private Div timerDisplayBox;
    private Div doorDiv;
    private Div lightIndicator;
    private Div[] radiationWaves = new Div[3];
    private List<TraceEntry> trace = new ArrayList<>();

    public MicrowaveControlView(TlaSpecService tlaSpecService) {
        this.tlaSpecService = tlaSpecService;
        this.microwaveFSM = new MicrowaveFSM();
        this.autoTickTimer = null;

        // Main vertical layout
        setWidthFull();
        setDefaultHorizontalComponentAlignment(Alignment.CENTER);
        setPadding(true);
        setSpacing(true);

        // 1️⃣ Safety/Liveness Labels (outside the microwave)
        HorizontalLayout labelLayout = new HorizontalLayout();
        labelLayout.setWidthFull();
        labelLayout.setJustifyContentMode(JustifyContentMode.CENTER);
        labelLayout.setSpacing(true);
        labelLayout.add(
            createLabel("Safety\n door = OPEN ⇒ radiation = OFF", "orange"),
            createLabel("Liveness\n radiation = ON ⇒ radiation = OFF", "yellow"),
            createLabel("Safety\n radiation = ON ⇒ door = CLOSED", "orange")
        );
        add(labelLayout);

        // 2️⃣ Microwave Graphic
        Div graphic = buildMicrowaveGraphic();
        add(graphic);

        // 3️⃣ Control Buttons
        HorizontalLayout controls = new HorizontalLayout();
        controls.setJustifyContentMode(JustifyContentMode.CENTER);
        controls.setSpacing(true);
        Button doorBtn = new Button("Door", e -> handleAction(
            microwaveFSM.getState() == MicrowaveFSM.State.DOOR_OPEN ? "CloseDoor" : "OpenDoor",
            microwaveFSM.getState() == MicrowaveFSM.State.DOOR_OPEN ? microwaveFSM.closeDoor() : microwaveFSM.openDoor()
        ));
        Button add10 = new Button("+10s", e -> handleAction("IncTime", microwaveFSM.addTime(10)));
        Button start = new Button("Start", e -> handleAction("Start", microwaveFSM.startCooking()));
        Button pause = new Button("Pause", e -> handleAction("Cancel", microwaveFSM.stopClock()));
        Button reset = new Button("Reset", e -> handleAction("Cancel", microwaveFSM.resetClock()));
        for (Button b : new Button[]{doorBtn, add10, start, pause, reset}) {
            b.getStyle()
             .set("background", "#ff9800")
             .set("color", "white")
             .set("border", "none")
             .set("borderRadius", "4px")
             .set("padding", "0.5rem 1rem")
             .set("fontWeight", "bold");
        }
        controls.add(doorBtn, add10, start, pause, reset);
        add(controls);

        // 4️⃣ TLC Check Area (under the microwave)
        tlaValidationArea = new TextArea("TLC Check");
        tlaValidationArea.setWidth("80%");
        tlaValidationArea.setReadOnly(true);
        tlaValidationArea.getStyle()
            .set("white-space", "pre-wrap")
            .set("background", "#fff3e0")
            .set("borderLeft", "4px solid orange");

        fullTlaOutput = new TextArea("Full TLC Output");
        fullTlaOutput.setWidth("80%");
        fullTlaOutput.setReadOnly(true);
        fullTlaOutput.setVisible(false);
        fullTlaOutput.getStyle().set("white-space", "pre-wrap");

        // Toggle full output on click
        tlaValidationArea.addFocusListener(e -> fullTlaOutput.setVisible(!fullTlaOutput.isVisible()));

        add(tlaValidationArea, fullTlaOutput);

        // Initialize the graphic state
        updateGraphic();
    }

    private Span createLabel(String text, String bgColor) {
        Span label = new Span(text);
        label.getStyle()
             .set("background", bgColor)
             .set("color", "black")
             .set("padding", "8px")
             .set("borderRadius", "6px")
             .set("white-space", "pre-line")
             .set("fontSize", "0.85rem");
        return label;
    }

    private Div buildMicrowaveGraphic() {
        int w = 400, h = 220;
        Div container = new Div();
        container.getStyle()
                 .set("position", "relative")
                 .set("width", w + "px")
                 .set("height", h + "px")
                 .set("background", "#f0f0f0")
                 .set("border", "4px solid orange")
                 .set("borderRadius", "12px")
                 .set("boxShadow", "0 4px 24px #ff980033");

        // Timer
        timerDisplayBox = new Div();
        timerDisplayBox.getStyle().set("position", "absolute");
        timerDisplayBox.getStyle().set("top", "16px");
        timerDisplayBox.getStyle().set("right", "16px");
        timerDisplayBox.getStyle().set("width", "72px");
        timerDisplayBox.getStyle().set("height", "32px");
        timerDisplayBox.getStyle().set("background", "#222");
        timerDisplayBox.getStyle().set("color", "#fff");
        timerDisplayBox.getStyle().set("display", "flex");
        timerDisplayBox.getStyle().set("alignItems", "center");
        timerDisplayBox.getStyle().set("justifyContent", "center");
        timerDisplayBox.getStyle().set("fontWeight", "bold");
        timerDisplayBox.getStyle().set("borderRadius", "6px");
        timerDisplayBox.setText("00:00");
        container.add(timerDisplayBox);

        // Door panel
        doorDiv = new Div();
        doorDiv.getStyle().set("position", "absolute");
        doorDiv.getStyle().set("width", "55%");
        doorDiv.getStyle().set("height", "80%");
        doorDiv.getStyle().set("top", "10%");
        doorDiv.getStyle().set("left", "5%");
        doorDiv.getStyle().set("background", "#e0e0e0");
        doorDiv.getStyle().set("border", "2px solid #ff9800");
        container.add(doorDiv);

        // Light indicator
        lightIndicator = new Div();
        lightIndicator.getStyle().set("position", "absolute");
        lightIndicator.getStyle().set("top", "25%");
        lightIndicator.getStyle().set("left", "20%");
        lightIndicator.getStyle().set("width", "32px");
        lightIndicator.getStyle().set("height", "32px");
        lightIndicator.getStyle().set("background", "radial-gradient(circle, #ffe066 60%, #ffeb3b 100%)");
        lightIndicator.getStyle().set("borderRadius", "50%");
        lightIndicator.setVisible(false);
        container.add(lightIndicator);

        // Radiation waves
        for (int i = 0; i < 3; i++) {
            Div wave = new Div();
            wave.getStyle().set("position", "absolute");
            wave.getStyle().set("top", (int)(h*0.35 + i*18) + "px");
            wave.getStyle().set("left", (int)(w*0.23 + i*10) + "px");
            wave.getStyle().set("width", "36px");
            wave.getStyle().set("height", "16px");
            wave.getStyle().set("borderRadius", "50%/60%");
            wave.getStyle().set("background", "linear-gradient(90deg, #ff9800 60%, transparent)");
            wave.setVisible(false);
            radiationWaves[i] = wave;
            container.add(wave);
        }

        return container;
    }

    private void handleAction(String action, String msg) {
        trace.add(new TraceEntry(microwaveFSM.getState(), microwaveFSM.getTimer(), action));
        String out = tlaSpecService.validateTransition(action, microwaveFSM);
        tlaValidationArea.setValue(out);
        fullTlaOutput.setValue(out);
        fullTlaOutput.setVisible(false);
        updateGraphic();
        scheduleAutoTick();
    }

    private void scheduleAutoTick() {
        if (autoTickTimer != null) autoTickTimer.cancel();
        if (microwaveFSM.getState() == MicrowaveFSM.State.COOKING && microwaveFSM.getTimer() > 0) {
            autoTickTimer = new Timer();
            autoTickTimer.scheduleAtFixedRate(new TimerTask() {
                public void run() {
                    UI.getCurrent().access(() -> handleAction("Tick", microwaveFSM.tick()));
                }
            }, 1000, 1000);
        }
    }

    private void updateGraphic() {
        boolean doorOpen = microwaveFSM.getState() == MicrowaveFSM.State.DOOR_OPEN;
        doorDiv.getStyle().set("transform", doorOpen ? "rotateY(135deg)" : "none");
        lightIndicator.setVisible(doorOpen);
        boolean cooking = microwaveFSM.getState() == MicrowaveFSM.State.COOKING;
        for (Div w : radiationWaves) w.setVisible(cooking);
        int t = microwaveFSM.getTimer();
        timerDisplayBox.setText(String.format("%02d:%02d", t/60, t%60));
    }

    private static class TraceEntry {
        final MicrowaveFSM.State state;
        final int timer;
        final String action;
        TraceEntry(MicrowaveFSM.State s, int t, String a) { state = s; timer = t; action = a; }
    }
}
