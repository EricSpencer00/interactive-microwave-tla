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
import com.vaadin.flow.component.html.Image;
import com.vaadin.flow.component.html.Span;
import com.vaadin.flow.component.orderedlayout.FlexComponent.Alignment;
import com.vaadin.flow.component.orderedlayout.FlexComponent.JustifyContentMode;
import com.vaadin.flow.component.orderedlayout.HorizontalLayout;
import com.vaadin.flow.component.orderedlayout.VerticalLayout;
import com.vaadin.flow.component.textfield.TextArea;

/**
 * A polished MicrowaveControlView with the microwave rendered as an image
 * plus overlay indicators, labels outside the oven, controls below,
 * and the TLC check panel at the bottom.
 */
public class MicrowaveControlView extends VerticalLayout {
    private final MicrowaveFSM fsm;
    private final TlaSpecService tla;
    private final TextArea tlaCheck;
    private final TextArea fullTla;
    private Div timerDisplay;
    private Div overlayDoor;
    private Div indicatorLight;
    private Div[] waves = new Div[3];
    private Timer autoTick;
    private List<Trace> trace = new ArrayList<>();

    public MicrowaveControlView(TlaSpecService tla) {
        this.fsm = new MicrowaveFSM();
        this.tla = tla;

        setWidthFull();
        setDefaultHorizontalComponentAlignment(Alignment.CENTER);
        setPadding(true);
        setSpacing(true);

        // Labels row
        HorizontalLayout tags = new HorizontalLayout(
            styledLabel("Safety: door=OPEN ⇒ rad=OFF", "#FFA726"),
            styledLabel("Liveness: ON ⇒ OFF", "#FFF176"),
            styledLabel("Safety: rad=ON ⇒ door=CLOSED", "#FFA726")
        );
        tags.setJustifyContentMode(JustifyContentMode.CENTER);
        tags.setSpacing(true);
        add(tags);

        // Microwave graphic container
        Div graphic = new Div();
        graphic.getStyle()
               .set("position", "relative")
               .set("width", "400px")
               .set("height", "250px");

        // Background image
        Image bg = new Image("frontend/images/microwave.svg", "Microwave");
        bg.getStyle().set("width", "100%");
        bg.getStyle().set("height", "100%");
        graphic.add(bg);

        // Timer overlay
        timerDisplay = new Div();
        timerDisplay.getStyle()
            .set("position", "absolute")
            .set("top", "20px")
            .set("right", "40px")
            .set("background", "#333")
            .set("color", "#FFF")
            .set("padding", "4px 8px")
            .set("borderRadius", "4px")
            .set("fontSize", "1.2rem");
        timerDisplay.setText("00:00");
        graphic.add(timerDisplay);

        // Door overlay (clickable)
        overlayDoor = new Div();
        overlayDoor.getStyle()
            .set("position", "absolute")
            .set("top", "80px")
            .set("left", "40px")
            .set("width", "180px")
            .set("height", "140px")
            .set("cursor", "pointer");
        overlayDoor.addClickListener(e -> toggleDoor());
        graphic.add(overlayDoor);

        // Light indicator
        indicatorLight = new Div();
        indicatorLight.getStyle()
            .set("position", "absolute")
            .set("top", "100px")
            .set("left", "90px")
            .set("width", "24px")
            .set("height", "24px")
            .set("background", "radial-gradient(circle, #FFF59D 60%, #FDD835)")
            .set("borderRadius", "50%");
        graphic.add(indicatorLight);

        // Radiation waves
        for (int i = 0; i < waves.length; i++) {
            Div wave = new Div();
            wave.getStyle()
                .set("position", "absolute")
                .set("top", (120 + i*20) + "px")
                .set("left", (100 + i*15) + "px")
                .set("width", "40px")
                .set("height", "16px")
                .set("borderRadius", "50%/60%")
                .set("background", "linear-gradient(90deg, #FFA726 60%, transparent)");
            wave.setVisible(false);
            waves[i] = wave;
            graphic.add(wave);
        }

        add(graphic);

        // Controls row
        HorizontalLayout ctrls = new HorizontalLayout();
        ctrls.setJustifyContentMode(JustifyContentMode.CENTER);
        ctrls.setSpacing(true);
        ctrls.add(
            createBtn("+10s", () -> perform("IncTime", fsm.addTime(10))),
            createBtn("Start", () -> perform("Start", fsm.startCooking())),
            createBtn("Pause", () -> perform("Cancel", fsm.stopClock())),
            createBtn("Reset", () -> perform("Cancel", fsm.resetClock()))
        );
        add(ctrls);

        // TLC area
        tlaCheck = new TextArea("TLC Check");
        tlaCheck.setWidth("80%");
        tlaCheck.setReadOnly(true);
        add(tlaCheck);

        fullTla = new TextArea("Full TLC Output");
        fullTla.setWidth("80%");
        fullTla.setReadOnly(true);
        fullTla.setVisible(false);
        add(fullTla);

        updateView();
    }

    private Span styledLabel(String txt, String bg) {
        Span s = new Span(txt);
        s.getStyle()
         .set("background", bg)
         .set("color", "#000")
         .set("padding", "6px")
         .set("borderRadius", "4px")
         .set("white-space", "pre");
        return s;
    }

    private Button createBtn(String text, Runnable action) {
        Button b = new Button(text, e -> action.run());
        b.getStyle()
         .set("background", "#FFA726")
         .set("color", "#FFF")
         .set("border", "none")
         .set("borderRadius", "4px")
         .set("padding", "0.5rem 1rem");
        return b;
    }

    private void perform(String act, String msg) {
        trace.add(new Trace(fsm.getState(), fsm.getTimer(), act));
        String out = tla.validateTransition(act, fsm);
        tlaCheck.setValue(out);
        fullTla.setValue(out);
        fullTla.setVisible(false);
        scheduleTick();
        updateView();
    }

    private void toggleDoor() {
        if (fsm.getState() == MicrowaveFSM.State.DOOR_OPEN) {
            perform("CloseDoor", fsm.closeDoor());
        } else {
            perform("OpenDoor", fsm.openDoor());
        }
    }

    private void scheduleTick() {
        if (autoTick != null) autoTick.cancel();
        if (fsm.getState() == MicrowaveFSM.State.COOKING && fsm.getTimer() > 0) {
            autoTick = new Timer();
            autoTick.scheduleAtFixedRate(new TimerTask() {
                public void run() {
                    UI.getCurrent().access(() -> perform("Tick", fsm.tick()));
                }
            }, 1000, 1000);
        }
    }

    private void updateView() {
        boolean open = fsm.getState() == MicrowaveFSM.State.DOOR_OPEN;
        overlayDoor.getStyle().set("transform", open ? "rotateY(135deg)" : "none");
        indicatorLight.setVisible(open);
        boolean cook = fsm.getState() == MicrowaveFSM.State.COOKING;
        for (Div w : waves) w.setVisible(cook);
        int t = fsm.getTimer();
        timerDisplay.setText(String.format("%02d:%02d", t/60, t%60));
    }

    private static class Trace {
        Trace(MicrowaveFSM.State s, int t, String a) {}
    }
}
