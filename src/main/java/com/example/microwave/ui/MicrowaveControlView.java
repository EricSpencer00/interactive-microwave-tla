package com.example.microwave.ui;

import java.util.ArrayList;
import java.util.List;
import java.util.Timer;
import java.util.TimerTask;

import com.example.microwave.fsm.MicrowaveFSM;
import com.example.microwave.service.TlaSpecService;
import com.vaadin.flow.component.Component;
import com.vaadin.flow.component.ComponentEventListener;
import com.vaadin.flow.component.DetachEvent;
import com.vaadin.flow.component.button.Button;
import com.vaadin.flow.component.html.Div;
import com.vaadin.flow.component.html.Image;
import com.vaadin.flow.component.orderedlayout.FlexComponent.Alignment;
import com.vaadin.flow.component.orderedlayout.FlexComponent.JustifyContentMode;
import com.vaadin.flow.component.orderedlayout.HorizontalLayout;
import com.vaadin.flow.component.orderedlayout.VerticalLayout;
import com.vaadin.flow.component.textfield.TextArea;
import com.vaadin.flow.server.StreamResource;

/**
 * MicrowaveControlView uses hardcoded images for each state,
 * a Tick button, and no safety/liveness labels.
 */
public class MicrowaveControlView extends VerticalLayout {
    private final MicrowaveFSM fsm;
    private final TlaSpecService tla;
    private final TextArea tlaCheck;
    private final TextArea fullTla;
    private Image ovenImage;
    private Div timerDisplay;
    private Timer autoTick;
    private List<Trace> trace = new ArrayList<>();

    public MicrowaveControlView(TlaSpecService tla) {
        this.fsm = new MicrowaveFSM();
        this.tla = tla;

        setWidthFull();
        setDefaultHorizontalComponentAlignment(Alignment.CENTER);
        setPadding(true);
        setSpacing(true);

        // Oven image
        ovenImage = new Image(getImageSource(), "Microwave");
        ovenImage.setWidth("400px");
        ovenImage.setHeight("250px");
        ovenImage.addClickListener(e -> toggleDoor());
        add(ovenImage);

        // Timer display
        timerDisplay = new Div();
        timerDisplay.getStyle()
            .set("background", "#333")
            .set("color", "#FFF")
            .set("padding", "4px 8px")
            .set("borderRadius", "4px")
            .set("fontSize", "1.2rem")
            .set("fontFamily", "monospace");
        add(timerDisplay);

        // Controls row with Tick button
        HorizontalLayout ctrls = new HorizontalLayout();
        ctrls.setJustifyContentMode(JustifyContentMode.CENTER);
        ctrls.setSpacing(true);
        ctrls.add(
            createBtn("+10s", () -> perform("IncTime", fsm.addTime(10))),
            createBtn("Start", () -> perform("Start", fsm.startCooking())),
            createBtn("Pause", () -> perform("Cancel", fsm.stopClock())),
            createBtn("Reset", () -> perform("Cancel", fsm.resetClock())),
            createBtn("Tick", () -> perform("Tick", fsm.tick()))
        );
        add(ctrls);

        // TLC output panels
        tlaCheck = new TextArea("TLC Check");
        tlaCheck.setWidth("80%");
        tlaCheck.setReadOnly(true);
        tlaCheck.setMaxHeight("200px");
        add(tlaCheck);

        fullTla = new TextArea("Full TLC Output");
        fullTla.setWidth("80%");
        fullTla.setReadOnly(true);
        fullTla.setMaxHeight("200px");
        add(fullTla);

        // Start auto-tick timer
        startAutoTick();

        // Initial state update
        updateDisplay();
    }

    private StreamResource getImageSource() {
        String imageName = fsm.getState() == MicrowaveFSM.State.DOOR_OPEN ? 
            "microwave_open.png" : "microwave_closed.png";
        return new StreamResource(imageName, () -> 
            getClass().getResourceAsStream("/META-INF/resources/frontend/images/" + imageName));
    }

    private void toggleDoor() {
        if (fsm.getState() == MicrowaveFSM.State.DOOR_OPEN) {
            perform("CloseDoor", fsm.closeDoor());
        } else {
            perform("OpenDoor", fsm.openDoor());
        }
    }

    private void perform(String action, String result) {
        if (result != null && !result.startsWith("Cannot")) {
            String tlaResult = tla.validateTransition(action, fsm);
            tlaCheck.setValue(tlaResult);
            fullTla.setValue(tla.runTLC(tla.loadDefaultSpec(), tla.loadDefaultCfg()));
            updateDisplay();
        }
    }

    private void updateDisplay() {
        ovenImage.setSrc(getImageSource());
        timerDisplay.setText(String.format("%02d:%02d", fsm.getTimer() / 60, fsm.getTimer() % 60));
    }

    private Component createBtn(String label, Runnable action) {
        Button btn = new Button(label);
        btn.addClickListener(e -> action.run());
        return btn;
    }

    private void startAutoTick() {
        autoTick = new Timer();
        autoTick.scheduleAtFixedRate(new TimerTask() {
            @Override
            public void run() {
                if (fsm.getState() == MicrowaveFSM.State.COOKING) {
                    getUI().ifPresent(ui -> ui.access(() -> {
                        perform("Tick", fsm.tick());
                    }));
                }
            }
        }, 1000, 1000);
    }

    @Override
    public void onDetach(DetachEvent detachEvent) {
        if (autoTick != null) {
            autoTick.cancel();
        }
        super.onDetach(detachEvent);
    }

    private static class Trace {
        Trace(MicrowaveFSM.State s, int t, String a) {}
    }
}