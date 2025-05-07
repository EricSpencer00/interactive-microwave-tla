package com.example.microwave.ui;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Timer;
import java.util.TimerTask;
import java.util.concurrent.ConcurrentHashMap;

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
 * MicrowaveControlView provides an interactive interface for the microwave simulation
 * with TLA+ validation feedback.
 */
public class MicrowaveControlView extends VerticalLayout {
    private static final String IMAGE_PATH = "images/";
    private static final int IMAGE_WIDTH = 400;
    private static final int IMAGE_HEIGHT = 250;
    private static final int MAX_TLA_OUTPUT_HEIGHT = 200;
    private static final int TIMER_INTERVAL = 1000;
    private static final int DEBOUNCE_DELAY = 500; // ms

    private final MicrowaveFSM fsm;
    private final TlaSpecService tla;
    private final TextArea tlaCheck;
    private final TextArea fullTla;
    private Image ovenImage;
    private Div timerDisplay;
    private Timer autoTick;
    private Timer debounceTimer;
    private List<Trace> trace = new ArrayList<>();
    
    // Cache for image resources
    private final Map<String, StreamResource> imageCache = new ConcurrentHashMap<>();
    
    // State tracking
    private MicrowaveFSM.State lastState;
    private int lastTimer;
    private String lastTlaResult;
    private String lastFullTlaResult;

    public MicrowaveControlView(TlaSpecService tla) {
        this.fsm = new MicrowaveFSM();
        this.tla = tla;
        this.lastState = fsm.getState();
        this.lastTimer = fsm.getTimer();

        setWidthFull();
        setDefaultHorizontalComponentAlignment(Alignment.CENTER);
        setPadding(true);
        setSpacing(true);

        // Microwave display section
        VerticalLayout displaySection = new VerticalLayout();
        displaySection.setWidthFull();
        displaySection.setAlignItems(Alignment.CENTER);
        displaySection.setSpacing(true);

        // Oven image
        ovenImage = new Image(getImageSource(), "Microwave");
        ovenImage.setWidth(IMAGE_WIDTH + "px");
        ovenImage.setHeight(IMAGE_HEIGHT + "px");
        ovenImage.addClickListener(e -> toggleDoor());
        displaySection.add(ovenImage);

        // Timer display
        timerDisplay = new Div();
        timerDisplay.getStyle()
            .set("background", "#333")
            .set("color", "#FFF")
            .set("padding", "8px 16px")
            .set("borderRadius", "4px")
            .set("fontSize", "1.5rem")
            .set("fontFamily", "monospace")
            .set("margin", "1rem 0");
        displaySection.add(timerDisplay);

        add(displaySection);

        // Controls section
        HorizontalLayout controlsSection = new HorizontalLayout();
        controlsSection.setJustifyContentMode(JustifyContentMode.CENTER);
        controlsSection.setSpacing(true);
        controlsSection.setPadding(true);
        controlsSection.getStyle().set("background", "#f5f5f5")
            .set("borderRadius", "8px")
            .set("margin", "1rem 0");
        
        controlsSection.add(
            createBtn("+10s", () -> perform("IncTime", fsm.addTime(10))),
            createBtn("Start", () -> perform("Start", fsm.startCooking())),
            createBtn("Pause", () -> perform("Cancel", fsm.stopClock())),
            createBtn("Reset", () -> perform("Cancel", fsm.resetClock())),
            createBtn("Tick", () -> perform("Tick", fsm.tick())),
            createBtn("Validate Full Spec", this::validateFullSpec)
        );
        add(controlsSection);

        // TLA+ validation section
        VerticalLayout validationSection = new VerticalLayout();
        validationSection.setWidthFull();
        validationSection.setSpacing(true);
        validationSection.getStyle().set("background", "#f8f9fa")
            .set("borderRadius", "8px")
            .set("padding", "1rem")
            .set("margin", "1rem 0");

        tlaCheck = new TextArea("TLA+ Transition Validation");
        tlaCheck.setWidth("100%");
        tlaCheck.setReadOnly(true);
        tlaCheck.setMaxHeight(MAX_TLA_OUTPUT_HEIGHT + "px");
        validationSection.add(tlaCheck);

        fullTla = new TextArea("Full TLA+ Model Check");
        fullTla.setWidth("100%");
        fullTla.setReadOnly(true);
        fullTla.setMaxHeight(MAX_TLA_OUTPUT_HEIGHT + "px");
        validationSection.add(fullTla);

        add(validationSection);

        // Start auto-tick timer
        startAutoTick();

        // Initial state update
        updateDisplay();
    }

    private StreamResource getImageSource() {
        String imageName = fsm.getState() == MicrowaveFSM.State.DOOR_OPEN ? 
            "microwave_open.png" : "microwave_closed.png";
        return imageCache.computeIfAbsent(imageName, name -> 
            new StreamResource(name, () -> 
                getClass().getResourceAsStream("/META-INF/resources/" + IMAGE_PATH + name)));
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
            // Debounce TLA validation
            if (debounceTimer != null) {
                debounceTimer.cancel();
            }
            debounceTimer = new Timer();
            debounceTimer.schedule(new TimerTask() {
                @Override
                public void run() {
                    getUI().ifPresent(ui -> ui.access(() -> {
                        String tlaResult = tla.validateTransition(action, fsm);
                        if (!tlaResult.equals(lastTlaResult)) {
                            tlaCheck.setValue(tlaResult);
                            lastTlaResult = tlaResult;
                        }
                        updateDisplay();
                    }));
                }
            }, DEBOUNCE_DELAY);
        }
    }

    private void validateFullSpec() {
        getUI().ifPresent(ui -> ui.access(() -> {
            String fullResult = tla.runTLC(tla.loadDefaultSpec(), tla.loadDefaultCfg());
            if (!fullResult.equals(lastFullTlaResult)) {
                fullTla.setValue(fullResult);
                lastFullTlaResult = fullResult;
            }
        }));
    }

    private void updateDisplay() {
        // Only update if state or timer changed
        if (fsm.getState() != lastState) {
            ovenImage.setSrc(getImageSource());
            lastState = fsm.getState();
        }
        
        if (fsm.getTimer() != lastTimer) {
            timerDisplay.setText(String.format("%02d:%02d", fsm.getTimer() / 60, fsm.getTimer() % 60));
            lastTimer = fsm.getTimer();
        }
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
        }, TIMER_INTERVAL, TIMER_INTERVAL);
    }

    @Override
    public void onDetach(DetachEvent detachEvent) {
        if (autoTick != null) {
            autoTick.cancel();
        }
        if (debounceTimer != null) {
            debounceTimer.cancel();
        }
        super.onDetach(detachEvent);
    }

    private static class Trace {
        Trace(MicrowaveFSM.State s, int t, String a) {}
    }
}