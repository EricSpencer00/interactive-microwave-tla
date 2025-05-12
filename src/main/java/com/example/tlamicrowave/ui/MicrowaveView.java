package com.example.tlamicrowave.ui;

import com.example.tlamicrowave.model.MicrowaveState;
import com.example.tlamicrowave.service.MicrowaveService;
import com.vaadin.flow.component.UI;
import com.vaadin.flow.component.Component;
import com.vaadin.flow.component.button.Button;
import com.vaadin.flow.component.dependency.JsModule;
import com.vaadin.flow.component.html.Div;
import com.vaadin.flow.component.html.H2;
import com.vaadin.flow.component.notification.Notification;
import com.vaadin.flow.component.notification.Notification.Position;
import com.vaadin.flow.component.orderedlayout.VerticalLayout;
import com.vaadin.flow.component.orderedlayout.HorizontalLayout;
import com.vaadin.flow.router.Route;
import jakarta.annotation.security.PermitAll;
import org.springframework.beans.factory.annotation.Autowired;
import java.time.LocalTime;
import java.time.format.DateTimeFormatter;
import java.util.stream.Stream;
import java.util.HashSet;
import java.util.Set;
import java.util.List;
import java.util.ArrayList;
import java.util.Arrays;

@Route("")
@PermitAll
@JsModule("./microwave-graphic.ts")
public class MicrowaveView extends VerticalLayout {
    private final MicrowaveService service;
    private final Div timerDisplay;
    private final Div verificationPanel;
    private final UI ui;
    private final MicrowaveGraphic graphic;
    private final Set<String> shownViolations = new HashSet<>();
    private final List<String> allLogs = new ArrayList<>();
    private int currentLogIndex = 0;
    private static final int LOGS_PER_PAGE = 1;
    private boolean showAllLogs = false;
    private Button showAllButton;

    // State tracking for polling
    private int lastTime = -1;
    private MicrowaveState.DoorState lastDoor = null;
    private MicrowaveState.RadiationState lastRad = null;
    private int lastLogSize = -1;

    @Autowired
    public MicrowaveView(MicrowaveService service) {
        this.service = service;
        this.ui = UI.getCurrent();
        service.setUI(ui);

        setSizeFull();
        setAlignItems(Alignment.CENTER);
        setJustifyContentMode(JustifyContentMode.CENTER);

        // 1) Timer display
        timerDisplay = new Div();
        timerDisplay.addClassName("timer-display");
        timerDisplay.getStyle().set("font-size", "1.2em");
        timerDisplay.getStyle().set("margin-bottom", "1em");
        timerDisplay.getElement().setAttribute("slot", "buttons");

        // 2) Microwave graphic
        graphic = new MicrowaveGraphic();
        graphic.getStyle()
               .set("width", "700px")
               .set("height", "500px")
               .set("flex", "none")
               .set("min-width", "700px")
               .set("max-width", "700px")
               .set("min-height", "500px")
               .set("max-height", "500px")
               .set("margin-bottom", "1em");

        // 3) Controls (six only: Power, Timer, +3s, Start, Cancel, Door)
        Button incrementButton = new Button("", e -> { service.incrementTime(); updateUI(); });
        Button startButton     = new Button("", e -> { service.start();         updateUI(); });
        Button cancelButton    = new Button("", e -> { service.cancel();        updateUI(); });
        Button doorButton      = new Button("", e -> { service.toggleDoor();    updateUI(); });
        Button powerButton     = new Button("", e -> { service.togglePower();   updateUI(); });
        powerButton.addClassName("power-toggle-button");

        // Style buttons with background images
        incrementButton.getStyle().set("background-image", "url('/images/plus3s.png')");
        startButton.getStyle().set("background-image", "url('/images/start.png')");
        cancelButton.getStyle().set("background-image", "url('/images/cancel.png')");
        doorButton.getStyle().set("background-image", "url('/images/door.png')");
        powerButton.getStyle().set("background-image", "url('/images/power.png')");

        // slot all six in exactly this order:
        //   [Power] [Timer] [+3s] [Start] [Cancel] [Door]
        List<Component> controls = List.of(
            powerButton,
            timerDisplay,
            incrementButton,
            startButton,
            cancelButton,
            doorButton
        );
        controls.forEach(c -> {
            c.getElement().setAttribute("slot", "buttons");
            graphic.getElement().appendChild(c.getElement());
        });

        // Add timer display to the graphic
        graphic.getElement().appendChild(timerDisplay.getElement());

        // Add the graphic to the layout
        add(graphic);

        // 4) Verification panel
        verificationPanel = new Div();
        verificationPanel.addClassName("verification-panel");
        verificationPanel.getStyle().set("margin-top", "2em");
        verificationPanel.getStyle().set("padding", "1em");
        verificationPanel.getStyle().set("border", "1px solid #ddd");
        verificationPanel.getStyle().set("border-radius", "5px");
        verificationPanel.getStyle().set("font-family", "monospace");
        verificationPanel.getStyle().set("white-space", "pre");
        verificationPanel.setWidth("800px");
        verificationPanel.getStyle().set("min-height", "100px");
        verificationPanel.getStyle().set("background-color", "#f8f9fa");

        // Navigation buttons for logs
        HorizontalLayout logNavigation = new HorizontalLayout();
        Button prevButton = new Button("Previous", e -> {
            if (currentLogIndex > 0) {
                currentLogIndex--;
                updateLogDisplay();
            }
        });
        Button nextButton = new Button("Next", e -> {
            if (currentLogIndex < allLogs.size() - 1) {
                currentLogIndex++;
                updateLogDisplay();
            }
        });
        showAllButton = new Button("Show All", e -> {
            showAllLogs = !showAllLogs;
            showAllButton.setText(showAllLogs ? "Show One" : "Show All");
            updateLogDisplay();
        });
        logNavigation.add(prevButton, nextButton, showAllButton);
        logNavigation.setSpacing(true);

        // assemble
        add(verificationPanel);
        add(logNavigation);

        // Enable server-side polling
        ui.setPollInterval(1_000);
        ui.addPollListener(event -> {
            // 1) keep the clock ticking
            timerDisplay.setText(
                LocalTime.now().format(DateTimeFormatter.ofPattern("HH:mm"))
            );

            // 2) grab the current state
            MicrowaveState st = service.getState();
            List<String> logs = service.getVerificationLog();

            // 3) detect any change
            boolean changed =
                st.getTimeRemaining() != lastTime ||
                st.getDoor() != lastDoor ||
                st.getRadiation() != lastRad ||
                logs.size() != lastLogSize;

            if (changed) {
                updateUI();
                // remember for next time
                lastTime = st.getTimeRemaining();
                lastDoor = st.getDoor();
                lastRad = st.getRadiation();
                lastLogSize = logs.size();
            }
        });

        // initial render
        updateUI();
    }

    private void updateLogDisplay() {
        verificationPanel.removeAll();
        if (!allLogs.isEmpty()) {
            if (showAllLogs) {
                // Show all logs
                allLogs.forEach(log -> {
                    Div entry = new Div(log);
                    entry.getStyle().set("margin", "0.2em 0");
                    verificationPanel.add(entry);
                });
            } else {
                // Show single log
                if (currentLogIndex < allLogs.size()) {
                    Div entry = new Div(allLogs.get(currentLogIndex));
                    entry.getStyle().set("margin", "0.2em 0");
                    verificationPanel.add(entry);
                }
            }
        }
    }

    private void updateUI() {
        ui.access(() -> {
            MicrowaveState state = service.getState();

            // Update microwave graphic
            graphic.getElement().setProperty("doorOpen", state.getDoor() == MicrowaveState.DoorState.OPEN);
            graphic.getElement().setProperty("heating", state.getRadiation() == MicrowaveState.RadiationState.ON);
            // graphic.getElement().setProperty("beeping", state.getBeep() == MicrowaveState.BeepState.ON);
            graphic.getElement().setProperty("time", state.getTimeRemaining());
            graphic.getElement().setProperty("powerOn", state.getPower() == MicrowaveState.PowerState.ON);

            // Check safety violations
            if (state.isDoorSafetyViolated()) {
                Notification.show("⚠️ Door Safety Violated!", 3_000, Position.TOP_END);
            }
            if (state.isRadiationSafetyViolated()) {
                Notification.show("⚠️ Radiation Safety Violated!", 3_000, Position.TOP_END);
            }

            // Update verification log
            allLogs.clear();
            allLogs.addAll(service.getVerificationLog());
            // Always show the latest state when not in "Show All" mode
            if (!showAllLogs) {
                currentLogIndex = Math.max(0, allLogs.size() - 1);
            }
            updateLogDisplay();

            // Show notification for violation attempts only once
            service.getVerificationLog().forEach(log -> {
                if (log.contains("Violation Attempt") && !shownViolations.contains(log)) {
                    Notification.show(log, 3_000, Position.TOP_END);
                    shownViolations.add(log);
                }
            });
        });
    }
}
