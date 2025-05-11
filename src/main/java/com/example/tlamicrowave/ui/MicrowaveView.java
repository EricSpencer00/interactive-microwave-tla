package com.example.tlamicrowave.ui;

import com.example.tlamicrowave.model.MicrowaveState;
import com.example.tlamicrowave.service.MicrowaveService;
import com.vaadin.flow.component.UI;
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

        // 2) Microwave graphic
        graphic = new MicrowaveGraphic();

        // 3) Controls
        Button incrementButton = new Button("+3s", e -> { service.incrementTime(); updateUI(); });
        Button startButton     = new Button("Start", e -> { service.start();       updateUI(); });
        Button cancelButton    = new Button("Cancel", e -> { service.cancel();     /* service.stopBeep(); */ updateUI(); });
        Button doorButton      = new Button("Open/Close Door", e -> { service.toggleDoor(); /* service.stopBeep(); */ updateUI(); });
        Button tickButton      = new Button("Tick", e -> { service.manualTick();  updateUI(); });

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

        Stream.of(incrementButton, startButton, cancelButton, doorButton)
            .forEach(btn -> {
                btn.getElement().setAttribute("slot", "buttons");
                graphic.getElement().appendChild(btn.getElement());
            });

        // assemble
        add(timerDisplay);
        add(graphic);
        add(new H2("TLA+ State Trace"));
        add(verificationPanel);
        add(logNavigation);

        // Enable server-side polling
        ui.setPollInterval(1_000);
        ui.addPollListener(event -> {
            timerDisplay.setText(LocalTime.now().format(DateTimeFormatter.ofPattern("HH:mm:ss")));
            updateUI();
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

            // Check safety violations
            if (state.isDoorSafetyViolated()) {
                Notification.show("⚠️ Door Safety Violated!", 3_000, Position.TOP_END);
            }
            // if (state.isBeepSafetyViolated()) {
            //     Notification.show("⚠️ Beep Safety Violated!", 3_000, Position.TOP_END);
            // }
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
