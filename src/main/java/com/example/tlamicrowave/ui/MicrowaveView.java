package com.example.tlamicrowave.ui;

import com.example.tlamicrowave.model.MicrowaveState;
import com.example.tlamicrowave.service.MicrowaveService;
import com.example.tlamicrowave.service.VerificationLogService;
import com.vaadin.flow.component.UI;
import com.vaadin.flow.component.button.Button;
import com.vaadin.flow.component.checkbox.Checkbox;
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
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

@Route("")
@PermitAll
@JsModule("./microwave-graphic.ts")
public class MicrowaveView extends VerticalLayout {
    private final MicrowaveService service;
    private final VerificationLogService logService;
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
    private final HorizontalLayout logNavigation;
    private static final Logger log = LoggerFactory.getLogger(MicrowaveView.class);
    private final Checkbox dangerModeToggle;

    @Autowired
    public MicrowaveView(MicrowaveService service, VerificationLogService logService) {
        this.service = service;
        this.logService = logService;
        this.ui = UI.getCurrent();
        service.setUI(ui);

        setSizeFull();
        setAlignItems(Alignment.CENTER);
        setJustifyContentMode(JustifyContentMode.CENTER);
        
        // Create top bar with dangerous mode toggle
        HorizontalLayout topBar = new HorizontalLayout();
        topBar.setWidthFull();
        topBar.setJustifyContentMode(JustifyContentMode.END);
        
        dangerModeToggle = new Checkbox("⚠️ Dangerous Mode");
        dangerModeToggle.addValueChangeListener(e -> {
            boolean dangerous = e.getValue();
            service.setDangerousMode(dangerous);
            if (dangerous) {
                Notification.show("⚠️ Dangerous Mode Enabled - Safety protections disabled!", 
                    3000, Position.TOP_CENTER);
            } else {
                Notification.show("✅ Safe Mode Enabled - Safety protections active", 
                    3000, Position.TOP_CENTER);
            }
        });
        
        dangerModeToggle.getStyle()
            .set("margin-right", "20px")
            .set("padding", "8px")
            .set("background-color", "#fff3cd")
            .set("border-radius", "4px")
            .set("border", "1px solid #ffeeba");
            
        topBar.add(dangerModeToggle);
        add(topBar);

        // 1) Timer display
        timerDisplay = new Div();
        timerDisplay.addClassName("timer-display");
        timerDisplay.getStyle().set("font-size", "1.2em");
        timerDisplay.getStyle().set("margin-bottom", "1em");

        // 2) Microwave graphic
        graphic = new MicrowaveGraphic();

        // 3) Controls
        Button incrementButton = new Button("", e -> { service.incrementTime(); updateUI(); });
        Button startButton     = new Button("", e -> { service.start();       updateUI(); });
        Button cancelButton    = new Button("", e -> { service.cancel();     /* service.stopBeep(); */ updateUI(); });
        Button doorButton      = new Button("", e -> { service.toggleDoor(); /* service.stopBeep(); */ updateUI(); });
        // Button tickButton      = new Button("Tick", e -> { service.manualTick();  updateUI(); });
        Button powerButton     = new Button("", e -> { service.togglePower(); updateUI(); });

        // Style buttons with background images
        incrementButton.getStyle().set("background-image", "url('/images/plus3s.png')");
        startButton.getStyle().set("background-image", "url('/images/start.png')");
        cancelButton.getStyle().set("background-image", "url('/images/cancel.png')");
        doorButton.getStyle().set("background-image", "url('/images/door.png')");
        powerButton.getStyle().set("background-image", "url('/images/power.png')");

        // Set button sizes
        Stream.of(incrementButton, startButton, cancelButton, doorButton, powerButton)
            .forEach(btn -> {
                btn.getStyle().set("width", "100%");
                btn.getStyle().set("height", "100%");
                btn.getStyle().set("background-size", "contain");
                btn.getStyle().set("background-repeat", "no-repeat");
                btn.getStyle().set("background-position", "center");
                btn.getStyle().set("border", "none");
                btn.getStyle().set("padding", "0");
                btn.getElement().setAttribute("slot", "buttons");
                graphic.getElement().appendChild(btn.getElement());
            });

        // 4) Verification panel
        verificationPanel = new Div();
        verificationPanel.addClassName("verification-panel");
        verificationPanel.getStyle().set("padding", "1em")
                                    .set("border", "1px solid #ddd")
                                    .set("border-radius", "5px")
                                    .set("font-family", "monospace")
                                    .set("white-space", "pre")
                                    .set("background-color", "#f8f9fa")
                                    .set("width", "800px")
                                    .set("height", "400px")
                                    .set("max-height", "400px")
                                    .set("overflow-y", "auto")
                                    .set("overflow-x", "hidden");

        // Navigation buttons for logs
        logNavigation = new HorizontalLayout();
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
        Button verifyBtn = new Button("Verify with TLC", e -> {
            try {
                service.verifyWithTlc();
                var result = service.getLastTlcResult();
                if (result == null) {
                    Notification.show("TLC not run yet", 2_000, Position.TOP_END);
                    verificationPanel.setText("TLC verification not run yet.");
                } else if (result.invariantHolds) {
                    Notification.show("✔ Invariant holds!", 3_000, Position.TOP_END);
                    verificationPanel.setText("Invariant holds! No violations found.");
                } else {
                    Notification.show("❌ Violation detected", 3_000, Position.TOP_END);
                    StringBuilder sb = new StringBuilder();
                    sb.append("Violation detected!\n\n");
                    
                    if (result.traceStates != null && !result.traceStates.isEmpty()) {
                        sb.append("Violation Trace:\n\n");
                        for (int i = 0; i < result.traceStates.size(); i++) {
                            sb.append("State ").append(i).append(":\n");
                            result.traceStates.get(i).forEach((k, v) -> 
                                sb.append("  ").append(k).append(" = ").append(v).append("\n"));
                            sb.append("\n");
                        }
                    } else {
                        sb.append("Raw TLC Output:\n\n");
                        sb.append(result.rawOutput);
                    }
                    
                    verificationPanel.setText(sb.toString());
                }
            } catch (Exception ex) {
                log.error("TLC verification failed", ex);
                Notification.show("Error running TLC: " + ex.getMessage(), 5_000, Position.TOP_END);
                verificationPanel.setText("Error running TLC:\n\n" + ex.getMessage());
            }
        });
        logNavigation.add(prevButton, nextButton, showAllButton, verifyBtn);
        logNavigation.setSpacing(true);

        // Update bounding box when show all button is clicked
        showAllButton.addClickListener(e -> {
            verificationPanel.getStyle().set("min-height", showAllLogs ? "400px" : "100px");
        });

        // assemble
        add(timerDisplay);
        add(graphic);
        add(new H2("TLA+ State Trace"));
        add(verificationPanel);
        add(logNavigation);

        service.logState("Initial");
        allLogs.addAll(service.getVerificationLog());
        updateLogDisplay();

        // Internal clock that updates frontend every second
        ui.setPollInterval(1_000);
        ui.addPollListener(event -> {
            // timerDisplay.setText(LocalTime.now().format(DateTimeFormatter.ofPattern("HH:mm:ss")));
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

            // Update dangerous mode indicator UI
            if (service.isDangerousMode()) {
                dangerModeToggle.getStyle()
                    .set("background-color", "#f8d7da")
                    .set("border", "1px solid #f5c6cb");
            } else {
                dangerModeToggle.getStyle()
                    .set("background-color", "#fff3cd")
                    .set("border", "1px solid #ffeeba");
            }

            // Check safety violations - only show in UI if not in dangerous mode
            if (!service.isDangerousMode()) {
                if (state.isDoorSafetyViolated()) {
                    Notification.show("⚠️ Door Safety Violated!", 3_000, Position.TOP_END);
                }
                // if (state.isBeepSafetyViolated()) {
                //     Notification.show("⚠️ Beep Safety Violated!", 3_000, Position.TOP_END);
                // }
                if (state.isRadiationSafetyViolated()) {
                    Notification.show("⚠️ Radiation Safety Violated!", 3_000, Position.TOP_END);
                }
            }

            // Update verification log
            allLogs.clear();
            allLogs.addAll(service.getVerificationLog());
            // Always show the latest state when not in "Show All" mode
            if (!showAllLogs) {
                currentLogIndex = Math.max(0, allLogs.size() - 1);
            }
            updateLogDisplay();

            // Show notification for violation attempts only once (and only in safe mode)
            if (!service.isDangerousMode()) {
                service.getVerificationLog().forEach(log -> {
                    if (log.contains("Violation Attempt") && !shownViolations.contains(log)) {
                        Notification.show(log, 3_000, Position.TOP_END);
                        shownViolations.add(log);
                    }
                });
            }
        });
    }
}
