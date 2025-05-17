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
import java.util.Arrays;
import com.vaadin.flow.component.Component;
import com.vaadin.flow.component.orderedlayout.FlexLayout;
import com.vaadin.flow.component.tabs.Tab;
import com.vaadin.flow.component.tabs.Tabs;

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
    private boolean isNavigatingHistory = false;
    private Button showAllButton;
    private Button verifyBtn;
    private final HorizontalLayout logNavigation;
    private static final Logger log = LoggerFactory.getLogger(MicrowaveView.class);
    private Button powerButton;
    private Tabs leftPanelTabs;
    private Div leftPanelContent;

    @Autowired
    public MicrowaveView(MicrowaveService service, VerificationLogService logService) {
        this.service = service;
        this.logService = logService;
        this.ui = UI.getCurrent();
        service.setUI(ui);

        setSizeFull();
        setPadding(false);
        setMargin(false);
        setSpacing(false);
        
        FlexLayout mainLayout = new FlexLayout();
        mainLayout.setSizeFull();
        
        // Create left panel with tabs
        VerticalLayout leftPanel = createLeftPanel();
        
        VerticalLayout microwaveContent = new VerticalLayout();
        microwaveContent.setSizeFull();
        microwaveContent.setAlignItems(Alignment.CENTER);
        microwaveContent.setJustifyContentMode(JustifyContentMode.CENTER);
        microwaveContent.setPadding(true);
        
        HorizontalLayout topBar = new HorizontalLayout();
        topBar.setWidthFull();
        topBar.setJustifyContentMode(JustifyContentMode.CENTER);
        
        H2 title = new H2("Interactive TLA Microwave");
        title.getStyle()
            .set("margin", "0")
            .set("font-size", "1.5em")
            .set("color", "#333")
            .set("font-weight", "bold");
        
        topBar.add(title);
        microwaveContent.add(topBar);

        HorizontalLayout timerLayout = new HorizontalLayout();
        timerLayout.setAlignItems(Alignment.CENTER);
        timerLayout.setSpacing(true);
        
        Div powerIndicator = new Div();
        powerIndicator.getStyle()
            .set("width", "20px")
            .set("height", "20px")
            .set("border-radius", "50%")
            .set("background-color", "#dc3545")
            .set("margin-right", "5px")
            .set("border", "2px solid #333");
            
        timerDisplay = new Div();
        timerDisplay.addClassName("timer-display");
        timerDisplay.getStyle().set("font-size", "1.2em");
        
        timerLayout.add(powerIndicator, timerDisplay);
        timerLayout.getStyle().set("margin-bottom", "1em");
        microwaveContent.add(timerLayout);

        graphic = new MicrowaveGraphic();
        microwaveContent.add(graphic);

        Button incrementButton = new Button("", e -> { service.incrementTime(); updateUI(); });
        Button startButton     = new Button("", e -> { service.start();       updateUI(); });
        Button cancelButton    = new Button("", e -> { service.cancel();     /* service.stopBeep(); */ updateUI(); });
        Button doorButton      = new Button("", e -> { service.toggleDoor(); /* service.stopBeep(); */ updateUI(); });
        powerButton           = new Button("", e -> { service.togglePower(); updateUI(); });

        incrementButton.getStyle().set("background-image", "url('/images/plus3s.png')");
        startButton.getStyle().set("background-image", "url('/images/start.png')");
        cancelButton.getStyle().set("background-image", "url('/images/cancel.png')");
        doorButton.getStyle().set("background-image", "url('/images/door.png')");
        powerButton.getStyle().set("background-image", "url('/images/power.png')");

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
        microwaveContent.add(new H2("TLA+ State Trace"));
        microwaveContent.add(verificationPanel);

        logNavigation = new HorizontalLayout();
        Button prevButton = new Button("Previous", e -> {
            if (currentLogIndex > 0) {
                isNavigatingHistory = true;
                currentLogIndex--;
                updateLogDisplay();
            }
        });
        Button nextButton = new Button("Next", e -> {
            if (currentLogIndex < allLogs.size() - 1) {
                isNavigatingHistory = true;
                currentLogIndex++;
                updateLogDisplay();
            }
        });
        Button latestButton = new Button("Latest", e -> {
            isNavigatingHistory = false;
            currentLogIndex = Math.max(0, allLogs.size() - 1);
            updateLogDisplay();
        });
        Button clearLogButton = new Button("Clear Log", e -> {
            try {
                logService.clear();
                service.logState("Initial");
                allLogs.clear();
                allLogs.addAll(service.getVerificationLog());
                currentLogIndex = 0;
                updateLogDisplay();
                Notification.show("Verification log cleared", 2_000, Position.TOP_END);
            } catch (Exception ex) {
                log.error("Failed to clear log", ex);
                Notification.show("Error clearing log: " + ex.getMessage(), 3_000, Position.TOP_END);
            }
        });
        showAllButton = new Button("Show All", e -> {
            showAllLogs = !showAllLogs;
            showAllButton.setText(showAllLogs ? "Show One" : "Show All");
            updateLogDisplay();
        });
        
        verifyBtn = new Button("Verify with TLC", e -> {
            try {
                verifyBtn.setEnabled(false);
                verifyBtn.setText("Verifying...");
                verificationPanel.setText("Verification in progress...\nPlease wait, this may take a few seconds...");
                
                new Thread(() -> {
                    try {
                        log.debug("Starting TLC verification from UI");
                        service.verifyWithTlc();
                        
                        ui.access(() -> {
                            log.debug("TLC verification completed, updating UI");
                            verifyBtn.setEnabled(true);
                            verifyBtn.setText("Verify with TLC");
                            
                            var result = service.getLastTlcResult();
                            if (result == null) {
                                Notification.show("TLC not run yet", 2_000, Position.TOP_END);
                                verificationPanel.setText("TLC verification not run yet.");
                            } else if (result.timedOut) {
                                Notification.show("⚠️ TLC verification timed out", 5_000, Position.TOP_END);
                                verificationPanel.setText("TLC VERIFICATION TIMED OUT\n\n" +
                                                        "The verification process took too long and was automatically stopped after 5 minutes.\n\n" +
                                                        "This usually happens when:\n" +
                                                        "1. Your state trace is very long\n" +
                                                        "2. The state space is too complex to explore efficiently\n\n" +
                                                        "Consider:\n" +
                                                        "- Clearing your state trace and starting with fewer actions\n" +
                                                        "- Using the direct safety check results instead:\n\n" +
                                                        result.rawOutput);
                            } else if (result.invariantHolds) {
                                Notification.show("✅ Safety properties verified!", 3_000, Position.TOP_END);
                                verificationPanel.setText("Safety verification completed successfully!\n\n" +
                                                        "The microwave behaved safely - radiation was never ON while the door was OPEN.");
                            } else {
                                boolean isLogViolation = result.rawOutput.contains("Safety violations found in execution log");
                                
                                if (isLogViolation) {
                                    Notification.show("❌ Safety violation detected in execution", 3_000, Position.TOP_END);
                                } else {
                                    Notification.show("❌ Safety violation detected in model", 3_000, Position.TOP_END);
                                }
                                
                                StringBuilder sb = new StringBuilder();
                                sb.append("SAFETY VIOLATION DETECTED!\n\n");
                                
                                sb.append("The safety property 'Safe == ~(radiation = ON /\\ door = OPEN)' was violated.\n");
                                sb.append("This means the microwave had radiation ON while the door was OPEN.\n\n");
                                
                                if (isLogViolation) {
                                    sb.append("The violation occurred in your actual execution trace:\n\n");
                                    sb.append(result.rawOutput);
                                } else if (result.traceStates != null && !result.traceStates.isEmpty()) {
                                    sb.append("Model Checking found a violation trace:\n\n");
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
                        });
                    } catch (Exception ex) {
                        log.error("TLC verification failed", ex);
                        ui.access(() -> {
                            verifyBtn.setEnabled(true);
                            verifyBtn.setText("Verify with TLC");
                            Notification.show("Error running TLC: " + ex.getMessage(), 5_000, Position.TOP_END);
                            verificationPanel.setText("Error running TLC:\n\n" + ex.getMessage() + "\n\n" +
                                                    "Stack trace:\n" + Arrays.toString(ex.getStackTrace()));
                        });
                    }
                }).start();
            } catch (Exception ex) {
                log.error("Failed to start verification thread", ex);
                verifyBtn.setEnabled(true);
                verifyBtn.setText("Verify with TLC");
                Notification.show("Error starting verification: " + ex.getMessage(), 5_000, Position.TOP_END);
                verificationPanel.setText("Error starting verification:\n\n" + ex.getMessage());
            }
        });
        logNavigation.add(prevButton, nextButton, latestButton, clearLogButton, showAllButton, verifyBtn);
        logNavigation.setSpacing(true);
        microwaveContent.add(logNavigation);

        showAllButton.addClickListener(e -> {
            verificationPanel.getStyle().set("min-height", showAllLogs ? "400px" : "100px");
        });

        mainLayout.add(leftPanel);
        mainLayout.add(microwaveContent);
        mainLayout.setFlexGrow(1, microwaveContent);
        
        add(mainLayout);
        setSizeFull();

        service.logState("Initial");
        allLogs.addAll(service.getVerificationLog());
        updateLogDisplay();

        ui.setPollInterval(1_000);
        ui.addPollListener(event -> {
            updateUI();
        });

        updateUI();
    }

    private void updateLogDisplay() {
        verificationPanel.removeAll();
        if (!allLogs.isEmpty()) {
            if (showAllLogs) {
                allLogs.forEach(log -> {
                    Div entry = new Div();
                    entry.getElement().setProperty("innerHTML", formatTlaLogEntry(log));
                    entry.getStyle()
                        .set("margin", "0.2em 0")
                        .set("font-family", "monospace")
                        .set("white-space", "pre-wrap");
                    verificationPanel.add(entry);
                });
            } else {
                if (currentLogIndex < allLogs.size()) {
                    Div entry = new Div();
                    entry.getElement().setProperty("innerHTML", formatTlaLogEntry(allLogs.get(currentLogIndex)));
                    entry.getStyle()
                        .set("margin", "0.2em 0")
                        .set("font-family", "monospace")
                        .set("white-space", "pre-wrap");
                    verificationPanel.add(entry);
                }
            }
        }
    }
    
    /**
     * Format TLA+ log entries with syntax highlighting
     */
    private String formatTlaLogEntry(String logEntry) {
        // Basic syntax highlighting for TLA+ 
        String formatted = logEntry
            // Highlight comments
            .replace("\\*", "<span style='color:#008800'>\\*</span>")
            // Highlight module name and keywords
            .replace("STATE_", "<span style='color:#0000FF; font-weight: bold;'>STATE_</span>")
            .replace(" == ", " <span style='color:#0000FF; font-weight: bold;'>==</span> ")
            // Highlight state variables
            .replace("/\\ door", "/\\ <span style='color:#000088'>door</span>")
            .replace("/\\ timeRemaining", "/\\ <span style='color:#000088'>timeRemaining</span>")
            .replace("/\\ radiation", "/\\ <span style='color:#000088'>radiation</span>")
            .replace("/\\ power", "/\\ <span style='color:#000088'>power</span>")
            // Highlight string values
            .replaceAll("\"([^\"]+)\"", "<span style='color:#880000'>\"$1\"</span>");
            
        return formatted;
    }

    private void updateUI() {
        ui.access(() -> {
            MicrowaveState state = service.getState();

            graphic.getElement().setProperty("doorOpen", state.getDoor() == MicrowaveState.DoorState.OPEN);
            graphic.getElement().setProperty("heating", state.getRadiation() == MicrowaveState.RadiationState.ON);
            graphic.getElement().setProperty("time", state.getTimeRemaining());

            if (timerDisplay.getParent().isPresent() && timerDisplay.getParent().get() instanceof HorizontalLayout) {
                HorizontalLayout timerLayout = (HorizontalLayout) timerDisplay.getParent().get();
                Component powerIndicator = timerLayout.getComponentAt(0);
                if (powerIndicator instanceof Div) {
                    if (!service.isPowerButtonEnabled()) {
                        ((Div) powerIndicator).getStyle().set("display", "none");
                    } else {
                        ((Div) powerIndicator).getStyle().remove("display");
                        if (state.getPower() == MicrowaveState.PowerState.ON) {
                            ((Div) powerIndicator).getStyle().set("background-color", "#28a745");
                        } else {
                            ((Div) powerIndicator).getStyle().set("background-color", "#dc3545");
                        }
                    }
                }
            }

            if (powerButton != null) {
                if (service.isPowerButtonEnabled()) {
                    powerButton.getElement().getStyle().remove("display");
                } else {
                    powerButton.getElement().getStyle().set("display", "none");
                }
            }

            if (!service.isDangerousMode()) {
                if (state.isDoorSafetyViolated()) {
                    Notification.show("⚠️ Door Safety Violated!", 3_000, Position.TOP_END);
                }
                if (state.isRadiationSafetyViolated()) {
                    Notification.show("⚠️ Radiation Safety Violated!", 3_000, Position.TOP_END);
                }
            }

            List<String> newLogs = service.getVerificationLog();
            
            if (!newLogs.equals(allLogs)) {
                allLogs.clear();
                allLogs.addAll(newLogs);
                
                if (!isNavigatingHistory && !showAllLogs) {
                    currentLogIndex = Math.max(0, allLogs.size() - 1);
                    updateLogDisplay();
                }
            }
            
            isNavigatingHistory = false;

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
    
    /**
     * Creates the left panel with tabs for Feature Toggles and TLA+ Cheatsheet
     */
    private VerticalLayout createLeftPanel() {
        VerticalLayout leftPanel = new VerticalLayout();
        leftPanel.setPadding(false);
        leftPanel.setSpacing(false);
        leftPanel.setWidth("350px");
        leftPanel.getStyle()
            .set("border-right", "1px solid #dee2e6")
            .set("height", "100%")
            .set("overflow-y", "auto");
        
        // Create tab components
        Tab featuresTab = new Tab("Features");
        Tab guideTab = new Tab("TLA+ Guide");
        
        // Create tabs and set full width
        leftPanelTabs = new Tabs(featuresTab, guideTab);
        leftPanelTabs.setWidthFull();
        
        // Create content container
        leftPanelContent = new Div();
        leftPanelContent.setWidthFull();
        leftPanelContent.getStyle().set("height", "100%");
        
        // Create the content components
        FeatureTogglesPanel featureToggles = new FeatureTogglesPanel(service);
        TlaCheatsheetPanel tlaCheatsheet = new TlaCheatsheetPanel();
        
        // Initially show the features panel
        featureToggles.setVisible(true);
        tlaCheatsheet.setVisible(false);
        
        leftPanelContent.add(featureToggles, tlaCheatsheet);
        
        // Add tab change listener
        leftPanelTabs.addSelectedChangeListener(event -> {
            // Hide all content
            leftPanelContent.getChildren().forEach(component -> component.setVisible(false));
            
            // Show the selected content
            if (event.getSelectedTab().equals(featuresTab)) {
                featureToggles.setVisible(true);
            } else {
                tlaCheatsheet.setVisible(true);
            }
        });
        
        leftPanel.add(leftPanelTabs, leftPanelContent);
        return leftPanel;
    }
}
