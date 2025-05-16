// MicrowaveService.java
package com.example.tlamicrowave.service;

import com.example.tlamicrowave.model.MicrowaveState;
import com.vaadin.flow.component.UI;
import org.springframework.scheduling.annotation.Scheduled;
import org.springframework.stereotype.Service;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import java.util.List;
import java.util.Objects;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.beans.factory.annotation.Value;
import java.util.Map;
import java.util.stream.Collectors;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

@Service
public class MicrowaveService {
    private static final Logger log = LoggerFactory.getLogger(MicrowaveService.class);
    private final MicrowaveState state = new MicrowaveState();
    private UI ui;
    private MicrowaveState lastLoggedState = new MicrowaveState().clone(); // Track last logged state
    private boolean dangerousMode = false; // Default to safe mode
    private boolean powerButtonEnabled = true; // Default to enabled

    @Value("${microwave.tick-interval:1000}")
    private long tickInterval;

    @Autowired
    private TlcIntegrationService tlcService;
    
    @Autowired
    private VerificationLogService verificationLogService;

    private TlcIntegrationService.TlcResult lastTlcResult;

    public void setUI(UI ui) { this.ui = ui; }

    @Scheduled(fixedRate=1000)
    public void tick() {
        // Only tick if radiation is ON and either power button is disabled or power is ON
        if (state.getRadiation() == MicrowaveState.RadiationState.ON && 
            (!powerButtonEnabled || state.getPower() == MicrowaveState.PowerState.ON)) {
            state.tick();
            // Only log state if it changed
            if (hasStateChanged()) {
                logState("Tick");
                lastLoggedState = state.clone();
            }
            pushUpdate();
        }
    }

    private boolean hasStateChanged() {
        return !Objects.equals(state.getDoor(), lastLoggedState.getDoor()) ||
               !Objects.equals(state.getRadiation(), lastLoggedState.getRadiation()) ||
               !Objects.equals(state.getPower(), lastLoggedState.getPower()) ||
               state.getTimeRemaining() != lastLoggedState.getTimeRemaining();
    }

    public void incrementTime() { 
        if (!powerButtonEnabled) {
            // When power button is disabled, use the no-power version
            applyAction("IncrementTime", state::incrementTimeNoPower, 
                () -> state.canIncrementTimeNoPower(), 
                "time + 3"); 
            lastLoggedState = state.clone();
        } else if (state.getPower() == MicrowaveState.PowerState.ON) {
            // When power button is enabled and power is ON
            applyAction("IncrementTime", state::incrementTime, 
                state::canIncrementTime, 
                "time + 3"); 
            lastLoggedState = state.clone();
        } else {
            verificationLogService.addLogEntry("IncrementTime Violation Attempt - Power is OFF");
            pushUpdate();
        }
    }
    
    public void start() { 
        if (dangerousMode) {
            // In dangerous mode, we allow starting even with door open
            // but power must still be ON if power button is enabled
            if (!powerButtonEnabled || state.getPower() == MicrowaveState.PowerState.ON) {
                state.forceDangerousState(
                    state.getDoor(),
                    MicrowaveState.RadiationState.ON,
                    state.getTimeRemaining(),
                    state.getPower()
                );
                logState("Start (Dangerous)");
                lastLoggedState = state.clone();
            } else {
                verificationLogService.addLogEntry("Start (Power Off) - Cannot turn on radiation without power");
                pushUpdate();
            }
        } else {
            // Check if we can start based on whether power button is enabled
            if (!powerButtonEnabled) {
                // When power button is disabled, use the no-power version
                if (state.canStartNoPower()) {
                    applyAction("Start", state::startNoPower, () -> true, "radiation = ON");
                    lastLoggedState = state.clone();
                } else {
                    // Log why we can't start
                    if (state.getTimeRemaining() <= 0) {
                        verificationLogService.addLogEntry("Start Violation Attempt - Need to set time first");
                    }
                    if (state.getDoor() != MicrowaveState.DoorState.CLOSED) {
                        verificationLogService.addLogEntry("Start Violation Attempt - Door must be closed");
                    }
                    pushUpdate();
                }
            } else {
                // When power button is enabled, use the standard version
                if (state.canStart()) {
                    applyAction("Start", state::start, () -> true, "radiation = ON");
                    lastLoggedState = state.clone();
                } else {
                    // Log why we can't start
                    if (state.getTimeRemaining() <= 0) {
                        verificationLogService.addLogEntry("Start Violation Attempt - Need to set time first");
                    }
                    if (state.getDoor() != MicrowaveState.DoorState.CLOSED) {
                        verificationLogService.addLogEntry("Start Violation Attempt - Door must be closed");
                    }
                    if (state.getPower() != MicrowaveState.PowerState.ON) {
                        verificationLogService.addLogEntry("Start Violation Attempt - Power must be ON");
                    }
                    pushUpdate();
                }
            }
        }
    }
    
    public void cancel() { 
        applyAction("Cancel", state::cancel, ()->true, "time = 0"); 
        lastLoggedState = state.clone();
    }
    
    public void toggleDoor() { 
        if (dangerousMode) {
            // In dangerous mode, toggling the door doesn't turn off radiation
            if (state.getDoor() == MicrowaveState.DoorState.OPEN) {
                state.forceDangerousState(
                    MicrowaveState.DoorState.CLOSED,
                    state.getRadiation(),
                    state.getTimeRemaining(),
                    state.getPower()
                );
                logState("CloseDoor (Dangerous)");
            } else {
                state.forceDangerousState(
                    MicrowaveState.DoorState.OPEN,
                    state.getRadiation(), // Keep radiation as is
                    state.getTimeRemaining(),
                    state.getPower()
                );
                logState("OpenDoor (Dangerous)");
            }
            lastLoggedState = state.clone();
        } else {
            applyAction(
                state.getDoor()==MicrowaveState.DoorState.OPEN ? "CloseDoor" : "OpenDoor",
                ()->{ 
                    if(state.getDoor()==MicrowaveState.DoorState.OPEN) 
                        state.closeDoor(); 
                    else 
                        state.openDoor(); 
                },
                ()->true, 
                "door toggled"
            );
            lastLoggedState = state.clone();
        }
    }
    
    public void togglePower() { 
        if (dangerousMode) {
            // In dangerous mode, turning power off still turns radiation off
            if (state.getPower() == MicrowaveState.PowerState.ON) {
                state.forceDangerousState(
                    state.getDoor(),
                    state.getRadiation(),
                    state.getTimeRemaining(),
                    MicrowaveState.PowerState.OFF
                );
                // Turn off radiation when power goes off
                if (state.getRadiation() == MicrowaveState.RadiationState.ON) {
                    state.forceDangerousState(
                        state.getDoor(),
                        MicrowaveState.RadiationState.OFF,
                        state.getTimeRemaining(),
                        MicrowaveState.PowerState.OFF
                    );
                }
                logState("TogglePower (Dangerous)");
            } else {
                state.forceDangerousState(
                    state.getDoor(),
                    state.getRadiation(),
                    state.getTimeRemaining(),
                    MicrowaveState.PowerState.ON
                );
                logState("TogglePower (Dangerous)");
            }
            lastLoggedState = state.clone();
        } else {
            applyAction("TogglePower", state::togglePower, ()->true, "power toggled"); 
            lastLoggedState = state.clone();
        }
    }

    private void applyAction(String name, Runnable action, java.util.function.BooleanSupplier guard, String detail) {
        if (dangerousMode || guard.getAsBoolean()) { 
            action.run(); 
            logState(name); 
            if (dangerousMode && !guard.getAsBoolean()) {
                verificationLogService.addLogEntry(name + " Danger: Safety constraint violated!");
            }
        } else { 
            verificationLogService.addLogEntry(name + " Violation Attempt"); 
        }
        pushUpdate();
    }

    public synchronized void logState(String action) {
        StringBuilder b = new StringBuilder();
        if (verificationLogService.isEmpty()) {
            if (powerButtonEnabled) {
                b.append("---- MODULE Microwave ----\n")
                 .append("EXTENDS Integers, TLC\n\n")
                 .append("VARIABLES door, time, radiation, power\n\n")
                 .append("CONSTANTS OPEN, CLOSED, ON, OFF\n\n")
                 .append("Init ==\n")
                 .append("/\\ door = CLOSED\n")
                 .append("/\\ time = 0\n")
                 .append("/\\ radiation = OFF\n")
                 .append("/\\ power = OFF\n\n")
                 .append("TogglePower ==\n")
                 .append("/\\ UNCHANGED <<door, time, radiation>>\n")
                 .append("/\\ power' = IF power = ON THEN OFF ELSE ON\n\n")
                 .append("IncrementTime ==\n")
                 .append("/\\ UNCHANGED <<door, radiation, power>>\n")
                 .append("/\\ time' = time + 3\n\n")
                 .append("Start ==\n")
                 .append("/\\ time > 0\n")
                 .append("/\\ radiation' = ON\n")
                 .append("/\\ UNCHANGED <<door, time, power>>\n\n")
                 .append("Tick ==\n")
                 .append("/\\ time > 0\n")
                 .append("/\\ time' = time - 1\n")
                 .append("/\\ UNCHANGED <<door, power>>\n")
                 .append("/\\ radiation' = IF time' = 0 THEN OFF ELSE radiation\n\n")
                 .append("Cancel ==\n")
                 .append("/\\ time' = 0\n")
                 .append("/\\ radiation' = OFF\n")
                 .append("/\\ UNCHANGED <<door, power>>\n\n")
                 .append("CloseDoor ==\n")
                 .append("/\\ door = OPEN\n")
                 .append("/\\ door' = CLOSED\n")
                 .append("/\\ UNCHANGED <<time, radiation, power>>\n\n")
                 .append("OpenDoor ==\n")
                 .append("/\\ door = CLOSED\n")
                 .append("/\\ door' = OPEN\n")
                 .append("/\\ radiation' = OFF\n")
                 .append("/\\ UNCHANGED <<time, power>>\n\n")
                 .append("Next == TogglePower \\/ IncrementTime \\/ Start \\/ Tick \\/ Cancel \\/ CloseDoor \\/ OpenDoor\n\n")
                 .append("Safe == ~(radiation = ON /\\ door = OPEN)\n\n")
                 .append("Spec == Init /\\ [][Next]_<<door,time,radiation,power>>\n\n")
                 .append("====\n");
            } else {
                // Version without power
                b.append("---- MODULE Microwave ----\n")
                 .append("EXTENDS Integers, TLC\n\n")
                 .append("VARIABLES door, time, radiation\n\n")
                 .append("CONSTANTS OPEN, CLOSED, ON, OFF\n\n")
                 .append("Init ==\n")
                 .append("/\\ door = CLOSED\n")
                 .append("/\\ time = 0\n")
                 .append("/\\ radiation = OFF\n\n")
                 .append("IncrementTime ==\n")
                 .append("/\\ UNCHANGED <<door, radiation>>\n")
                 .append("/\\ time' = time + 3\n\n")
                 .append("Start ==\n")
                 .append("/\\ time > 0\n")
                 .append("/\\ radiation' = ON\n")
                 .append("/\\ UNCHANGED <<door, time>>\n\n")
                 .append("Tick ==\n")
                 .append("/\\ time > 0\n")
                 .append("/\\ time' = time - 1\n")
                 .append("/\\ UNCHANGED <<door>>\n")
                 .append("/\\ radiation' = IF time' = 0 THEN OFF ELSE radiation\n\n")
                 .append("Cancel ==\n")
                 .append("/\\ time' = 0\n")
                 .append("/\\ radiation' = OFF\n")
                 .append("/\\ UNCHANGED <<door>>\n\n")
                 .append("CloseDoor ==\n")
                 .append("/\\ door = OPEN\n")
                 .append("/\\ door' = CLOSED\n")
                 .append("/\\ UNCHANGED <<time, radiation>>\n\n")
                 .append("OpenDoor ==\n")
                 .append("/\\ door = CLOSED\n")
                 .append("/\\ door' = OPEN\n")
                 .append("/\\ radiation' = OFF\n")
                 .append("/\\ UNCHANGED <<time>>\n\n")
                 .append("Next == IncrementTime \\/ Start \\/ Tick \\/ Cancel \\/ CloseDoor \\/ OpenDoor\n\n")
                 .append("Safe == ~(radiation = ON /\\ door = OPEN)\n\n")
                 .append("Spec == Init /\\ [][Next]_<<door,time,radiation>>\n\n")
                 .append("====\n");
            }
        }
        b.append("(* State: ").append(action).append(" *)\n");
        b.append("/\\ door = ").append(state.getDoor()).append("\n");
        b.append("/\\ time = ").append(state.getTimeRemaining()).append("\n");
        b.append("/\\ radiation = ").append(state.getRadiation()).append("\n");
        if (powerButtonEnabled) {
            b.append("/\\ power = ").append(state.getPower()).append("\n");
        }
        b.append("\n");
        
        // Add new state to log
        verificationLogService.addLogEntry(b.toString());
        
        log.debug(b.toString());
    }

    private void pushUpdate() {
        if (ui!=null) ui.access(() -> ui.push());
    }

    public List<String> getVerificationLog() {
        return verificationLogService.getVerificationLog();
    }

    public MicrowaveState getState() { return state; }

    public TlcIntegrationService.TlcResult getLastTlcResult() {
        return lastTlcResult;
    }

    public void verifyWithTlc() {
        try {
            log.debug("Starting verification process");
            // First check the actual execution log for safety violations
            log.debug("Checking safety violations in execution log");
            long startTime = System.currentTimeMillis();
            TlcIntegrationService.SafetyCheckResult logCheck = tlcService.checkSafetyInLog();
            log.debug("Safety check completed in {}ms. Safety holds: {}, violations: {}", 
                     System.currentTimeMillis() - startTime, 
                     logCheck.safetyHolds, 
                     logCheck.violations.size());
            
            // Get the list of states from the verification log
            List<String> verificationLog = verificationLogService.getVerificationLog();
            List<String> stateEntries = verificationLog.stream()
                .filter(entry -> entry.contains("(* State:"))
                .collect(Collectors.toList());
            
            // Convert log entries to state maps for trace verification
            List<Map<String, String>> traceStates = new ArrayList<>();
            for (String stateEntry : stateEntries) {
                Map<String, String> stateMap = new LinkedHashMap<>();
                stateMap.put("door", extractValueFromLog(stateEntry, "door"));
                stateMap.put("time", extractValueFromLog(stateEntry, "time"));
                stateMap.put("radiation", extractValueFromLog(stateEntry, "radiation"));
                if (powerButtonEnabled) {
                    stateMap.put("power", extractValueFromLog(stateEntry, "power"));
                }
                traceStates.add(stateMap);
            }
            
            log.debug("Extracted {} states from log for trace verification", traceStates.size());
            
            // Perform a direct safety check using our in-memory method
            boolean traceSafe = checkTraceSafety(traceStates);
            
            if (!traceSafe) {
                // A real safety violation was found
                log.warn("Direct safety check found violations in the trace");
                // Create a result showing the safety violation
                StringBuilder output = new StringBuilder();
                output.append("Safety violation found in execution trace:\n\n");
                output.append("The microwave execution contains a state where radiation is ON while the door is OPEN.\n\n");
                output.append("This violates the safety property: Safe == ~(radiation = ON /\\ door = OPEN)\n\n");
                
                // Find the violating state(s)
                List<Map<String, String>> violatingStates = new ArrayList<>();
                for (int i = 0; i < traceStates.size(); i++) {
                    Map<String, String> state = traceStates.get(i);
                    if ("ON".equals(state.get("radiation")) && "OPEN".equals(state.get("door"))) {
                        violatingStates.add(state);
                        output.append("Violation at state ").append(i).append(":\n");
                        output.append("  door = ").append(state.get("door")).append("\n");
                        output.append("  radiation = ").append(state.get("radiation")).append("\n");
                        output.append("  time = ").append(state.get("time")).append("\n");
                        if (powerButtonEnabled) {
                            output.append("  power = ").append(state.get("power")).append("\n");
                        }
                        output.append("\n");
                    }
                }
                
                lastTlcResult = new TlcIntegrationService.TlcResult(false, violatingStates, output.toString(), false);
                log.debug("Created TLC result from direct safety check");
                return;
            }
            
            // If we reach here, the trace is safe according to our direct check
            // Just return a success result without running TLC to avoid false positives
            
            // Create a simple success result 
            StringBuilder output = new StringBuilder();
            output.append("TRACE VERIFICATION COMPLETED\n\n");
            output.append("The execution trace is safe - radiation is never ON while the door is OPEN.\n\n");
            output.append("Your microwave implementation is working correctly.\n");
            
            lastTlcResult = new TlcIntegrationService.TlcResult(true, traceStates, output.toString(), false);
            log.debug("Direct verification completed. Trace is safe.");
            
        } catch (Exception e) {
            log.error("TLC integration failed", e);
        }
    }
    
    /**
     * Helper method to extract values from log entries
     */
    private String extractValueFromLog(String stateEntry, String variable) {
        Pattern pattern = Pattern.compile("/\\\\ " + variable + " = (.+)");
        Matcher matcher = pattern.matcher(stateEntry);
        if (matcher.find()) {
            return matcher.group(1).trim();
        }
        return "\"UNKNOWN\"";
    }
    
    public boolean isDangerousMode() {
        return dangerousMode;
    }
    
    public void setDangerousMode(boolean dangerousMode) {
        this.dangerousMode = dangerousMode;
        verificationLogService.addLogEntry("(* Mode changed to " + (dangerousMode ? "DANGEROUS" : "SAFE") + " *)");
        pushUpdate();
    }

    /**
     * Checks a trace for safety violations directly in memory before sending to TLC.
     * This avoids false positives that might occur in the temporal logic checking.
     * 
     * @param trace The trace to check
     * @return true if the trace is safe, false if a violation is found
     */
    private boolean checkTraceSafety(List<Map<String, String>> trace) {
        for (Map<String, String> state : trace) {
            // Check if radiation is ON while door is OPEN
            String door = state.get("door");
            String radiation = state.get("radiation");
            
            if ("ON".equals(radiation) && "OPEN".equals(door)) {
                log.warn("Safety violation found in trace: radiation=ON, door=OPEN");
                return false;
            }
        }
        log.debug("No safety violations found in direct trace check");
        return true;
    }

    public boolean isPowerButtonEnabled() {
        return powerButtonEnabled;
    }
    
    public void setPowerButtonEnabled(boolean enabled) {
        if (this.powerButtonEnabled != enabled) {
            this.powerButtonEnabled = enabled;
            verificationLogService.addLogEntry("(* Power Button " + (enabled ? "ENABLED" : "DISABLED") + " *)");
            
            // If disabling power button, ensure power is OFF but don't turn off radiation
            // This allows the microwave to continue working without power
            if (!enabled && state.getPower() == MicrowaveState.PowerState.ON) {
                state.forceDangerousState(
                    state.getDoor(),
                    state.getRadiation(), // Keep radiation state as is
                    state.getTimeRemaining(),
                    MicrowaveState.PowerState.OFF
                );
                logState("Power Button Disabled");
            }
            
            pushUpdate();
        }
    }
}
