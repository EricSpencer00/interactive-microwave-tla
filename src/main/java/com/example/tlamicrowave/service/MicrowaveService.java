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
import lombok.extern.slf4j.Slf4j;
import java.util.Map;
import java.util.stream.Collectors;

@Slf4j
@Service
public class MicrowaveService {
    private static final Logger log = LoggerFactory.getLogger(MicrowaveService.class);
    private final MicrowaveState state = new MicrowaveState();
    private UI ui;
    private MicrowaveState lastLoggedState = new MicrowaveState().clone(); // Track last logged state
    private boolean dangerousMode = false; // Default to safe mode

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
        if (state.getPower()==MicrowaveState.PowerState.ON && state.getRadiation()==MicrowaveState.RadiationState.ON) {
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
        applyAction("IncrementTime", state::incrementTime, state::canIncrementTime, "time + 3"); 
        lastLoggedState = state.clone();
    }
    
    public void start() { 
        if (dangerousMode) {
            // In dangerous mode, we allow starting even with door open
            // but power must still be ON
            if (state.getPower() == MicrowaveState.PowerState.ON) {
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
            applyAction("Start", state::start, state::canStart, "radiation = ON"); 
            lastLoggedState = state.clone();
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
        }
        b.append("(* State: ").append(action).append(" *)\n");
        b.append("/\\ door = ").append(state.getDoor()).append("\n");
        b.append("/\\ time = ").append(state.getTimeRemaining()).append("\n");
        b.append("/\\ radiation = ").append(state.getRadiation()).append("\n");
        b.append("/\\ power = ").append(state.getPower()).append("\n\n");
        
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
            
            // Only run TLC if no violations in the log, to avoid model-checking errors
            if (logCheck.safetyHolds) {
                log.debug("No safety violations in log, proceeding with TLC verification");
                lastTlcResult = tlcService.runTlc();
                log.debug("TLC verification completed. Invariant holds: {}, timed out: {}", 
                         lastTlcResult.invariantHolds, lastTlcResult.timedOut);
            } else {
                log.debug("Safety violations found in log, skipping TLC verification");
                // Create a TLC result with the log violations
                StringBuilder output = new StringBuilder();
                output.append("Safety violations found in execution log:\n\n");
                
                for (TlcIntegrationService.LogViolation violation : logCheck.violations) {
                    log.debug("Violation at state {}: {}", violation.stateNum, violation.violationDesc);
                    output.append("State ").append(violation.stateNum).append(" (").append(violation.stateLabel).append("):\n");
                    output.append("  Violation: ").append(violation.violationDesc).append("\n");
                    
                    for (Map.Entry<String, String> entry : violation.state.entrySet()) {
                        output.append("  ").append(entry.getKey()).append(" = ").append(entry.getValue()).append("\n");
                    }
                    output.append("\n");
                }
                
                // Convert log violations to the standard trace format expected by UI
                List<Map<String, String>> traceStates = logCheck.violations.stream()
                    .map(v -> v.state)
                    .collect(Collectors.toList());
                
                lastTlcResult = new TlcIntegrationService.TlcResult(false, traceStates, output.toString(), false);
                log.debug("Created TLC result from log violations");
            }
        } catch (Exception e) {
            log.error("TLC integration failed", e);
        }
    }
    
    public boolean isDangerousMode() {
        return dangerousMode;
    }
    
    public void setDangerousMode(boolean dangerousMode) {
        this.dangerousMode = dangerousMode;
        verificationLogService.addLogEntry("(* Mode changed to " + (dangerousMode ? "DANGEROUS" : "SAFE") + " *)");
        pushUpdate();
    }
}
