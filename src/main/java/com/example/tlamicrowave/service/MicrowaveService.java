// MicrowaveService.java
package com.example.tlamicrowave.service;

import com.example.tlamicrowave.model.MicrowaveState;
import com.vaadin.flow.component.UI;
import org.springframework.scheduling.annotation.Scheduled;
import org.springframework.stereotype.Service;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import java.util.ArrayList;
import java.util.List;
import org.springframework.beans.factory.annotation.Autowired;
import lombok.extern.slf4j.Slf4j;

@Slf4j
@Service
public class MicrowaveService {
    private static final Logger log = LoggerFactory.getLogger(MicrowaveService.class);
    private final MicrowaveState state = new MicrowaveState();
    private final List<String> verificationLog = new ArrayList<>();
    private UI ui;

    @Autowired
    private TlcIntegrationService tlcService;

    private TlcIntegrationService.TlcResult lastTlcResult;

    public void setUI(UI ui) { this.ui = ui; }

    @Scheduled(fixedRate=1000)
    public void tick() {
        if (state.getPower()==MicrowaveState.PowerState.ON && state.getRadiation()==MicrowaveState.RadiationState.ON) {
            state.tick();
            logState("Tick");
            pushUpdate();
        }
    }

    public void incrementTime() { applyAction("IncrementTime", state::incrementTime, state::canIncrementTime, "time + 3"); }
    public void start()         { applyAction("Start",        state::start,         state::canStart,        "radiation = ON"); }
    public void cancel()        { applyAction("Cancel",       state::cancel,        ()->true,               "time = 0"); }
    public void toggleDoor()    { applyAction(state.getDoor()==MicrowaveState.DoorState.OPEN?"CloseDoor":"OpenDoor",
                                                        ()->{ if(state.getDoor()==MicrowaveState.DoorState.OPEN) state.closeDoor(); else state.openDoor(); },
                                                        ()->true, "door toggled"); }
    public void togglePower()   { applyAction("TogglePower",  state::togglePower,   ()->true,               "power toggled"); }

    private void applyAction(String name, Runnable action, java.util.function.BooleanSupplier guard, String detail) {
        if (guard.getAsBoolean()) { action.run(); logState(name); }
        else                    { verificationLog.add(name+" Violation Attempt"); }
        pushUpdate();
    }

    public synchronized void logState(String action) {
        StringBuilder b = new StringBuilder();
        if (verificationLog.isEmpty()) {
            b.append("---- MODULE Microwave ----\n")
             .append("EXTENDS Integers, TLC\n\n")
             .append("VARIABLES door, time, radiation, power\n\n")
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
             .append("Next == Init \\/ TogglePower \\/ IncrementTime \\/ Start \\/ Tick \\/ Cancel\n\n")
             .append("Spec == Init /\\ [][Next]_<<door,time,radiation,power>>\n\n")
             .append("====\n");
        }
        b.append("(* State: ").append(action).append(" *)\n");
        b.append("/\\ door = ").append(state.getDoor()).append("\n");
        b.append("/\\ time = ").append(state.getTimeRemaining()).append("\n");
        b.append("/\\ radiation = ").append(state.getRadiation()).append("\n");
        b.append("/\\ power = ").append(state.getPower()).append("\n\n");
        verificationLog.add(b.toString());
        log.debug(b.toString());
    }

    private void pushUpdate() {
        if (ui!=null) ui.access(() -> ui.push());
    }

    public List<String> getVerificationLog() {
        return new ArrayList<>(verificationLog);
    }

    public MicrowaveState getState() { return state; }

    @Scheduled(fixedRate = 1000)
    public void verifyWithTlc() {
        try {
            tlcService.generateSpecFile();
            tlcService.generateConfigFile();
            lastTlcResult = tlcService.runTlc();
        } catch (Exception e) {
            log.error("TLC integration failed", e);
        }
    }

    public TlcIntegrationService.TlcResult getLastTlcResult() {
        return lastTlcResult;
    }
}
