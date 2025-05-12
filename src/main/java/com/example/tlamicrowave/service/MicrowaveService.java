package com.example.tlamicrowave.service;

import com.example.tlamicrowave.model.MicrowaveState;
import com.vaadin.flow.component.UI;
import lombok.RequiredArgsConstructor;
import org.springframework.scheduling.annotation.Scheduled;
import org.springframework.stereotype.Service;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.ArrayList;
import java.util.List;

@Service
@RequiredArgsConstructor
public class MicrowaveService {
    private static final Logger logger = LoggerFactory.getLogger(MicrowaveService.class);
    private final MicrowaveState state = new MicrowaveState();
    private final List<String> verificationLog = new ArrayList<>();
    private UI ui;

    public void setUI(UI ui) {
        this.ui = ui;
    }

    @Scheduled(fixedRate = 1000)
    public void tick() {
        logger.debug("Scheduled tick running, radiation state: {}", state.getRadiation());
        if (state.getPower() == MicrowaveState.PowerState.ON && state.getRadiation() == MicrowaveState.RadiationState.ON) {
            logger.debug("Executing tick, current time: {}", state.getTimeRemaining());
            state.tick();
            logState("Tick");
            if (ui != null) {
                ui.access(() -> {
                    logger.debug("Pushing UI update after tick");
                    ui.push();
                });
            }
        }
    }

    public void incrementTime() {
        if (state.canIncrementTime()) {
            state.incrementTime();
            logState("IncrementTime");
        } else {
            logState("IncrementTime Violation Attempt");
        }
        pushUpdate();
    }

    public void start() {
        if (state.canStart()) {
            state.start();
            logState("Start");
        } else {
            logState("Start Violation Attempt");
        }
        pushUpdate();
    }

    public void cancel() {
        state.cancel();
        logState("Cancel");
        pushUpdate();
    }

    public void toggleDoor() {
        if (state.getDoor() == MicrowaveState.DoorState.OPEN) {
            state.closeDoor();
            logState("CloseDoor");
        } else {
            state.openDoor();
            logState("OpenDoor");
        }
        pushUpdate();
    }

    public void manualTick() {
        state.manualTick();
        logState("ManualTick");
        pushUpdate();
    }

    public void togglePower() {
        state.togglePower();
        logState("TogglePower");
        pushUpdate();
    }

    private void logState(String action) {
        StringBuilder log = new StringBuilder();
        log.append("State: ").append(action).append("\n");
        log.append("/\\ door = ").append(state.getDoor()).append("\n");
        log.append("/\\ time = ").append(state.getTimeRemaining()).append("\n");
        log.append("/\\ radiation = ").append(state.getRadiation()).append("\n");
        log.append("/\\ power = ").append(state.getPower()).append("\n");
        // log.append("/\\ beep = ").append(state.getBeep()).append("\n");
        
        // Check safety properties
        if (state.isDoorSafetyViolated()) {
            log.append("/\\ [VIOLATION] ~(door = CLOSED => radiation = OFF)\n");
        }
        if (state.isBeepSafetyViolated()) {
            log.append("/\\ [VIOLATION] ~(beep = ON => time = 0)\n");
        }
        if (state.isRadiationSafetyViolated()) {
            log.append("/\\ [VIOLATION] ~(radiation = ON => door = CLOSED)\n");
        }
        if (state.isDoorStateSafetyViolated()) {
            log.append("/\\ [VIOLATION] ~(door = OPEN => radiation = OFF)\n");
        }
        // Power safety: nothing should be on if power is OFF
        if (state.getPower() == MicrowaveState.PowerState.OFF && (state.getRadiation() == MicrowaveState.RadiationState.ON || state.getTimeRemaining() > 0)) {
            log.append("/\\ [VIOLATION] ~(power = OFF => radiation = OFF ∧ time = 0)\n");
        }
  
        
        logger.debug("State change: {}", log);
        verificationLog.add(log.toString());
    }

    private void pushUpdate() {
        if (ui != null) {
            ui.access(() -> {
                logger.debug("Pushing UI update");
                ui.push();
            });
        }
    }

    public List<String> getVerificationLog() {
        return new ArrayList<>(verificationLog);
    }

    public MicrowaveState getState() {
        return state;
    }

    public MicrowaveState.PowerState getPower() { 
        return state.getPower(); 
    }

    // public void stopBeep() {
    //     state.stopBeep();
    //     pushUpdate();
    // }
} 