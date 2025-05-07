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
    private final MicrowaveState state;
    private final List<String> verificationLog = new ArrayList<>();
    private UI ui;

    public void setUI(UI ui) {
        this.ui = ui;
    }

    @Scheduled(fixedRate = 1000)
    public void tick() {
        logger.debug("Scheduled tick running, radiation state: {}", state.getRadiation());
        if (state.getRadiation() == MicrowaveState.RadiationState.ON) {
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
            pushUpdate();
        }
    }

    public void start() {
        if (state.canStart()) {
            state.start();
            logState("Start");
            pushUpdate();
        }
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

    private void logState(String action) {
        String log = String.format("%s: (door=%s, time=%d, radiation=%s)",
                action,
                state.getDoor(),
                state.getTimeRemaining(),
                state.getRadiation());
        logger.debug("State change: {}", log);
        verificationLog.add(log);
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
} 