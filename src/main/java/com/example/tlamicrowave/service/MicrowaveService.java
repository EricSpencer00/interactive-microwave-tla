package com.example.tlamicrowave.service;

import com.example.tlamicrowave.model.MicrowaveState;
import lombok.RequiredArgsConstructor;
import org.springframework.scheduling.annotation.Scheduled;
import org.springframework.stereotype.Service;

import java.util.ArrayList;
import java.util.List;

@Service
@RequiredArgsConstructor
public class MicrowaveService {
    private final MicrowaveState state = new MicrowaveState();
    private final List<String> verificationLog = new ArrayList<>();

    @Scheduled(fixedRate = 1000)
    public void tick() {
        state.tick();
        logState("Tick");
    }

    public void incrementTime() {
        if (state.canIncrementTime()) {
            state.incrementTime();
            logState("IncrementTime");
        }
    }

    public void start() {
        if (state.canStart()) {
            state.start();
            logState("Start");
        }
    }

    public void cancel() {
        state.cancel();
        logState("Cancel");
    }

    public void toggleDoor() {
        if (state.getDoor() == MicrowaveState.DoorState.OPEN) {
            state.closeDoor();
            logState("CloseDoor");
        } else {
            state.openDoor();
            logState("OpenDoor");
        }
    }

    private void logState(String action) {
        String log = String.format("%s: (door=%s, time=%d, radiation=%s)",
                action,
                state.getDoor(),
                state.getTimeRemaining(),
                state.getRadiation());
        verificationLog.add(log);
    }

    public List<String> getVerificationLog() {
        return new ArrayList<>(verificationLog);
    }

    public MicrowaveState getState() {
        return state;
    }
} 