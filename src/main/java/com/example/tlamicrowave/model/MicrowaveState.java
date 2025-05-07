package com.example.tlamicrowave.model;

import org.springframework.stereotype.Component;

import lombok.Data;

@Data
@Component
public class MicrowaveState {

    public enum DoorState { OPEN, CLOSED }
    public enum RadiationState { OFF, ON }

    private static final int MAX_TIME = 60;

    private DoorState door = DoorState.CLOSED;
    private RadiationState radiation = RadiationState.OFF;
    private int timeRemaining = 0;

    public boolean canIncrementTime() {
        return radiation == RadiationState.OFF && timeRemaining < MAX_TIME;
    }

    public boolean canStart() {
        return radiation == RadiationState.OFF && timeRemaining > 0 && door == DoorState.CLOSED;
    }

    public void incrementTime() {
        if (canIncrementTime()) {
            timeRemaining++;
        }
    }

    public void start() {
        if (canStart()) {
            radiation = RadiationState.ON;
        }
    }

    public void cancel() {
        radiation = RadiationState.OFF;
        timeRemaining = 0;
    }

    public void tick() {
        if (radiation == RadiationState.ON && timeRemaining > 0) {
            timeRemaining--;
            if (timeRemaining == 0) {
                radiation = RadiationState.OFF;
            }
        }
    }

    public void openDoor() {
        door = DoorState.OPEN;
        radiation = RadiationState.OFF;
    }

    public void closeDoor() {
        door = DoorState.CLOSED;
    }

    public void manualTick() {
        if (timeRemaining > 0) {
            timeRemaining--;
            if (timeRemaining == 0) {
                radiation = RadiationState.OFF;
            }
        }
    }

    public boolean isDoorSafetyViolated() {
        return door == DoorState.OPEN && radiation == RadiationState.ON;
    }
} 