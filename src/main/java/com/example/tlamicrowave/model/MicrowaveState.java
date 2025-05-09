package com.example.tlamicrowave.model;

import org.springframework.stereotype.Component;

import lombok.Data;

@Data
@Component
public class MicrowaveState {

    public enum DoorState { OPEN, CLOSED }
    public enum RadiationState { OFF, ON }
    public enum BeepState { OFF, ON }

    private static final int MAX_TIME = 60;

    private DoorState door = DoorState.CLOSED;
    private RadiationState radiation = RadiationState.OFF;
    private BeepState beep = BeepState.OFF;
    private int timeRemaining = 0;

    public boolean canIncrementTime() {
        return radiation == RadiationState.OFF && timeRemaining < MAX_TIME;
    }

    public boolean canStart() {
        return radiation == RadiationState.OFF && timeRemaining > 0 && door == DoorState.CLOSED;
    }

    public void incrementTime() {
        if (canIncrementTime()) {
            timeRemaining += 3;
            if (timeRemaining > MAX_TIME) {
                timeRemaining = MAX_TIME;
            }
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
        beep = BeepState.OFF;
    }

    public void tick() {
        if (radiation == RadiationState.ON && timeRemaining > 0) {
            timeRemaining--;
            if (timeRemaining == 0) {
                radiation = RadiationState.OFF;
                beep = BeepState.ON;
            }
        }
    }

    public void openDoor() {
        door = DoorState.OPEN;
        radiation = RadiationState.OFF;
        beep = BeepState.OFF;
    }

    public void closeDoor() {
        door = DoorState.CLOSED;
    }

    public DoorState getDoor() {
        return door;
    }

    public RadiationState getRadiation() {
        return radiation;
    }

    public int getTimeRemaining() {
        return timeRemaining;
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

    public boolean isBeepSafetyViolated() {
        return beep == BeepState.ON && (timeRemaining > 0 || radiation == RadiationState.ON);
    }

    public boolean isRadiationSafetyViolated() {
        return radiation == RadiationState.ON && (timeRemaining == 0 || beep == BeepState.ON);
    }

    public boolean isDoorStateSafetyViolated() {
        return radiation == RadiationState.ON && door == DoorState.OPEN;
    }

    public BeepState getBeep() {
        return beep;
    }

    public void stopBeep() {
        beep = BeepState.OFF;
    }
} 