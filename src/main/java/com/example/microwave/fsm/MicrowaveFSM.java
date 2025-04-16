package com.example.microwave.fsm;

public class MicrowaveFSM {
    
    public enum State {
        IDLE,
        COOKING,
        PAUSED,
        DOOR_OPEN
    }
    
    private State state;
    private int timer; // timer in seconds
    private boolean lightOn;
    private boolean radiationOn;
    
    public MicrowaveFSM() {
        state = State.IDLE;
        timer = 0;
        lightOn = false;
        radiationOn = false;
    }
    
    public String openDoor() {
        if (state == State.DOOR_OPEN) {
            return "Door is already open.";
        }
        // Opening the door stops cooking and turns off radiation, but turns on light.
        state = State.DOOR_OPEN;
        radiationOn = false;
        lightOn = true;
        return "Door opened: Light is on, Radiation off.";
    }
    
    public String closeDoor() {
        if (state != State.DOOR_OPEN) {
            return "Door is already closed.";
        }
        // Closing the door: if there is a pending timer value, state becomes PAUSED.
        lightOn = false;
        if (timer > 0) {
            state = State.PAUSED;
            return "Door closed: Timer is paused.";
        } else {
            state = State.IDLE;
            return "Door closed: Microwave is idle.";
        }
    }
    
    public String addTime(int seconds) {
        timer += seconds;
        return "Added " + seconds + " seconds. Timer is now " + timer + " seconds.";
    }
    
    public String startCooking() {
        if (state == State.DOOR_OPEN) {
            return "Cannot start cooking: Door is open.";
        }
        if (timer <= 0) {
            return "No time on the clock. Please add time.";
        }
        state = State.COOKING;
        radiationOn = true;
        lightOn = false;
        return "Cooking started: Radiation on.";
    }
    
    public String stopClock() {
        if (state != State.COOKING) {
            return "Microwave is not actively cooking.";
        }
        state = State.PAUSED;
        radiationOn = false;
        return "Cooking paused: Radiation off.";
    }
    
    public String resetClock() {
        timer = 0;
        if (state == State.COOKING || state == State.PAUSED) {
            state = State.IDLE;
            radiationOn = false;
        }
        return "Timer reset. Microwave is idle.";
    }
    
    // Simulate one tick (one second decrement) if cooking.
    public String tick() {
        if (state == State.COOKING) {
            if (timer > 0) {
                timer--;
                if (timer == 0) {
                    state = State.IDLE;
                    radiationOn = false;
                    return "Timer finished: BEEP! Cooking complete.";
                }
                return "Tick: Timer is now " + timer + " seconds.";
            } else {
                state = State.IDLE;
                radiationOn = false;
                return "Timer finished: BEEP! Cooking complete.";
            }
        }
        return "No active cooking. Timer remains " + timer + " seconds.";
    }
    
    // Getters for UI display:
    public State getState() { return state; }
    public int getTimer() { return timer; }
    public boolean isLightOn() { return lightOn; }
    public boolean isRadiationOn() { return radiationOn; }
}
