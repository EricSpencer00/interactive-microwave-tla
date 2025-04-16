package com.example.microwave.fsm;

public class MicrowaveFSM {
    
    public enum State {
        IDLE,
        DOOR_OPEN,
        COOKING
    }
    
    private State currentState;
    
    public MicrowaveFSM() {
        currentState = State.IDLE;
    }
    
    public State getCurrentState() {
        return currentState;
    }
    
    // Simulate FSM transitions based on an action.
    public String transition(String action) {
        switch (action) {
            case "openDoor":
                if (currentState == State.IDLE || currentState == State.COOKING) {
                    currentState = State.DOOR_OPEN;
                    return "Door opened";
                } else {
                    return "Invalid transition: door already open";
                }
            case "closeDoor":
                if (currentState == State.DOOR_OPEN) {
                    currentState = State.IDLE;
                    return "Door closed";
                } else {
                    return "Invalid transition: door already closed";
                }
            case "startCooking":
                if (currentState == State.IDLE) {
                    currentState = State.COOKING;
                    return "Cooking started";
                } else {
                    return "Invalid transition: cannot start cooking in current state";
                }
            case "stopCooking":
                if (currentState == State.COOKING) {
                    currentState = State.IDLE;
                    return "Cooking stopped";
                } else {
                    return "Invalid transition: not currently cooking";
                }
            default:
                return "Unknown action";
        }
    }
}
