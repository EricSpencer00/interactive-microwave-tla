package com.microwave.dream.service;

import com.microwave.dream.model.*;
import java.util.*;

public class MicrowaveService {
    private static final int MAX_TIME = 99;
    private MicrowaveState state;
    private List<MicrowaveTraceEntry> trace;

    public MicrowaveService() {
        this.state = new MicrowaveState(MicrowaveState.Door.CLOSED, MicrowaveState.Power.OFF, 0, MicrowaveState.Light.OFF);
        this.trace = new ArrayList<>();
    }

    public MicrowaveState getState() {
        return state;
    }

    public List<MicrowaveTraceEntry> getTrace() {
        return trace;
    }

    public void resetTrace() {
        trace.clear();
    }

    public boolean processEvent(MicrowaveEvent event, Integer param) {
        MicrowaveState newState = computeNextState(state, event, param);
        // TODO: Validate with TLA+ (call TLC)
        if (newState != null) {
            state = newState;
            trace.add(new MicrowaveTraceEntry(event, state, param));
            return true;
        }
        return false;
    }

    private MicrowaveState computeNextState(MicrowaveState s, MicrowaveEvent event, Integer param) {
        switch (event) {
            case OPEN_DOOR:
                if (s.getDoor() == MicrowaveState.Door.CLOSED) {
                    return new MicrowaveState(MicrowaveState.Door.OPEN, s.getPower(), s.getTimer(), MicrowaveState.Light.ON);
                }
                break;
            case CLOSE_DOOR:
                if (s.getDoor() == MicrowaveState.Door.OPEN) {
                    return new MicrowaveState(MicrowaveState.Door.CLOSED, s.getPower(), s.getTimer(), (s.getTimer() > 0) ? MicrowaveState.Light.ON : MicrowaveState.Light.OFF);
                }
                break;
            case SET_POWER_LOW:
                return new MicrowaveState(s.getDoor(), MicrowaveState.Power.LOW, s.getTimer(), s.getLight());
            case SET_POWER_HIGH:
                return new MicrowaveState(s.getDoor(), MicrowaveState.Power.HIGH, s.getTimer(), s.getLight());
            case SET_TIMER:
                if (param != null && param > 0 && param <= MAX_TIME) {
                    return new MicrowaveState(s.getDoor(), s.getPower(), param, s.getLight());
                }
                break;
            case START:
                if (s.getDoor() == MicrowaveState.Door.CLOSED && s.getTimer() > 0 && s.getPower() != MicrowaveState.Power.OFF) {
                    return new MicrowaveState(s.getDoor(), s.getPower(), s.getTimer(), MicrowaveState.Light.ON);
                }
                break;
            case STOP:
                return new MicrowaveState(s.getDoor(), s.getPower(), s.getTimer(), (s.getTimer() > 0) ? MicrowaveState.Light.ON : MicrowaveState.Light.OFF);
            case TICK:
                if (s.getTimer() > 0) {
                    int newTimer = s.getTimer() - 1;
                    MicrowaveState.Light newLight = (newTimer == 0) ? MicrowaveState.Light.OFF : s.getLight();
                    return new MicrowaveState(s.getDoor(), s.getPower(), newTimer, newLight);
                }
                break;
        }
        return null; // Invalid transition
    }
} 