package com.microwave.dream.model;

public class MicrowaveTraceEntry {
    private MicrowaveEvent event;
    private MicrowaveState state;
    private Integer param; // For actions like SET_TIMER

    public MicrowaveTraceEntry(MicrowaveEvent event, MicrowaveState state, Integer param) {
        this.event = event;
        this.state = state;
        this.param = param;
    }

    public MicrowaveEvent getEvent() { return event; }
    public MicrowaveState getState() { return state; }
    public Integer getParam() { return param; }

    @Override
    public String toString() {
        return String.format("TraceEntry{event=%s, state=%s, param=%s}", event, state, param);
    }
} 