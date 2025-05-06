package com.microwave.dream.model;

public class MicrowaveState {
    public enum Door { OPEN, CLOSED }
    public enum Power { OFF, LOW, HIGH }
    public enum Light { ON, OFF }

    private Door door;
    private Power power;
    private int timer;
    private Light light;

    public MicrowaveState(Door door, Power power, int timer, Light light) {
        this.door = door;
        this.power = power;
        this.timer = timer;
        this.light = light;
    }

    public Door getDoor() { return door; }
    public Power getPower() { return power; }
    public int getTimer() { return timer; }
    public Light getLight() { return light; }

    @Override
    public String toString() {
        return String.format("MicrowaveState{door=%s, power=%s, timer=%d, light=%s}",
                door, power, timer, light);
    }
} 