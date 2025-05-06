package com.example.microwave;

public class MicrowaveController {
    private int timeInSeconds = 0;
    private boolean isRunning = false;
    private boolean isDoorOpen = false;
    private StringBuilder inputBuffer = new StringBuilder();

    public void pressNumber(int number) {
        if (!isRunning && !isDoorOpen) {
            inputBuffer.append(number);
            if (inputBuffer.length() > 4) {
                inputBuffer.delete(0, 1);
            }
            updateTimeFromBuffer();
        }
    }

    public void start() {
        if (!isDoorOpen && timeInSeconds > 0) {
            isRunning = true;
        }
    }

    public void stop() {
        isRunning = false;
        inputBuffer.setLength(0);
        timeInSeconds = 0;
    }

    public void toggleDoor() {
        isDoorOpen = !isDoorOpen;
        if (isDoorOpen) {
            isRunning = false;
        }
    }

    public String getDisplayTime() {
        if (inputBuffer.length() > 0 && !isRunning) {
            return formatTimeFromBuffer();
        }
        return formatTime(timeInSeconds);
    }

    public boolean isDoorOpen() {
        return isDoorOpen;
    }

    private void updateTimeFromBuffer() {
        if (inputBuffer.length() > 0) {
            timeInSeconds = Integer.parseInt(inputBuffer.toString());
        }
    }

    private String formatTimeFromBuffer() {
        StringBuilder display = new StringBuilder();
        int length = inputBuffer.length();
        for (int i = 0; i < 4 - length; i++) {
            display.append("0");
        }
        display.append(inputBuffer);
        return display.substring(0, 2) + ":" + display.substring(2);
    }

    private String formatTime(int seconds) {
        int minutes = seconds / 60;
        int remainingSeconds = seconds % 60;
        return String.format("%02d:%02d", minutes, remainingSeconds);
    }
} 