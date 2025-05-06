package com.example.microwave;

import com.vaadin.flow.component.button.Button;
import com.vaadin.flow.component.html.Div;
import com.vaadin.flow.component.html.H2;
import com.vaadin.flow.component.orderedlayout.VerticalLayout;
import com.vaadin.flow.router.Route;
import com.vaadin.flow.theme.lumo.LumoUtility;

@Route("")
public class MicrowaveView extends VerticalLayout {
    private final MicrowaveController controller;
    private final Div display;
    private final Div door;
    private final Div keypad;

    public MicrowaveView() {
        controller = new MicrowaveController();
        
        // Main container
        setWidth("600px");
        setHeight("800px");
        addClassName("microwave-container");
        
        // Title
        H2 title = new H2("Interactive Microwave");
        title.addClassName(LumoUtility.TextAlignment.CENTER);
        add(title);

        // Display
        display = new Div();
        display.addClassName("microwave-display");
        display.setText("00:00");
        add(display);

        // Door
        door = new Div();
        door.addClassName("microwave-door");
        door.setText("DOOR");
        add(door);

        // Keypad
        keypad = new Div();
        keypad.addClassName("microwave-keypad");
        createKeypad();
        add(keypad);

        // Initialize state
        updateDisplay();
    }

    private void createKeypad() {
        // Number buttons
        for (int i = 1; i <= 9; i++) {
            Button button = new Button(String.valueOf(i));
            button.addClassName("number-button");
            final int number = i;
            button.addClickListener(e -> {
                controller.pressNumber(number);
                updateDisplay();
            });
            keypad.add(button);
        }

        // Zero button
        Button zeroButton = new Button("0");
        zeroButton.addClassName("number-button");
        zeroButton.addClickListener(e -> {
            controller.pressNumber(0);
            updateDisplay();
        });
        keypad.add(zeroButton);

        // Control buttons
        Button startButton = new Button("Start");
        startButton.addClassName("control-button");
        startButton.addClickListener(e -> {
            controller.start();
            updateDisplay();
        });
        keypad.add(startButton);

        Button stopButton = new Button("Stop");
        stopButton.addClassName("control-button");
        stopButton.addClickListener(e -> {
            controller.stop();
            updateDisplay();
        });
        keypad.add(stopButton);

        Button doorButton = new Button("Door");
        doorButton.addClassName("control-button");
        doorButton.addClickListener(e -> {
            controller.toggleDoor();
            updateDisplay();
        });
        keypad.add(doorButton);
    }

    private void updateDisplay() {
        display.setText(controller.getDisplayTime());
        door.setText(controller.isDoorOpen() ? "DOOR OPEN" : "DOOR");
        door.addClassName(controller.isDoorOpen() ? "door-open" : "door-closed");
    }
} 