package com.example.tlamicrowave.ui;

import com.example.tlamicrowave.model.MicrowaveState;
import com.example.tlamicrowave.service.MicrowaveService;
import com.vaadin.flow.component.button.Button;
import com.vaadin.flow.component.html.Div;
import com.vaadin.flow.component.html.H2;
import com.vaadin.flow.component.orderedlayout.VerticalLayout;
import com.vaadin.flow.router.Route;
import jakarta.annotation.security.PermitAll;
import org.springframework.beans.factory.annotation.Autowired;
import com.vaadin.flow.component.UI;

@Route("")
@PermitAll
public class MicrowaveView extends VerticalLayout {
    private final MicrowaveService service;
    private final Div display;
    private final Div verificationPanel;
    private final UI ui;

    @Autowired
    public MicrowaveView(MicrowaveService service) {
        this.service = service;
        this.ui = UI.getCurrent();
        service.setUI(ui);
        setSizeFull();
        setAlignItems(Alignment.CENTER);
        setJustifyContentMode(JustifyContentMode.CENTER);

        // Microwave display
        display = new Div();
        display.addClassName("microwave-display");
        display.getStyle().set("font-size", "2em");
        display.getStyle().set("padding", "1em");
        display.getStyle().set("border", "2px solid #ccc");
        display.getStyle().set("border-radius", "10px");
        display.getStyle().set("background", "#f5f5f5");
        display.getStyle().set("min-width", "200px");
        display.getStyle().set("text-align", "center");

        // Control buttons
        Button incrementButton = new Button("+1s");
        Button startButton = new Button("Start");
        Button cancelButton = new Button("Cancel");
        Button doorButton = new Button("Open/Close Door");
        Button tickButton = new Button("Tick");

        // Verification panel
        verificationPanel = new Div();
        verificationPanel.addClassName("verification-panel");
        verificationPanel.getStyle().set("margin-top", "2em");
        verificationPanel.getStyle().set("padding", "1em");
        verificationPanel.getStyle().set("border", "1px solid #ddd");
        verificationPanel.getStyle().set("border-radius", "5px");
        verificationPanel.getStyle().set("max-height", "200px");
        verificationPanel.getStyle().set("overflow-y", "auto");

        // Add components
        add(display);
        add(new VerticalLayout(incrementButton, startButton, cancelButton, doorButton, tickButton));
        add(new H2("TLC Verification Output"));
        add(verificationPanel);

        // Add button click listeners
        incrementButton.addClickListener(e -> {
            service.incrementTime();
            updateUI();
        });

        startButton.addClickListener(e -> {
            service.start();
            updateUI();
        });

        cancelButton.addClickListener(e -> {
            service.cancel();
            updateUI();
        });

        doorButton.addClickListener(e -> {
            service.toggleDoor();
            updateUI();
        });

        tickButton.addClickListener(e -> {
            service.manualTick();
            updateUI();
        });

        // Initial UI update
        updateUI();
    }

    private void updateUI() {
        ui.access(() -> {
            MicrowaveState state = service.getState();
            
            // Update display
            String displayText = String.format("%02d", state.getTimeRemaining());
            if (state.getDoor() == MicrowaveState.DoorState.OPEN) {
                displayText += " DOOR OPEN";
            }
            if (state.getRadiation() == MicrowaveState.RadiationState.ON) {
                displayText += " HEATING";
            }
            display.setText(displayText);

            // Update verification panel
            verificationPanel.removeAll();
            service.getVerificationLog().forEach(log -> {
                Div logEntry = new Div(log);
                logEntry.getStyle().set("margin", "0.2em 0");
                verificationPanel.add(logEntry);
            });
        });
    }
} 