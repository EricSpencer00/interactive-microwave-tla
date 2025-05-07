package com.example.tlamicrowave.ui;

import com.example.tlamicrowave.model.MicrowaveState;
import com.example.tlamicrowave.service.MicrowaveService;
import com.vaadin.flow.component.UI;
import com.vaadin.flow.component.button.Button;
import com.vaadin.flow.component.html.Div;
import com.vaadin.flow.component.html.H2;
import com.vaadin.flow.component.orderedlayout.VerticalLayout;
import com.vaadin.flow.router.Route;

import jakarta.annotation.security.PermitAll;

import org.springframework.beans.factory.annotation.Autowired;

import java.time.LocalTime;
import java.time.format.DateTimeFormatter;

import com.vaadin.flow.component.PollEvent;

@Route("")
@PermitAll
public class MicrowaveView extends VerticalLayout {
    private final MicrowaveService service;
    private final Div timerDisplay;
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

        // 1) Timer display
        timerDisplay = new Div();
        timerDisplay.addClassName("timer-display");
        timerDisplay.getStyle().set("font-size", "1.2em");
        timerDisplay.getStyle().set("margin-bottom", "1em");

        // 2) Microwave display
        display = new Div();
        display.addClassName("microwave-display");
        display.getStyle().set("font-size", "2em");
        display.getStyle().set("padding", "1em");
        display.getStyle().set("border", "2px solid #ccc");
        display.getStyle().set("border-radius", "10px");
        display.getStyle().set("background", "#f5f5f5");
        display.getStyle().set("min-width", "200px");
        display.getStyle().set("text-align", "center");

        // 3) Controls
        Button incrementButton = new Button("+1s", e -> { service.incrementTime(); updateUI(); });
        Button startButton     = new Button("Start", e -> { service.start();       updateUI(); });
        Button cancelButton    = new Button("Cancel", e -> { service.cancel();     updateUI(); });
        Button doorButton      = new Button("Open/Close Door", e -> { service.toggleDoor(); updateUI(); });
        Button tickButton      = new Button("Tick", e -> { service.manualTick();  updateUI(); });
        Button stopBeepButton  = new Button("Stop Beep", e -> { service.stopBeep(); updateUI(); });

        // 4) Verification panel
        verificationPanel = new Div();
        verificationPanel.addClassName("verification-panel");
        verificationPanel.getStyle().set("margin-top", "2em");
        verificationPanel.getStyle().set("padding", "1em");
        verificationPanel.getStyle().set("border", "1px solid #ddd");
        verificationPanel.getStyle().set("border-radius", "5px");
        verificationPanel.getStyle().set("max-height", "200px");
        verificationPanel.getStyle().set("overflow-y", "auto");

        // assemble
        add(timerDisplay);
        add(display);
        add(new VerticalLayout(incrementButton, startButton, cancelButton, doorButton, tickButton, stopBeepButton));
        add(new H2("TLC Verification Output"));
        add(verificationPanel);

        // --- new: enable server-side polling every second ---
        ui.setPollInterval(1_000);
        ui.addPollListener((PollEvent event) -> {
            // update the clock
            timerDisplay.setText(LocalTime.now()
                .format(DateTimeFormatter.ofPattern("HH:mm:ss")));
            // refresh microwave display & log
            updateUI();
        });

        // initial render
        updateUI();
    }

    private void updateUI() {
        ui.access(() -> {
            MicrowaveState state = service.getState();

            // update microwave readout
            String displayText = String.format("%02d", state.getTimeRemaining());
            if (state.getDoor() == MicrowaveState.DoorState.OPEN) {
                displayText += " DOOR OPEN";
            }
            if (state.getRadiation() == MicrowaveState.RadiationState.ON) {
                displayText += " HEATING";
            }
            if (state.getBeep() == MicrowaveState.BeepState.ON) {
                displayText += " BEEPING";
            }
            display.setText(displayText);

            // update verification log
            verificationPanel.removeAll();
            service.getVerificationLog().forEach(log -> {
                Div entry = new Div(log);
                entry.getStyle().set("margin", "0.2em 0");
                verificationPanel.add(entry);
            });
        });
    }
}
