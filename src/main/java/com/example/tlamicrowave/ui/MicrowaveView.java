package com.example.tlamicrowave.ui;

import com.example.tlamicrowave.model.MicrowaveState;
import com.example.tlamicrowave.service.MicrowaveService;
import com.vaadin.flow.component.UI;
import com.vaadin.flow.component.button.Button;
import com.vaadin.flow.component.dependency.JsModule;
import com.vaadin.flow.component.html.Div;
import com.vaadin.flow.component.html.H2;
import com.vaadin.flow.component.notification.Notification;
import com.vaadin.flow.component.notification.Notification.Position;
import com.vaadin.flow.component.orderedlayout.VerticalLayout;
import com.vaadin.flow.router.Route;
import jakarta.annotation.security.PermitAll;
import org.springframework.beans.factory.annotation.Autowired;
import java.time.LocalTime;
import java.time.format.DateTimeFormatter;

@Route("")
@PermitAll
@JsModule("./microwave-graphic.ts")
public class MicrowaveView extends VerticalLayout {
    private final MicrowaveService service;
    private final Div timerDisplay;
    private final Div verificationPanel;
    private final UI ui;
    private final MicrowaveGraphic graphic;

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

        // 2) Microwave graphic
        graphic = new MicrowaveGraphic();

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
        add(graphic);
        add(new VerticalLayout(incrementButton, startButton, cancelButton, doorButton, tickButton, stopBeepButton));
        add(new H2("TLC Verification Output"));
        add(verificationPanel);

        // Enable server-side polling
        ui.setPollInterval(1_000);
        ui.addPollListener(event -> {
            timerDisplay.setText(LocalTime.now().format(DateTimeFormatter.ofPattern("HH:mm:ss")));
            updateUI();
        });

        // initial render
        updateUI();
    }

    private void updateUI() {
        ui.access(() -> {
            MicrowaveState state = service.getState();

            // Update microwave graphic
            graphic.getElement().setProperty("doorOpen", state.getDoor() == MicrowaveState.DoorState.OPEN);
            graphic.getElement().setProperty("heating", state.getRadiation() == MicrowaveState.RadiationState.ON);
            graphic.getElement().setProperty("beeping", state.getBeep() == MicrowaveState.BeepState.ON);
            graphic.getElement().setProperty("time", state.getTimeRemaining());

            // Check safety violations
            if (state.isDoorSafetyViolated()) {
                Notification.show("⚠️ Door Safety Violated!", 3_000, Position.TOP_END);
            }
            if (state.isBeepSafetyViolated()) {
                Notification.show("⚠️ Beep Safety Violated!", 3_000, Position.TOP_END);
            }
            if (state.isRadiationSafetyViolated()) {
                Notification.show("⚠️ Radiation Safety Violated!", 3_000, Position.TOP_END);
            }

            // Update verification log
            verificationPanel.removeAll();
            service.getVerificationLog().forEach(log -> {
                Div entry = new Div(log);
                entry.getStyle().set("margin", "0.2em 0");
                verificationPanel.add(entry);
            });
        });
    }
}
