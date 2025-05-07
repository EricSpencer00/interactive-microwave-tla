package com.example.microwave.ui;

import com.example.microwave.fsm.MicrowaveFSM;
import com.example.microwave.service.TlaSpecService;
import com.vaadin.flow.component.button.Button;
import com.vaadin.flow.component.button.ButtonVariant;
import com.vaadin.flow.component.dialog.Dialog;
import com.vaadin.flow.component.html.Div;
import com.vaadin.flow.component.html.Span;
import com.vaadin.flow.component.notification.Notification;
import com.vaadin.flow.component.orderedlayout.FlexComponent.Alignment;
import com.vaadin.flow.component.orderedlayout.FlexComponent.JustifyContentMode;
import com.vaadin.flow.component.orderedlayout.HorizontalLayout;
import com.vaadin.flow.component.orderedlayout.VerticalLayout;
import com.vaadin.flow.component.textfield.TextArea;

/**
 * Customer‑facing microwave control panel:
 * - Graphic on left
 * - Status labels beneath graphic
 * - TLA Check box under status
 * - Controls + "Verify Trace" on right
 */
public class MicrowaveControlView extends HorizontalLayout {
    private final MicrowaveFSM microwaveFSM;
    private final TlaSpecService tlaSpecService;

    public MicrowaveControlView(TlaSpecService tlaSpecService) {
        this.tlaSpecService = tlaSpecService;
        this.microwaveFSM = new MicrowaveFSM();

        setSizeFull();
        setPadding(true);
        setSpacing(true);
        setAlignItems(Alignment.START);

        // --- Left panel: microwave + status + TLA ---
        VerticalLayout left = new VerticalLayout();
        left.setWidth("65%");
        left.setAlignItems(Alignment.CENTER);
        left.setSpacing(true);

        // Graphic
        Div graphic = buildMicrowaveGraphic();
        left.add(graphic);

        // Status labels
        Span stateLabel = new Span();
        Span timerLabel = new Span();
        Span lightLabel = new Span();
        Span radLabel = new Span();
        updateStatus(stateLabel, timerLabel, lightLabel, radLabel);
        left.add(stateLabel, timerLabel, lightLabel, radLabel);

        // TLA+ check box
        Div tlaBox = new Div();
        tlaBox.getStyle().set("border", "2px solid #FFA500");
        tlaBox.getStyle().set("padding", "0.5rem");
        tlaBox.getStyle().set("width", "100%");
        Span tlaTitle = new Span("TLA+ Check:");
        Span tlaOutput = new Span("(waiting...)");
        tlaOutput.getStyle().set("white-space", "pre-wrap");
        tlaBox.add(tlaTitle, tlaOutput);
        left.add(tlaBox);

        // --- Right panel: controls + verify ---
        VerticalLayout right = new VerticalLayout();
        right.setWidth("35%");
        right.setAlignItems(Alignment.STRETCH);
        right.setJustifyContentMode(JustifyContentMode.START);
        right.setSpacing(true);

        // Control buttons
        Button add10 = new Button("+10s", e -> performAction(
            "IncTime", microwaveFSM.addTime(10),
            stateLabel, timerLabel, lightLabel, radLabel, tlaOutput
        ));
        add10.addThemeVariants(ButtonVariant.LUMO_PRIMARY);

        Button start = new Button("Start", e -> performAction(
            "Start", microwaveFSM.startCooking(),
            stateLabel, timerLabel, lightLabel, radLabel, tlaOutput
        ));
        start.addThemeVariants(ButtonVariant.LUMO_SUCCESS);

        Button pause = new Button("Pause", e -> performAction(
            "Pause", microwaveFSM.stopClock(),
            stateLabel, timerLabel, lightLabel, radLabel, tlaOutput
        ));
        pause.addThemeVariants(ButtonVariant.LUMO_CONTRAST);

        Button tick = new Button("Tick", e -> performAction(
            "Tick", microwaveFSM.tick(),
            stateLabel, timerLabel, lightLabel, radLabel, tlaOutput
        ));

        Button reset = new Button("Reset", e -> performAction(
            "Cancel", microwaveFSM.resetClock(),
            stateLabel, timerLabel, lightLabel, radLabel, tlaOutput
        ));
        reset.addThemeVariants(ButtonVariant.LUMO_ERROR);

        // Verify trace with full model-check
        Button verify = new Button("Verify Trace", e -> {
            String full = tlaSpecService.runTLC(
                tlaSpecService.loadDefaultSpec(),
                tlaSpecService.loadDefaultCfg()
            );
            Dialog dlg = new Dialog();
            TextArea area = new TextArea("Full TLA+ Output", full);
            area.setWidth("600px");
            area.setHeight("400px");
            dlg.add(area);
            dlg.open();
        });
        verify.addThemeVariants(ButtonVariant.LUMO_SUCCESS);

        right.add(add10, start, pause, tick, reset, verify);

        add(left, right);
    }

    private void performAction(
        String tlaAction,
        String message,
        Span stateLabel,
        Span timerLabel,
        Span lightLabel,
        Span radLabel,
        Span tlaOutput
    ) {
        Notification.show(message);
        String out = tlaSpecService.validateTransition(tlaAction, microwaveFSM);
        tlaOutput.setText(out);
        updateStatus(stateLabel, timerLabel, lightLabel, radLabel);
    }

    private void updateStatus(
        Span stateLabel,
        Span timerLabel,
        Span lightLabel,
        Span radLabel
    ) {
        stateLabel.setText("State: " + microwaveFSM.getState());
        int t = microwaveFSM.getTimer();
        timerLabel.setText(String.format("Timer: %02d:%02d", t / 60, t % 60));
        lightLabel.setText("Light: " + (microwaveFSM.isLightOn() ? "On" : "Off"));
        radLabel.setText("Radiation: " + (microwaveFSM.isRadiationOn() ? "On" : "Off"));
    }

    private Div buildMicrowaveGraphic() {
        Div wrapper = new Div();
        wrapper.getStyle().set("position", "relative");
        wrapper.getStyle().set("width", "300px");
        wrapper.getStyle().set("height", "200px");
        wrapper.getStyle().set("background", "#fff");
        wrapper.getStyle().set("border", "2px solid #FFA500");
        wrapper.getStyle().set("border-radius", "8px");
        wrapper.getStyle().set("box-shadow", "2px 2px 8px rgba(0,0,0,0.1)");

        Div door = new Div();
        door.getStyle().set("width", "200px");
        door.getStyle().set("height", "140px");
        door.getStyle().set("background", "#e0e0e0");
        door.getStyle().set("border", "2px solid #ccc");
        door.getStyle().set("border-radius", "6px");
        door.getStyle().set("position", "absolute");
        door.getStyle().set("top", "30px");
        door.getStyle().set("left", "50px");
        door.getStyle().set("transition", "transform 0.3s ease");

        wrapper.add(door);
        return wrapper;
    }
}
