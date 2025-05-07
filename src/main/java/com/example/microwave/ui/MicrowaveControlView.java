package com.example.microwave.ui;

import java.util.ArrayList;
import java.util.List;
import java.util.Timer;
import java.util.TimerTask;

import com.example.microwave.fsm.MicrowaveFSM;
import com.example.microwave.service.TlaSpecService;
import com.vaadin.flow.component.UI;
import com.vaadin.flow.component.button.Button;
import com.vaadin.flow.component.html.Div;
import com.vaadin.flow.component.html.Image;
import com.vaadin.flow.component.html.Span;
import com.vaadin.flow.component.orderedlayout.FlexComponent.Alignment;
import com.vaadin.flow.component.orderedlayout.FlexComponent.JustifyContentMode;
import com.vaadin.flow.component.orderedlayout.HorizontalLayout;
import com.vaadin.flow.component.orderedlayout.VerticalLayout;
import com.vaadin.flow.component.textfield.TextArea;

/**
 * MicrowaveControlView now uses distinct images for each state:
 * closed_off, closed_on, open_off, open_on.
 * Clicking the oven toggles the door; cooking animation is shown by the image names.
 */
public class MicrowaveControlView extends VerticalLayout {
    private final MicrowaveFSM fsm;
    private final TlaSpecService tla;
    private final TextArea tlaCheck;
    private final TextArea fullTla;
    private Image ovenImage;
    private Div timerDisplay;
    private Timer autoTick;
    private List<Trace> trace = new ArrayList<>();

    public MicrowaveControlView(TlaSpecService tla) {
        this.fsm = new MicrowaveFSM();
        this.tla = tla;

        setWidthFull();
        setDefaultHorizontalComponentAlignment(Alignment.CENTER);
        setPadding(true);
        setSpacing(true);

        // Safety/Liveness labels
        HorizontalLayout tags = new HorizontalLayout(
            styledLabel("Safety: door=OPEN ⇒ rad=OFF", "#FFA726"),
            styledLabel("Liveness: ON ⇒ OFF", "#FFF176"),
            styledLabel("Safety: rad=ON ⇒ door=CLOSED", "#FFA726")
        );
        tags.setJustifyContentMode(JustifyContentMode.CENTER);
        tags.setSpacing(true);
        add(tags);

        // Oven image placeholder
        ovenImage = new Image(getImageSource(), "Microwave");
        ovenImage.setWidth("400px");
        ovenImage.setHeight("250px");
        ovenImage.addClickListener(e -> toggleDoor());
        add(ovenImage);

        // Timer display
        timerDisplay = new Div();
        timerDisplay.getStyle()
            .set("background", "#333").set("color", "#FFF")
            .set("padding", "4px 8px").set("borderRadius", "4px")
            .set("fontSize", "1.2rem");
        add(timerDisplay);

        // Controls
        HorizontalLayout ctrls = new HorizontalLayout();
        ctrls.setJustifyContentMode(JustifyContentMode.CENTER);
        ctrls.setSpacing(true);
        ctrls.add(
            createBtn("+10s", () -> perform("IncTime", fsm.addTime(10))),
            createBtn("Start", () -> perform("Start", fsm.startCooking())),
            createBtn("Pause", () -> perform("Cancel", fsm.stopClock())),
            createBtn("Reset", () -> perform("Cancel", fsm.resetClock()))
        );
        add(ctrls);

        // TLC output panel
        tlaCheck = new TextArea("TLC Check");
        tlaCheck.setWidth("80%");
        tlaCheck.setReadOnly(true);
        add(tlaCheck);
        fullTla = new TextArea("Full TLC Output");
        fullTla.setWidth("80%");
        fullTla.setReadOnly(true);
        fullTla.setVisible(false);
        add(fullTla);

        // Initialize view
        updateView();
    }

    private void toggleDoor() {
        if (fsm.getState() == MicrowaveFSM.State.DOOR_OPEN) {
            perform("CloseDoor", fsm.closeDoor());
        } else {
            perform("OpenDoor", fsm.openDoor());
        }
    }

    private void perform(String action, String msg) {
        trace.add(new Trace(fsm.getState(), fsm.getTimer(), action));
        String out = tla.validateTransition(action, fsm);
        tlaCheck.setValue(out);
        fullTla.setValue(out);
        fullTla.setVisible(false);
        scheduleTick();
        updateView();
    }

    private void scheduleTick() {
        if (autoTick != null) autoTick.cancel();
        if (fsm.getState() == MicrowaveFSM.State.COOKING && fsm.getTimer() > 0) {
            autoTick = new Timer();
            autoTick.scheduleAtFixedRate(new TimerTask() {
                public void run() {
                    UI.getCurrent().access(() -> perform("Tick", fsm.tick()));
                }
            }, 1000, 1000);
        }
    }

    private void updateView() {
        ovenImage.setSrc(getImageSource());
        int t = fsm.getTimer();
        timerDisplay.setText(String.format("%02d:%02d", t/60, t%60));
    }

    private String getImageSource() {
        String door = (fsm.getState() == MicrowaveFSM.State.DOOR_OPEN) ? "open" : "closed";
        String rad  = fsm.isRadiationOn() ? "on" : "off";
        return "frontend/images/microwave_" + door + "_" + rad + ".png";
    }

    private Span styledLabel(String txt, String bg) {
        Span s = new Span(txt);
        s.getStyle()
         .set("background", bg)
         .set("color", "#000")
         .set("padding", "6px")
         .set("borderRadius", "4px")
         .set("white-space", "pre");
        return s;
    }

    private Button createBtn(String text, Runnable action) {
        Button b = new Button(text, e -> action.run());
        b.getStyle()
         .set("background", "#FFA726")
         .set("color", "#FFF")
         .set("border", "none")
         .set("borderRadius", "4px")
         .set("padding", "0.5rem 1rem");
        return b;
    }

    private static class Trace {
        Trace(MicrowaveFSM.State s, int t, String a) {}
    }
}
