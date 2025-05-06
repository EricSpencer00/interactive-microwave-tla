package com.microwave.dream.ui;

import java.io.ByteArrayOutputStream;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.util.List;

import org.springframework.core.ParameterizedTypeReference;
import org.springframework.http.ResponseEntity;
import org.springframework.web.client.RestTemplate;

import com.fasterxml.jackson.databind.ObjectMapper;
import com.vaadin.flow.component.button.Button;
import com.vaadin.flow.component.button.ButtonVariant;
import com.vaadin.flow.component.dialog.Dialog;
import com.vaadin.flow.component.html.Div;
import com.vaadin.flow.component.html.Span;
import com.vaadin.flow.component.notification.Notification;
import com.vaadin.flow.component.orderedlayout.HorizontalLayout;
import com.vaadin.flow.component.orderedlayout.VerticalLayout;
import com.vaadin.flow.component.textfield.TextArea;
import com.vaadin.flow.component.upload.Upload;
import com.vaadin.flow.component.upload.receivers.MemoryBuffer;
import com.vaadin.flow.router.Route;

import elemental.json.JsonObject;

@Route("")
public class MicrowaveDreamView extends VerticalLayout {
    private final RestTemplate restTemplate = new RestTemplate();
    private final String api = "/api/microwave";

    private Div microwaveDiv;
    private Div doorDiv;
    private Div handleDiv;
    private Div displayDiv;
    private Div lightDiv;
    private Div controlsDiv;
    private Span timerSpan;
    private Span powerSpan;

    public MicrowaveDreamView() {
        setWidthFull();
        setJustifyContentMode(JustifyContentMode.CENTER);
        setAlignItems(Alignment.CENTER);
        setPadding(true);

        microwaveDiv = new Div();
        microwaveDiv.addClassName("microwave");
        microwaveDiv.getStyle().set("position", "relative");
        microwaveDiv.getStyle().set("width", "400px");
        microwaveDiv.getStyle().set("height", "220px");
        microwaveDiv.getStyle().set("background", "#f0f0f0");
        microwaveDiv.getStyle().set("border", "2px solid #ccc");
        microwaveDiv.getStyle().set("border-radius", "16px");
        microwaveDiv.getStyle().set("margin", "60px auto 0 auto");
        microwaveDiv.getStyle().set("display", "flex");
        microwaveDiv.getStyle().set("flex-direction", "row");
        microwaveDiv.getStyle().set("box-shadow", "0 8px 32px 0 rgba(31, 38, 135, 0.18)");

        // Door
        doorDiv = new Div();
        doorDiv.addClassName("microwave-door");
        doorDiv.getStyle().set("width", "220px");
        doorDiv.getStyle().set("height", "180px");
        doorDiv.getStyle().set("background", "#e0e0e0");
        doorDiv.getStyle().set("border", "2px solid #aaa");
        doorDiv.getStyle().set("border-radius", "10px");
        doorDiv.getStyle().set("margin", "20px 0 0 20px");
        doorDiv.getStyle().set("position", "relative");
        doorDiv.getStyle().set("transition", "transform 0.4s cubic-bezier(.4,2,.6,1)");
        doorDiv.getStyle().set("box-shadow", "0 2px 8px 0 rgba(60,60,60,0.08)");
        doorDiv.getStyle().set("overflow", "hidden");

        // Door handle (clickable)
        handleDiv = new Div();
        handleDiv.addClassName("microwave-handle");
        handleDiv.getStyle().set("width", "16px");
        handleDiv.getStyle().set("height", "60px");
        handleDiv.getStyle().set("background", "#bbb");
        handleDiv.getStyle().set("border-radius", "8px");
        handleDiv.getStyle().set("position", "absolute");
        handleDiv.getStyle().set("right", "-18px");
        handleDiv.getStyle().set("top", "60px");
        handleDiv.getStyle().set("cursor", "pointer");
        handleDiv.getStyle().set("box-shadow", "1px 1px 4px #888");
        handleDiv.addClickListener(e -> toggleDoor());
        doorDiv.add(handleDiv);

        // Display (timer and power)
        displayDiv = new Div();
        displayDiv.addClassName("microwave-display");
        displayDiv.getStyle().set("width", "100px");
        displayDiv.getStyle().set("height", "50px");
        displayDiv.getStyle().set("background", "#181c18");
        displayDiv.getStyle().set("color", "#39ff14");
        displayDiv.getStyle().set("font-family", "'Share Tech Mono', 'Consolas', monospace");
        displayDiv.getStyle().set("font-size", "1.5em");
        displayDiv.getStyle().set("display", "flex");
        displayDiv.getStyle().set("flex-direction", "column");
        displayDiv.getStyle().set("align-items", "center");
        displayDiv.getStyle().set("justify-content", "center");
        displayDiv.getStyle().set("position", "absolute");
        displayDiv.getStyle().set("top", "20px");
        displayDiv.getStyle().set("left", "60px");
        displayDiv.getStyle().set("border-radius", "6px");
        displayDiv.getStyle().set("box-shadow", "0 0 8px 2px #222 inset");
        displayDiv.getStyle().set("border", "1.5px solid #263238");
        displayDiv.getStyle().set("letter-spacing", "2px");
        displayDiv.getStyle().set("z-index", "2");
        timerSpan = new Span();
        powerSpan = new Span();
        displayDiv.add(timerSpan, powerSpan);
        doorDiv.add(displayDiv);

        // Light indicator
        lightDiv = new Div();
        lightDiv.addClassName("microwave-light");
        lightDiv.getStyle().set("width", "20px");
        lightDiv.getStyle().set("height", "20px");
        lightDiv.getStyle().set("border-radius", "50%");
        lightDiv.getStyle().set("position", "absolute");
        lightDiv.getStyle().set("bottom", "20px");
        lightDiv.getStyle().set("left", "30px");
        doorDiv.add(lightDiv);

        // --- Controls Panel ---
        controlsDiv = new Div();
        controlsDiv.addClassName("microwave-controls");
        controlsDiv.getStyle().set("width", "120px");
        controlsDiv.getStyle().set("height", "180px");
        controlsDiv.getStyle().set("background", "#d0d0d0");
        controlsDiv.getStyle().set("border", "1.5px solid #90a4ae");
        controlsDiv.getStyle().set("border-radius", "10px");
        controlsDiv.getStyle().set("margin", "20px 0 0 20px");
        controlsDiv.getStyle().set("display", "flex");
        controlsDiv.getStyle().set("flex-direction", "column");
        controlsDiv.getStyle().set("align-items", "center");
        controlsDiv.getStyle().set("justify-content", "space-around");
        controlsDiv.getStyle().set("padding", "10px 0");

        Button powerLowButton = new Button("Power Low", e -> sendEvent("SET_POWER_LOW", null));
        Button powerHighButton = new Button("Power High", e -> sendEvent("SET_POWER_HIGH", null));
        Button setTimerButton = new Button("Set Timer 30s", e -> sendEvent("SET_TIMER", 30));
        Button startButton = new Button("Start", e -> sendEvent("START", null));
        Button stopButton = new Button("Stop", e -> sendEvent("STOP", null));
        Button tickButton = new Button("Tick", e -> sendEvent("TICK", null));
        controlsDiv.add(powerLowButton, powerHighButton, setTimerButton, startButton, stopButton, tickButton);

        microwaveDiv.add(doorDiv, controlsDiv);
        add(microwaveDiv);

        // --- Trace Export/Import Controls ---
        HorizontalLayout traceControls = new HorizontalLayout();
        Button exportTraceButton = new Button("Export Trace", e -> exportTrace());
        exportTraceButton.addThemeVariants(ButtonVariant.LUMO_PRIMARY);
        MemoryBuffer buffer = new MemoryBuffer();
        Upload upload = new Upload(buffer);
        upload.setAcceptedFileTypes(".json");
        upload.addSucceededListener(event -> {
            try {
                InputStream is = buffer.getInputStream();
                ByteArrayOutputStream baos = new ByteArrayOutputStream();
                byte[] buf = new byte[1024];
                int n;
                while ((n = is.read(buf)) > 0) {
                    baos.write(buf, 0, n);
                }
                String json = new String(baos.toByteArray(), StandardCharsets.UTF_8);
                // POST to /api/microwave/trace/upload
                ResponseEntity<String> response = restTemplate.postForEntity(api + "/trace/upload", json, String.class);
                Notification.show("Trace check result: " + response.getBody(), 5000, Notification.Position.MIDDLE);
            } catch (Exception ex) {
                Notification.show("Failed to upload trace: " + ex.getMessage(), 5000, Notification.Position.MIDDLE);
            }
        });
        traceControls.add(exportTraceButton, upload);
        add(traceControls);

        updateUI();
    }

    private void toggleDoor() {
        JsonObject state = restTemplate.getForObject(api + "/state", JsonObject.class);
        String door = state.getString("door");
        if ("CLOSED".equals(door)) {
            sendEvent("OPEN_DOOR", null);
        } else {
            sendEvent("CLOSE_DOOR", null);
        }
    }

    private void sendEvent(String event, Integer param) {
        String url = api + "/event?event=" + event + (param != null ? "&param=" + param : "");
        restTemplate.postForObject(url, null, Boolean.class);
        updateUI();
    }

    private void updateUI() {
        JsonObject state = restTemplate.getForObject(api + "/state", JsonObject.class);
        String door = state.getString("door");
        int timer = (int) state.getNumber("timer");
        String power = state.getString("power");
        String light = state.getString("light");
        // Door animation
        doorDiv.getStyle().set("transform", "CLOSED".equals(door) ? "rotateY(0deg)" : "rotateY(-60deg)");
        // Timer display
        timerSpan.setText(String.format("%02d:%02d", timer / 60, timer % 60));
        powerSpan.setText("Power: " + power);
        // Light indicator
        if ("ON".equals(light)) {
            lightDiv.getStyle().set("background", "#ff0");
            lightDiv.getStyle().set("box-shadow", "0 0 10px 4px #ff0");
        } else {
            lightDiv.getStyle().set("background", "#888");
            lightDiv.getStyle().set("box-shadow", "none");
        }
    }

    private void exportTrace() {
        try {
            ResponseEntity<List> response = restTemplate.exchange(api + "/trace", org.springframework.http.HttpMethod.GET, null, new ParameterizedTypeReference<List>() {});
            List trace = response.getBody();
            ObjectMapper mapper = new ObjectMapper();
            String json = mapper.writerWithDefaultPrettyPrinter().writeValueAsString(trace);
            Dialog dialog = new Dialog();
            dialog.setWidth("600px");
            dialog.setHeight("400px");
            TextArea textArea = new TextArea("Trace JSON");
            textArea.setWidthFull();
            textArea.setHeight("300px");
            textArea.setValue(json);
            dialog.add(textArea);
            Button closeBtn = new Button("Close", e -> dialog.close());
            dialog.add(closeBtn);
            dialog.open();
        } catch (Exception ex) {
            Notification.show("Failed to export trace: " + ex.getMessage(), 5000, Notification.Position.MIDDLE);
        }
    }
} 