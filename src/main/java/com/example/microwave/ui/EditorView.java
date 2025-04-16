package com.example.microwave.ui;

import com.vaadin.flow.component.button.Button;
import com.vaadin.flow.component.notification.Notification;
import com.vaadin.flow.component.orderedlayout.VerticalLayout;
import com.vaadin.flow.component.textfield.TextArea;
import com.vaadin.flow.router.Route;
import com.example.microwave.service.TlaSpecService;

@Route("")
public class EditorView extends VerticalLayout {

    private final TlaSpecService tlaSpecService;
    
    public EditorView(TlaSpecService tlaSpecService) {
        this.tlaSpecService = tlaSpecService;
        
        // TLA+ Editor (in this example, a simple TextArea)
        TextArea tlaEditor = new TextArea("Edit TLA+ Spec");
        tlaEditor.setWidth("600px");
        tlaEditor.setHeight("300px");
        tlaEditor.setValue(loadDefaultSpec());
        
        // Button to validate the TLA+ specification using TLC
        Button validateButton = new Button("Validate Spec", event -> {
            boolean valid = tlaSpecService.validateSpec(tlaEditor.getValue());
            String message = valid ? "Spec is valid!" : "Spec errors detected.";
            Notification.show(message);
        });
        
        // Button to test a sample FSM transition against TLA+ based validation
        Button testTransitionButton = new Button("Test FSM Transition", event -> {
            String result = tlaSpecService.testFSMTransition("startCooking");
            Notification.show("FSM Transition: " + result);
        });
        
        add(tlaEditor, validateButton, testTransitionButton);
    }
    
    private String loadDefaultSpec() {
        // Default TLA+ specification; in practice, you might load this from a resource file.
        return "---- MODULE MicrowaveSpec ----\n" +
               "VARIABLES state\n\n" +
               "Init == state = \"idle\"\n\n" +
               "Next == \\/ (state = \"idle\" /\\ state' = \"cooking\")\n" +
               "        \\/ (state = \"cooking\" /\\ state' = \"idle\")\n\n" +
               "Spec == Init /\\ [][Next]_<<state>>\n" +
               "====";
    }
}
