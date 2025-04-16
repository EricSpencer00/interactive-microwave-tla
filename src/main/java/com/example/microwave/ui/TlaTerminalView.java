package com.example.microwave.ui;

import com.vaadin.flow.component.button.Button;
import com.vaadin.flow.component.textfield.TextArea;
import com.vaadin.flow.component.orderedlayout.VerticalLayout;
import com.example.microwave.service.TlaSpecService;

public class TlaTerminalView extends VerticalLayout {
    
    private final TlaSpecService tlaSpecService;
    
    public TlaTerminalView(TlaSpecService tlaSpecService) {
        this.tlaSpecService = tlaSpecService;
        
        TextArea tlaInput = new TextArea("TLA+ Spec");
        tlaInput.setWidth("800px");
        tlaInput.setHeight("300px");
        tlaInput.setValue(loadDefaultSpec());
        
        TextArea cfgInput = new TextArea("Config File");
        cfgInput.setWidth("800px");
        cfgInput.setHeight("150px");
        cfgInput.setValue("INIT Init\nNEXT Next");
        
        TextArea result = new TextArea("TLC Output");
        result.setWidth("800px");
        result.setHeight("250px");
        result.setReadOnly(true);
        
        Button runChecker = new Button("Run TLC", e -> {
            String output = tlaSpecService.runTLC(tlaInput.getValue(), cfgInput.getValue());
            result.setValue(output);
        });
        
        add(tlaInput, cfgInput, runChecker, result);
    }
    
    private String loadDefaultSpec() {
        return "---- MODULE MicrowaveSpec ----\n" +
               "VARIABLES state\n\n" +
               "Init == state = \"idle\"\n\n" +
               "Next ==\n" +
               "  \\/ /\\ state = \"idle\" /\\ state' = \"cooking\"\n" +
               "  \\/ /\\ state = \"cooking\" /\\ state' = \"idle\"\n\n" +
               "Spec == Init /\\ [][Next]_<<state>>\n====";
    }
}
