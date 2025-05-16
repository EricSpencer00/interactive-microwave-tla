package com.example.tlamicrowave.ui;

import com.example.tlamicrowave.service.MicrowaveService;
import com.vaadin.flow.component.checkbox.Checkbox;
import com.vaadin.flow.component.html.Div;
import com.vaadin.flow.component.html.H3;
import com.vaadin.flow.component.orderedlayout.VerticalLayout;

/**
 * A panel that allows toggling various features of the microwave.
 * This is designed to be modular so new features can be easily added.
 */
public class FeatureTogglesPanel extends VerticalLayout {
    private final MicrowaveService service;
    
    public FeatureTogglesPanel(MicrowaveService service) {
        this.service = service;
        
        setWidth("250px");
        setPadding(true);
        setSpacing(true);
        
        getStyle()
            .set("background-color", "#f8f9fa")
            .set("border-right", "1px solid #dee2e6")
            .set("box-shadow", "2px 0 5px rgba(0,0,0,0.1)")
            .set("z-index", "100")
            .set("height", "100%");
            
        H3 title = new H3("Feature Toggles");
        title.getStyle()
            .set("margin-top", "0")
            .set("color", "#495057")
            .set("font-size", "1.2em");
            
        add(title);
        
        // Add separator
        Div separator = new Div();
        separator.getStyle()
            .set("width", "100%")
            .set("height", "1px")
            .set("background-color", "#dee2e6")
            .set("margin", "8px 0");
        add(separator);
        
        // Add power button toggle
        Checkbox powerButtonToggle = new Checkbox("Power Button");
        powerButtonToggle.setValue(true); // Default to enabled
        powerButtonToggle.addValueChangeListener(e -> {
            boolean enabled = e.getValue();
            service.setPowerButtonEnabled(enabled);
        });
        styleToggle(powerButtonToggle);
        
        // Add dangerous mode toggle
        Checkbox dangerousModeToggle = new Checkbox("⚠️ Dangerous Mode");
        dangerousModeToggle.setValue(false); // Default to disabled
        dangerousModeToggle.addValueChangeListener(e -> {
            boolean dangerous = e.getValue();
            service.setDangerousMode(dangerous);
        });
        styleToggle(dangerousModeToggle);
        
        add(powerButtonToggle, dangerousModeToggle);
    }
    
    private void styleToggle(Checkbox toggle) {
        toggle.getStyle()
            .set("margin", "8px 0")
            .set("padding", "8px")
            .set("background-color", "#ffffff")
            .set("border-radius", "4px")
            .set("border", "1px solid #ced4da")
            .set("width", "100%");
    }
} 