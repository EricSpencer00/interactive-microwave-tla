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
        
        // Replace fixed width with min/max width for responsiveness
        setMinWidth("250px");
        setMaxWidth("100%");
        setPadding(true);
        setSpacing(true);
        
        getStyle()
            .set("background-color", "#f8f9fa")
            .set("border-right", "1px solid #dee2e6")
            .set("box-shadow", "2px 0 5px rgba(0,0,0,0.1)")
            .set("z-index", "100")
            .set("height", "100%")
            .set("overflow-y", "auto"); // Only vertical scrolling is needed
            
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
        
        // Create container for toggles 
        Div togglesContainer = new Div();
        togglesContainer.setWidthFull();
        
        // Add power button toggle
        Checkbox powerButtonToggle = new Checkbox("🔌 Power Button");
        powerButtonToggle.setValue(false); // Default to disabled
        powerButtonToggle.addValueChangeListener(e -> {
            boolean enabled = e.getValue();
            service.setPowerButtonEnabled(enabled);
        });
        powerButtonToggle.setWidthFull();
        styleToggle(powerButtonToggle);
        
        // Add dangerous mode toggle
        Checkbox dangerousModeToggle = new Checkbox("⚠️ Dangerous Mode");
        dangerousModeToggle.setValue(false); // Default to disabled
        dangerousModeToggle.addValueChangeListener(e -> {
            boolean dangerous = e.getValue();
            service.setDangerousMode(dangerous);
        });
        dangerousModeToggle.setWidthFull();
        styleToggle(dangerousModeToggle);
        
        // Add toggles to container
        togglesContainer.add(powerButtonToggle, dangerousModeToggle);
        
        add(togglesContainer);
    }
    
    private void styleToggle(Checkbox toggle) {
        toggle.getStyle()
            .set("margin", "8px 0")
            .set("padding", "8px")
            .set("background-color", "#ffffff")
            .set("border-radius", "4px")
            .set("border", "1px solid #ced4da")
            .set("display", "block") // Make checkbox take full width
            .set("overflow", "hidden") // Prevent overflow
            .set("text-overflow", "ellipsis") // Add ellipsis for text that doesn't fit
            .set("white-space", "nowrap"); // Keep text on one line
    }
} 