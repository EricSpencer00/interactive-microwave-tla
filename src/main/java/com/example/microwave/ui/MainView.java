package com.example.microwave.ui;

import com.example.microwave.service.TlaSpecService;
import com.vaadin.flow.component.tabs.Tab;
import com.vaadin.flow.component.tabs.Tabs;
import com.vaadin.flow.component.orderedlayout.VerticalLayout;
import com.vaadin.flow.router.Route;

@Route("")
public class MainView extends VerticalLayout {

    public MainView(TlaSpecService tlaSpecService) {
        // Create tabs for navigation.
        Tabs tabs = new Tabs();
        Tab microwaveTab = new Tab("Microwave Control");
        Tab tlaTab = new Tab("TLA Terminal");
        tabs.add(microwaveTab, tlaTab);
        
        // Create views for each tab.
        MicrowaveControlView microwaveControlView = new MicrowaveControlView();
        TlaTerminalView tlaTerminalView = new TlaTerminalView(tlaSpecService);
        
        // Container for pages.
        VerticalLayout pages = new VerticalLayout();
        pages.setSizeFull();
        pages.add(microwaveControlView, tlaTerminalView);
        
        // Set initial visibility.
        microwaveControlView.setVisible(true);
        tlaTerminalView.setVisible(false);
        
        // Switch views when tabs change.
        tabs.addSelectedChangeListener(event -> {
            if (tabs.getSelectedTab().equals(microwaveTab)) {
                microwaveControlView.setVisible(true);
                tlaTerminalView.setVisible(false);
            } else {
                microwaveControlView.setVisible(false);
                tlaTerminalView.setVisible(true);
            }
        });
        
        add(tabs, pages);
    }
}
