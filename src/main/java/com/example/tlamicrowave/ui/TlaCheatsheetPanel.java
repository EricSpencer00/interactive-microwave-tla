package com.example.tlamicrowave.ui;

import com.vaadin.flow.component.Html;
import com.vaadin.flow.component.accordion.Accordion;
import com.vaadin.flow.component.accordion.AccordionPanel;
import com.vaadin.flow.component.html.Div;
import com.vaadin.flow.component.html.H3;
import com.vaadin.flow.component.html.Span;
import com.vaadin.flow.component.orderedlayout.VerticalLayout;
import com.vaadin.flow.component.tabs.Tab;
import com.vaadin.flow.component.tabs.Tabs;

/**
 * A panel that displays a TLA+ cheatsheet and tutorial for the microwave.
 */
public class TlaCheatsheetPanel extends VerticalLayout {
    
    private final Tabs tabs;
    private final Div content;
    
    public TlaCheatsheetPanel() {
        // Remove fixed width so it can be responsive
        setMinWidth("350px");
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
            
        H3 title = new H3("TLA+ Guide");
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
        
        // Create tabs for Tutorial and Cheatsheet
        Tab tutorialTab = new Tab("Tutorial");
        Tab cheatsheetTab = new Tab("TLA+ Cheatsheet");
        
        tabs = new Tabs(tutorialTab, cheatsheetTab);
        tabs.setWidthFull();
        
        content = new Div();
        content.setWidthFull();
        
        // Create the content for the Tutorial tab
        Div tutorialContent = createTutorialContent();
        tutorialContent.setVisible(true);
        
        // Create the content for the Cheatsheet tab
        Div cheatsheetContent = createCheatsheetContent();
        cheatsheetContent.setVisible(false);
        
        content.add(tutorialContent, cheatsheetContent);
        
        tabs.addSelectedChangeListener(event -> {
            // Hide all content
            content.getChildren().forEach(component -> component.setVisible(false));
            
            // Show the selected content
            if (event.getSelectedTab().equals(tutorialTab)) {
                tutorialContent.setVisible(true);
            } else {
                cheatsheetContent.setVisible(true);
            }
        });
        
        add(tabs, content);
    }
    
    private Div createTutorialContent() {
        Div tutorialDiv = new Div();
        tutorialDiv.getStyle()
            .set("padding", "16px 0");
        tutorialDiv.setWidthFull();
        
        Accordion accordion = new Accordion();
        accordion.setWidthFull();
        
        // Introduction
        AccordionPanel introPanel = accordion.add("Introduction",
            new Html("<div style='max-width: 100%; word-wrap: break-word;'>" +
                "<p>This interactive microwave demonstrates formal verification using TLA+.</p>" +
                "<p>The microwave state is continuously checked against safety properties.</p>" +
                "</div>"));
        
        // How to Use
        AccordionPanel howToUsePanel = accordion.add("How to Use",
            new Html("<div style='max-width: 100%; word-wrap: break-word;'>" +
                "<ol>" +
                "<li><b>Power Button</b>: Turn the microwave on/off</li>" +
                "<li><b>+3s Button</b>: Add 3 seconds to cooking time</li>" +
                "<li><b>Start Button</b>: Begin cooking</li>" +
                "<li><b>Door Button</b>: Open/close the microwave door</li>" +
                "<li><b>Cancel Button</b>: Stop cooking and reset timer</li>" +
                "</ol>" +
                "</div>"));
        
        // Feature Toggles
        AccordionPanel togglesPanel = accordion.add("Feature Toggles",
            new Html("<div style='max-width: 100%; word-wrap: break-word;'>" +
                "<ul>" +
                "<li><b>Power Button Toggle</b>: Enable/disable the power button</li>" +
                "<li><b>Dangerous Mode</b>: Allow safety violations (radiation with door open)</li>" +
                "</ul>" +
                "</div>"));
        
        // Safety Properties
        AccordionPanel safetyPanel = accordion.add("Safety Properties",
            new Html("<div style='max-width: 100%; word-wrap: break-word;'>" +
                "<p>The main safety property is: <code>Safe == ~(radiation = ON /\\ door = OPEN)</code></p>" +
                "<p>This ensures radiation cannot be on while the door is open.</p>" +
                "</div>"));
        
        // Verification
        AccordionPanel verificationPanel = accordion.add("Verification",
            new Html("<div style='max-width: 100%; word-wrap: break-word;'>" +
                "<p>Click the \"Verify with TLC\" button to check if your actions violated any safety properties.</p>" +
                "<p>The TLA+ specification adapts based on enabled features.</p>" +
                "</div>"));
        
        // Try This
        AccordionPanel tryThisPanel = accordion.add("Try This",
            new Html("<div style='max-width: 100%; word-wrap: break-word;'>" +
                "<ol>" +
                "<li>Set time, start cooking, then open door (radiation should stop)</li>" +
                "<li>Enable dangerous mode, then try the same sequence (radiation can stay on!)</li>" +
                "<li>Disable power button to see simplified TLA+ specification</li>" +
                "<li>Click \"Verify with TLC\" to check safety properties</li>" +
                "</ol>" +
                "</div>"));
        
        accordion.open(0); // Open the first panel by default
        tutorialDiv.add(accordion);
        
        return tutorialDiv;
    }
    
    private Div createCheatsheetContent() {
        Div cheatsheetDiv = new Div();
        cheatsheetDiv.getStyle()
            .set("padding", "16px 0");
        cheatsheetDiv.setWidthFull();
        
        Accordion accordion = new Accordion();
        accordion.setWidthFull();
        
        // Basic Syntax
        AccordionPanel basicSyntaxPanel = accordion.add("Basic Syntax",
            new Html("<div style='font-family: monospace; word-wrap: break-word; max-width: 100%;'>" +
                "<p><b>Module Declaration:</b><br>" +
                "<code>---- MODULE ModuleName ----</code></p>" +
                "<p><b>Imports:</b><br>" +
                "<code>EXTENDS Integers, Sequences</code></p>" +
                "<p><b>Variables:</b><br>" +
                "<code>VARIABLES x, y, z</code></p>" +
                "<p><b>Constants:</b><br>" +
                "<code>CONSTANTS C1, C2</code></p>" +
                "<p><b>Module End:</b><br>" +
                "<code>====</code></p>" +
                "</div>"));
        
        // Operators
        AccordionPanel operatorsPanel = accordion.add("Operators",
            new Html("<div style='font-family: monospace; word-wrap: break-word; max-width: 100%;'>" +
                "<p><b>Logical:</b><br>" +
                "<code>/\\ (and), \\/ (or), ~ (not), => (implies)</code></p>" +
                "<p><b>Equality:</b><br>" +
                "<code>= (equals), # (not equals)</code></p>" +
                "<p><b>Temporal:</b><br>" +
                "<code>[]P (always P), &lt;&gt;P (eventually P)</code></p>" +
                "<p><b>Primed Variables:</b><br>" +
                "<code>x' (value of x in next state)</code></p>" +
                "</div>"));
        
        // State Predicates
        AccordionPanel statePredicatesPanel = accordion.add("State Predicates",
            new Html("<div style='font-family: monospace; word-wrap: break-word; max-width: 100%;'>" +
                "<p><b>Init Predicate:</b><br>" +
                "<code>Init == x = 0 /\\ y = FALSE</code></p>" +
                "<p><b>Next-State Relation:</b><br>" +
                "<code>Next == x' = x + 1 /\\ y' = TRUE</code></p>" +
                "<p><b>Unchanged Variables:</b><br>" +
                "<code>UNCHANGED &lt;&lt;x, y&gt;&gt;</code></p>" +
                "</div>"));
        
        // Specifications
        AccordionPanel specificationsPanel = accordion.add("Specifications",
            new Html("<div style='font-family: monospace; word-wrap: break-word; max-width: 100%;'>" +
                "<p><b>Safety Property:</b><br>" +
                "<code>Safe == x > 0 => y = TRUE</code></p>" +
                "<p><b>Liveness Property:</b><br>" +
                "<code>Live == &lt;&gt;(x > 10)</code></p>" +
                "<p><b>Complete Spec:</b><br>" +
                "<code>Spec == Init /\\ [][Next]_vars</code></p>" +
                "</div>"));
        
        // Microwave Example
        AccordionPanel microwaveExamplePanel = accordion.add("Microwave Example",
            new Html("<div style='font-family: monospace; word-wrap: break-word; max-width: 100%;'>" +
                "<p><b>Variables:</b><br>" +
                "<code>VARIABLES door, time, radiation, power</code></p>" +
                "<p><b>Constants:</b><br>" +
                "<code>CONSTANTS OPEN, CLOSED, ON, OFF</code></p>" +
                "<p><b>Safety Property:</b><br>" +
                "<code>Safe == ~(radiation = ON /\\ door = OPEN)</code></p>" +
                "<p><b>Action Example:</b><br>" +
                "<code>OpenDoor ==<br>" +
                "/\\ door = CLOSED<br>" +
                "/\\ door' = OPEN<br>" +
                "/\\ radiation' = OFF<br>" +
                "/\\ UNCHANGED &lt;&lt;time, power&gt;&gt;</code></p>" +
                "</div>"));
        
        // TLC Commands
        AccordionPanel tlcCommandsPanel = accordion.add("TLC Commands",
            new Html("<div style='font-family: monospace; word-wrap: break-word; max-width: 100%;'>" +
                "<p><b>Run TLC:</b><br>" +
                "<code>tlc ModuleName</code></p>" +
                "<p><b>Config File:</b><br>" +
                "<code>SPECIFICATION Spec<br>" +
                "INVARIANT Safe<br>" +
                "PROPERTY Live</code></p>" +
                "</div>"));
        
        accordion.open(0); // Open the first panel by default
        cheatsheetDiv.add(accordion);
        
        return cheatsheetDiv;
    }
} 