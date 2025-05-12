package com.example.tlamicrowave;

import com.vaadin.flow.component.dependency.CssImport;
import com.vaadin.flow.component.page.AppShellConfigurator;
import com.vaadin.flow.component.page.Push;
import org.springframework.stereotype.Component;

@Component
@Push
@CssImport("./styles/styles.css")    // tell Vaadin to bundle your CSS
public class AppShellConfig implements AppShellConfigurator {
} 