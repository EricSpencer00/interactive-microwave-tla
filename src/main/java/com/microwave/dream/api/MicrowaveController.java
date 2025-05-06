package com.microwave.dream.api;

import java.util.List;

import org.springframework.web.bind.annotation.GetMapping;
import org.springframework.web.bind.annotation.PostMapping;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RequestParam;
import org.springframework.web.bind.annotation.RestController;

import com.microwave.dream.model.MicrowaveEvent;
import com.microwave.dream.model.MicrowaveState;
import com.microwave.dream.model.MicrowaveTraceEntry;
import com.microwave.dream.service.MicrowaveService;

@RestController
@RequestMapping("/api/microwave")
public class MicrowaveController {
    private final MicrowaveService service = new MicrowaveService();

    @GetMapping("/state")
    public MicrowaveState getState() {
        return service.getState();
    }

    @PostMapping("/event")
    public boolean processEvent(@RequestParam MicrowaveEvent event, @RequestParam(required = false) Integer param) {
        return service.processEvent(event, param);
    }

    @GetMapping("/trace")
    public List<MicrowaveTraceEntry> getTrace() {
        return service.getTrace();
    }

    @PostMapping("/trace/reset")
    public void resetTrace() {
        service.resetTrace();
    }

    // TODO: Add endpoint to upload a trace and check it against the TLA+ spec
} 