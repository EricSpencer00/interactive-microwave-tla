package com.example.microwave.service;

import org.springframework.stereotype.Service;
import java.io.*;

@Service
public class TlaSpecService {

    // Use the system's temporary directory for writing spec files.
    private static final String TMP_DIR = System.getProperty("java.io.tmpdir");

    // Validates the TLA+ spec by writing it to a file and running TLC.
    public boolean validateSpec(String spec) {
        try {
            File specFile = new File(TMP_DIR, "MicrowaveSpec.tla");
            try (FileWriter writer = new FileWriter(specFile)) {
                writer.write(spec);
            }
            
            // Generate a minimal config file for TLC.
            File cfgFile = new File(TMP_DIR, "MicrowaveSpec.cfg");
            try (FileWriter writer = new FileWriter(cfgFile)) {
                writer.write("INIT Init\n");
                writer.write("NEXT Next\n");
            }
            
            // Run the TLC model checker. (Ensure TLC is installed and available in your system PATH.)
            ProcessBuilder pb = new ProcessBuilder("tlc", specFile.getAbsolutePath());
            pb.directory(new File(TMP_DIR));
            Process process = pb.start();
            BufferedReader reader = new BufferedReader(new InputStreamReader(process.getInputStream()));
            String line;
            boolean success = false;
            while ((line = reader.readLine()) != null) {
                System.out.println(line);
                // A simple detection: if the output mentions "No error", we consider it valid.
                if (line.contains("No error")) {
                    success = true;
                }
            }
            process.waitFor();
            return success;
        } catch (IOException | InterruptedException e) {
            e.printStackTrace();
            return false;
        }
    }

    // A stub method to simulate validating an FSM transition against the spec.
    public String testFSMTransition(String transition) {
        // In a complete integration, you would parse TLC output or even re-load the FSM rules from the spec.
        if ("startCooking".equals(transition)) {
            return "Transition allowed: idle -> cooking";
        } else {
            return "Transition not recognized.";
        }
    }
}
