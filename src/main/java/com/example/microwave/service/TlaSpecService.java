package com.example.microwave.service;

import org.springframework.stereotype.Service;
import java.io.*;
import java.nio.file.*;
import java.util.*;

@Service
public class TlaSpecService {

    // Use a relative path (resolved as absolute at runtime)
    private final String JAR_PATH = Paths.get("lib", "tla2tools.jar").toAbsolutePath().toString();

    public String runTLC(String tlaSpecCode, String cfgCode) {
        try {
            // Create a temporary directory for this run.
            Path tempDir = Files.createTempDirectory("tla-run");
            File tlaFile = tempDir.resolve("MicrowaveSpec.tla").toFile();
            File cfgFile = tempDir.resolve("MicrowaveSpec.cfg").toFile();

            // Write the TLA+ specification.
            try (FileWriter writer = new FileWriter(tlaFile)) {
                writer.write(tlaSpecCode);
            }
            
            // Write the configuration file.
            try (FileWriter writer = new FileWriter(cfgFile)) {
                writer.write(cfgCode);
            }
            
            // Build the command to run TLC.
            List<String> command = Arrays.asList(
                "java", "-cp", JAR_PATH, "tlc2.TLC", tlaFile.getAbsolutePath()
            );
            System.out.println("Running: " + String.join(" ", command)); // Debug output.
            
            ProcessBuilder pb = new ProcessBuilder(command);
            pb.directory(tempDir.toFile());
            pb.redirectErrorStream(true);
            Process process = pb.start();
            
            // Capture TLC output.
            BufferedReader reader = new BufferedReader(new InputStreamReader(process.getInputStream()));
            StringBuilder output = new StringBuilder();
            String line;
            while ((line = reader.readLine()) != null) {
                output.append(line).append("\n");
            }
            
            process.waitFor();
            return output.toString();
            
        } catch (IOException | InterruptedException e) {
            return "TLC Error: " + e.getMessage();
        }
    }
}
