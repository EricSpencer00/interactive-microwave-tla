package com.example.microwave.service;

import org.springframework.stereotype.Service;
import java.io.*;
import java.nio.file.*;
import java.util.*;

@Service
public class TlaSpecService {

    private final String JAR_PATH = "lib/tla2tools.jar"; // relative to project root or adjust if needed

    public String runTLC(String tlaSpecCode, String cfgCode) {
        try {
            // Create a temp folder
            Path tempDir = Files.createTempDirectory("tla-run");
            File tlaFile = tempDir.resolve("MicrowaveSpec.tla").toFile();
            File cfgFile = tempDir.resolve("MicrowaveSpec.cfg").toFile();

            // Write .tla
            try (FileWriter writer = new FileWriter(tlaFile)) {
                writer.write(tlaSpecCode);
            }

            // Write .cfg
            try (FileWriter writer = new FileWriter(cfgFile)) {
                writer.write(cfgCode);
            }

            // Build the TLC process
            List<String> command = Arrays.asList(
                "java", "-cp", JAR_PATH, "tlc2.TLC", tlaFile.getAbsolutePath()
            );

            ProcessBuilder pb = new ProcessBuilder(command);
            pb.directory(tempDir.toFile());
            pb.redirectErrorStream(true);

            Process process = pb.start();

            // Read the output
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
