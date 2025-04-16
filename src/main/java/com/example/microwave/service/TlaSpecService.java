package com.example.microwave.service;

import org.springframework.stereotype.Service;
import java.io.*;
import java.nio.file.*;
import java.util.*;

@Service
public class TlaSpecService {

    // 🔧 Dynamically resolve tla2tools.jar relative to app root
    private final String JAR_PATH = Paths.get("lib", "tla2tools.jar").toAbsolutePath().toString();

    public String runTLC(String tlaSpecCode, String cfgCode) {
        try {
            // ⏱️ Create temp dir for .tla and .cfg
            Path tempDir = Files.createTempDirectory("tla-run");
            File tlaFile = tempDir.resolve("MicrowaveSpec.tla").toFile();
            File cfgFile = tempDir.resolve("MicrowaveSpec.cfg").toFile();

            try (FileWriter writer = new FileWriter(tlaFile)) {
                writer.write(tlaSpecCode);
            }
            try (FileWriter writer = new FileWriter(cfgFile)) {
                writer.write(cfgCode);
            }

            List<String> command = Arrays.asList(
                "java", "-cp", JAR_PATH, "tlc2.TLC", tlaFile.getAbsolutePath()
            );

            System.out.println("Running: " + String.join(" ", command)); // 🪵 Debug

            ProcessBuilder pb = new ProcessBuilder(command);
            pb.directory(tempDir.toFile());
            pb.redirectErrorStream(true);

            Process process = pb.start();

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
