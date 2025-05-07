package com.example.microwave.service;

import java.io.BufferedReader;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.List;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.springframework.core.io.ClassPathResource;
import org.springframework.stereotype.Service;

import com.example.microwave.fsm.MicrowaveFSM;

@Service
public class TlaSpecService {
    private static final Logger logger = LoggerFactory.getLogger(TlaSpecService.class);

    private final String JAR_PATH = Paths.get("lib", "tla2tools.jar").toAbsolutePath().toString();
    private static final String TLA_SPEC_PATH = "MicrowaveSpec.tla";
    private static final String TLA_CFG_PATH = "MicrowaveSpec.cfg";

    public String runTLC(String tlaSpecCode, String cfgCode) {
        try {
            // Create a temporary directory for this run
            Path tempDir = Files.createTempDirectory("tla-run");
            File tlaFile = tempDir.resolve(TLA_SPEC_PATH).toFile();
            File cfgFile = tempDir.resolve(TLA_CFG_PATH).toFile();

            // Write the TLA+ specification and configuration
            Files.write(tlaFile.toPath(), tlaSpecCode.getBytes());
            Files.write(cfgFile.toPath(), cfgCode.getBytes());
            
            // Build the command to run TLC
            List<String> command = Arrays.asList(
                "java", "-cp", JAR_PATH, "tlc2.TLC", tlaFile.getAbsolutePath()
            );
            logger.debug("Running TLC: {}", String.join(" ", command));
            
            ProcessBuilder pb = new ProcessBuilder(command);
            pb.directory(tempDir.toFile());
            pb.redirectErrorStream(true);
            Process process = pb.start();
            
            // Capture TLC output
            StringBuilder output = new StringBuilder();
            try (BufferedReader reader = new BufferedReader(new InputStreamReader(process.getInputStream()))) {
                String line;
                while ((line = reader.readLine()) != null) {
                    output.append(line).append("\n");
                }
            }
            
            int exitCode = process.waitFor();
            if (exitCode != 0) {
                logger.error("TLC process exited with code: {}", exitCode);
            }
            
            // Clean up temporary files
            Files.deleteIfExists(tlaFile.toPath());
            Files.deleteIfExists(cfgFile.toPath());
            Files.deleteIfExists(tempDir);
            
            return output.toString();
            
        } catch (IOException | InterruptedException e) {
            logger.error("Error running TLC", e);
            return "TLC Error: " + e.getMessage();
        }
    }
    
    private String readResourceAsString(String resourcePath) throws IOException {
        try (InputStream is = new ClassPathResource(resourcePath).getInputStream();
             ByteArrayOutputStream result = new ByteArrayOutputStream()) {
            byte[] buffer = new byte[1024];
            int length;
            while ((length = is.read(buffer)) != -1) {
                result.write(buffer, 0, length);
            }
            return result.toString("UTF-8");
        }
    }
    
    public String loadDefaultSpec() {
        try {
            return readResourceAsString(TLA_SPEC_PATH);
        } catch (IOException e) {
            logger.error("Error loading default TLA+ specification", e);
            return "Error loading specification: " + e.getMessage();
        }
    }
    
    public String loadDefaultCfg() {
        try {
            return readResourceAsString(TLA_CFG_PATH);
        } catch (IOException e) {
            logger.error("Error loading default TLA+ configuration", e);
            return "Error loading configuration: " + e.getMessage();
        }
    }
    
    private String generateFSMInitClause(MicrowaveFSM fsm) {
        String doorValue = (fsm.getState() == MicrowaveFSM.State.DOOR_OPEN) ? "open" : "closed";
        String radiationValue = (fsm.getState() == MicrowaveFSM.State.COOKING) ? "on" : "off";
        int time = fsm.getTimer();
        return "OverriddenInit ==\n" +
               "  /\\ door = \"" + doorValue + "\"\n" +
               "  /\\ radiation = \"" + radiationValue + "\"\n" +
               "  /\\ timeRemaining = " + time + "\n";
    }
    
    private String generateOverriddenNextClause(String action) {
        return "OverriddenNext == " + action + "\n";
    }
    
    public String validateTransition(String action, MicrowaveFSM fsm) {
        try {
            // Create temporary directory for TLA files
            Path tempDir = Files.createTempDirectory("tla-run");
            Path specFile = tempDir.resolve(TLA_SPEC_PATH);
            
            // Copy the TLA spec file to temp directory
            Files.copy(new ClassPathResource(TLA_SPEC_PATH).getInputStream(), specFile);
            
            // Build the command to run TLC
            ProcessBuilder pb = new ProcessBuilder(
                "java", "-cp", JAR_PATH,
                "tlc2.TLC",
                specFile.toString()
            );
            
            // Start the process
            Process process = pb.start();
            
            // Read the output
            StringBuilder output = new StringBuilder();
            try (BufferedReader reader = new BufferedReader(new InputStreamReader(process.getInputStream()))) {
                String line;
                while ((line = reader.readLine()) != null) {
                    output.append(line).append("\n");
                }
            }
            
            // Wait for the process to complete
            int exitCode = process.waitFor();
            if (exitCode != 0) {
                logger.error("TLC validation process exited with code: {}", exitCode);
            }
            
            // Clean up
            Files.deleteIfExists(specFile);
            Files.deleteIfExists(tempDir);
            
            return output.toString();
            
        } catch (Exception e) {
            logger.error("Error running TLA validation", e);
            return "Error running TLA validation: " + e.getMessage();
        }
    }
}
