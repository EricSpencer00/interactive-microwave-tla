package com.example.tlamicrowave.service;

import org.springframework.stereotype.Service;
import org.springframework.beans.factory.annotation.Value;
import java.io.*;
import java.nio.file.*;
import java.util.*;
import java.util.regex.*;

@Service
public class TlcIntegrationService {
    private static final String SPEC_FILENAME = "Microwave.tla";
    private static final String CFG_FILENAME = "Microwave.cfg";
    
    @Value("${tlc.spec-dir}")
    private String specDirPath;
    
    @Value("${tlc.cmd}")
    private String tlcCommand;
    
    @Value("${tlc.cmd.args}")
    private String tlcArgs;   // comma-separated

    /**
     * Writes a clean TLA+ specification file to disk.
     */
    public void generateSpecFile() throws IOException {
        String spec =
            "---- MODULE Microwave ----\n" +
            "EXTENDS Integers, TLC\n\n" +
            "VARIABLES door, time, radiation, power\n\n" +
            "Init ==\n" +
            "/\\ door = CLOSED\n" +
            "/\\ time = 0\n" +
            "/\\ radiation = OFF\n" +
            "/\\ power = OFF\n\n" +
            "TogglePower ==\n" +
            "/\\ UNCHANGED <<door, time, radiation>>\n" +
            "/\\ power' = IF power = ON THEN OFF ELSE ON\n\n" +
            "IncrementTime ==\n" +
            "/\\ UNCHANGED <<door, radiation, power>>\n" +
            "/\\ time' = time + 3\n\n" +
            "Start ==\n" +
            "/\\ time > 0\n" +
            "/\\ radiation' = ON\n" +
            "/\\ UNCHANGED <<door, time, power>>\n\n" +
            "Tick ==\n" +
            "/\\ time > 0\n" +
            "/\\ time' = time - 1\n" +
            "/\\ UNCHANGED <<door, power>>\n" +
            "/\\ radiation' = IF time' = 0 THEN OFF ELSE radiation\n\n" +
            "Cancel ==\n" +
            "/\\ time' = 0\n" +
            "/\\ radiation' = OFF\n" +
            "/\\ UNCHANGED <<door, power>>\n\n" +
            "Safe == ~(radiation = ON /\\ door = OPEN)\n\n" +
            "Spec == Init /\\ [][Next]_<<door,time,radiation,power>>\n\n" +
            "THEOREM Spec => []Safe\n" +
            "====\n";
        Path specDir = Paths.get(specDirPath);
        Files.createDirectories(specDir);
        Files.writeString(specDir.resolve(SPEC_FILENAME), spec);
    }

    /**
     * Writes a TLC configuration file to disk.
     */
    public void generateConfigFile() throws IOException {
        String cfg =
            "SPECIFICATION Spec\n" +
            "INVARIANT Safe\n";
        Path specDir = Paths.get(specDirPath);
        Files.createDirectories(specDir);
        Files.writeString(specDir.resolve(CFG_FILENAME), cfg);
    }

    /**
     * Executes the TLC model checker against the generated spec, returning the results.
     */
    public TlcResult runTlc() throws IOException, InterruptedException {
        // Use files from root directory
        Path specPath = Paths.get(System.getProperty("user.dir"), SPEC_FILENAME);
        Path cfgPath = Paths.get(System.getProperty("user.dir"), CFG_FILENAME);
        
        if (!Files.exists(specPath) || !Files.exists(cfgPath)) {
            throw new IOException("TLA+ specification files not found in root directory");
        }

        // Now run TLC
        List<String> command = new ArrayList<>();
        Path scriptPath = Paths.get(System.getProperty("user.dir"), "run-tlc.sh");
        command.add(scriptPath.toString());
        
        command.add(specPath.toString());
        command.add("-config");
        command.add(cfgPath.toString());

        ProcessBuilder pb = new ProcessBuilder(command);
        pb.directory(Paths.get(System.getProperty("user.dir")).toFile());  // Run from root directory
        pb.redirectErrorStream(true);
        Process proc = pb.start();

        StringBuilder output = new StringBuilder();
        try (BufferedReader reader = new BufferedReader(new InputStreamReader(proc.getInputStream()))) {
            String line;
            while ((line = reader.readLine()) != null) {
                output.append(line).append(System.lineSeparator());
            }
        }

        int exitCode = proc.waitFor();
        boolean invariantHolds = (exitCode == 0);

        List<Map<String, String>> traceStates = parseTlcTrace(output.toString());
        return new TlcResult(invariantHolds, traceStates, output.toString());
    }

    /**
     * Parses the TLC counterexample trace from raw output into a list of state maps.
     */
    public List<Map<String, String>> parseTlcTrace(String rawOutput) {
        List<Map<String, String>> states = new ArrayList<>();
        if (rawOutput == null || rawOutput.trim().isEmpty()) {
            return states;
        }

        // Debug log the raw output
        System.out.println("Raw TLC output:");
        System.out.println(rawOutput);

        // Look for the counterexample section
        String[] lines = rawOutput.split("\\R");
        boolean inCounterexample = false;
        Map<String, String> current = null;

        for (String line : lines) {
            // Skip empty lines
            if (line.trim().isEmpty()) {
                continue;
            }

            // Check if we're entering a counterexample
            if (line.contains("Error: Invariant") || line.contains("Error: Deadlock")) {
                inCounterexample = true;
                continue;
            }

            // Only process lines if we're in a counterexample
            if (inCounterexample) {
                if (line.startsWith("State ")) {
                    if (current != null) {
                        states.add(current);
                    }
                    current = new LinkedHashMap<>();
                } else if (current != null && line.trim().startsWith("/\\")) {
                    // Parse state assignments
                    String[] parts = line.trim().substring(3).split("=");
                    if (parts.length == 2) {
                        String key = parts[0].trim();
                        String value = parts[1].trim();
                        current.put(key, value);
                    }
                }
            }
        }

        // Add the last state if exists
        if (current != null) {
            states.add(current);
        }

        // Debug log the parsed states
        System.out.println("Parsed states: " + states.size());
        for (int i = 0; i < states.size(); i++) {
            System.out.println("State " + i + ": " + states.get(i));
        }

        return states;
    }

    /**
     * Compares the simulated trace (from your service) against the TLC trace for exact equality.
     */
    public boolean compareTraces(List<Map<String, String>> simStates, List<Map<String, String>> tlcStates) {
        if (simStates.size() != tlcStates.size()) {
            return false;
        }
        for (int i = 0; i < simStates.size(); i++) {
            if (!simStates.get(i).equals(tlcStates.get(i))) {
                return false;
            }
        }
        return true;
    }

    public static class TlcResult {
        public final boolean invariantHolds;
        public final List<Map<String, String>> traceStates;
        public final String rawOutput;

        public TlcResult(boolean invariantHolds, List<Map<String, String>> traceStates, String rawOutput) {
            this.invariantHolds = invariantHolds;
            this.traceStates = traceStates;
            this.rawOutput = rawOutput;
        }
    }
}
