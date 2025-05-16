package com.example.tlamicrowave.service;

import org.springframework.stereotype.Service;
import org.springframework.beans.factory.annotation.Value;
import org.springframework.beans.factory.annotation.Autowired;
import java.io.*;
import java.nio.file.*;
import java.util.*;
import java.util.regex.*;
import java.util.stream.Collectors;

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
    
    @Autowired
    private VerificationLogService verificationLogService;

    /**
     * Writes a TLA+ specification file to disk using the verification log.
     */
    public void generateSpecFile() throws IOException {
        List<String> verificationLog = verificationLogService.getVerificationLog();
        
        // Start with the module header
        StringBuilder specBuilder = new StringBuilder();
        specBuilder.append("---- MODULE Microwave ----\n")
                   .append("EXTENDS Integers, TLC\n\n")
                   .append("VARIABLES door, time, radiation, power\n\n")
                   .append("CONSTANTS OPEN, CLOSED, ON, OFF\n\n")
                   .append("Init ==\n")
                   .append("/\\ door = CLOSED\n")
                   .append("/\\ time = 0\n")
                   .append("/\\ radiation = OFF\n")
                   .append("/\\ power = OFF\n\n")
                   .append("TogglePower ==\n")
                   .append("/\\ UNCHANGED <<door, time, radiation>>\n")
                   .append("/\\ power' = IF power = ON THEN OFF ELSE ON\n\n")
                   .append("IncrementTime ==\n")
                   .append("/\\ UNCHANGED <<door, radiation, power>>\n")
                   .append("/\\ time' = time + 3\n\n")
                   .append("Start ==\n")
                   .append("/\\ time > 0\n")
                   .append("/\\ radiation' = ON\n")
                   .append("/\\ UNCHANGED <<door, time, power>>\n\n")
                   .append("Tick ==\n")
                   .append("/\\ time > 0\n")
                   .append("/\\ time' = time - 1\n")
                   .append("/\\ UNCHANGED <<door, power>>\n")
                   .append("/\\ radiation' = IF time' = 0 THEN OFF ELSE radiation\n\n")
                   .append("Cancel ==\n")
                   .append("/\\ time' = 0\n")
                   .append("/\\ radiation' = OFF\n")
                   .append("/\\ UNCHANGED <<door, power>>\n\n")
                   .append("CloseDoor ==\n")
                   .append("/\\ door = OPEN\n")
                   .append("/\\ door' = CLOSED\n")
                   .append("/\\ UNCHANGED <<time, radiation, power>>\n\n")
                   .append("OpenDoor ==\n")
                   .append("/\\ door = CLOSED\n")
                   .append("/\\ door' = OPEN\n")
                   .append("/\\ radiation' = OFF\n")
                   .append("/\\ UNCHANGED <<time, power>>\n\n")
                   .append("Next == TogglePower \\/ IncrementTime \\/ Start \\/ Tick \\/ Cancel \\/ CloseDoor \\/ OpenDoor\n\n")
                   .append("Safe == ~(radiation = ON /\\ door = OPEN)\n\n")
                   .append("Spec == Init /\\ [][Next]_<<door,time,radiation,power>>\n\n");
        
        if (verificationLog.isEmpty()) {
            // If no log exists, just end the file
            specBuilder.append("====\n");
            Path specPath = Paths.get(System.getProperty("user.dir"), SPEC_FILENAME);
            Files.writeString(specPath, specBuilder.toString());
            return;
        }
        
        // Add the states as a trace
        specBuilder.append("(* Trace of states from execution *)\n");
        specBuilder.append("Trace ==\n");
        
        List<String> stateEntries = verificationLog.stream()
            .filter(entry -> entry.contains("(* State:"))
            .collect(Collectors.toList());
            
        for (int i = 0; i < stateEntries.size(); i++) {
            String stateEntry = stateEntries.get(i);
            specBuilder.append("  ").append(i == 0 ? "/\\ " : "\\/ /\\ ").append("door = ")
                       .append(extractValue(stateEntry, "door")).append("\n");
            specBuilder.append("     /\\ time = ").append(extractValue(stateEntry, "time")).append("\n");
            specBuilder.append("     /\\ radiation = ").append(extractValue(stateEntry, "radiation")).append("\n");
            specBuilder.append("     /\\ power = ").append(extractValue(stateEntry, "power")).append("\n");
            if (i < stateEntries.size() - 1) {
                specBuilder.append("\n");
            }
        }
        
        // End the file
        specBuilder.append("\n====\n");
        
        // Write to the root directory
        Path specPath = Paths.get(System.getProperty("user.dir"), SPEC_FILENAME);
        Files.writeString(specPath, specBuilder.toString());
    }
    
    private String extractValue(String stateEntry, String variable) {
        Pattern pattern = Pattern.compile("/\\\\ " + variable + " = (.+)");
        Matcher matcher = pattern.matcher(stateEntry);
        if (matcher.find()) {
            return matcher.group(1).trim();
        }
        return "\"UNKNOWN\"";
    }

    /**
     * Writes a TLC configuration file to disk.
     */
    public void generateConfigFile() throws IOException {
        String cfg =
            "SPECIFICATION Spec\n" +
            "INVARIANT Safe\n" +
            "CONSTANTS\n" +
            "  OPEN = \"OPEN\"\n" +
            "  CLOSED = \"CLOSED\"\n" +
            "  ON = \"ON\"\n" +
            "  OFF = \"OFF\"\n" +
            "MAX_STATES = 1000\n" +
            "MAX_TRACE_LENGTH = 100\n";
        Path cfgPath = Paths.get(System.getProperty("user.dir"), CFG_FILENAME);
        Files.writeString(cfgPath, cfg);
    }

    /**
     * Executes the TLC model checker against the generated spec, returning the results.
     */
    public TlcResult runTlc() throws IOException, InterruptedException {
        // Use files from root directory
        Path specPath = Paths.get(System.getProperty("user.dir"), SPEC_FILENAME);
        Path cfgPath = Paths.get(System.getProperty("user.dir"), CFG_FILENAME);
        
        // Generate files if they don't exist
        if (!Files.exists(specPath)) {
            generateSpecFile();
        }
        
        if (!Files.exists(cfgPath)) {
            generateConfigFile();
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
