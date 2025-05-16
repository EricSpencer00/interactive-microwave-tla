package com.example.tlamicrowave.service;

import org.springframework.stereotype.Service;
import org.springframework.beans.factory.annotation.Value;
import org.springframework.beans.factory.annotation.Autowired;
import java.io.*;
import java.nio.file.*;
import java.util.*;
import java.util.regex.*;
import java.util.stream.Collectors;
import java.util.concurrent.TimeUnit;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

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

    private static final Logger log = LoggerFactory.getLogger(TlcIntegrationService.class);

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
                   .append("/\\ door = CLOSED\n")
                   .append("/\\ power = ON\n")
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
        
        // Extract only the last 20 states to keep verification fast
        List<String> stateEntries = verificationLog.stream()
            .filter(entry -> entry.contains("(* State:"))
            .collect(Collectors.toList());
        
        // Take only the last 20 states if there are more
        if (stateEntries.size() > 20) {
            stateEntries = stateEntries.subList(stateEntries.size() - 20, stateEntries.size());
        }
        
        // Add the reduced states as a trace
        specBuilder.append("(* Trace of states from execution - last 20 states only *)\n");
        specBuilder.append("Trace ==\n");
            
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
            "MAX_TRACE_LENGTH = 100\n" +
            "WORKERS = 2\n";
        Path cfgPath = Paths.get(System.getProperty("user.dir"), CFG_FILENAME);
        Files.writeString(cfgPath, cfg);
    }

    /**
     * Executes the TLC model checker against the generated spec, returning the results.
     */
    public TlcResult runTlc() throws IOException, InterruptedException {
        log.debug("TLC verification started");
        
        // Use files from root directory
        Path specPath = Paths.get(System.getProperty("user.dir"), SPEC_FILENAME);
        Path cfgPath = Paths.get(System.getProperty("user.dir"), CFG_FILENAME);
        
        log.debug("Deleting existing files before generating new ones");
        // Delete existing files first to ensure we don't have stale data
        Files.deleteIfExists(specPath);
        Files.deleteIfExists(cfgPath);
        
        log.debug("Generating fresh spec file");
        // Generate fresh files
        long startGen = System.currentTimeMillis();
        generateSpecFile();
        log.debug("Spec file generation completed in {} ms", System.currentTimeMillis() - startGen);
        
        log.debug("Generating config file");
        startGen = System.currentTimeMillis();
        generateConfigFile();
        log.debug("Config file generation completed in {} ms", System.currentTimeMillis() - startGen);

        // Now run TLC with aggressive performance options
        List<String> command = new ArrayList<>();
        Path scriptPath = Paths.get(System.getProperty("user.dir"), "run-tlc.sh");
        command.add(scriptPath.toString());
        
        command.add(specPath.toString());
        command.add("-config");
        command.add(cfgPath.toString());
        
        // Add performance options
        command.add("-workers");
        command.add("2");  // Use 2 worker threads
        command.add("-nowarning"); // Skip warnings
        command.add("-cleanup");   // Clean up temp files
        
        log.debug("Preparing to execute TLC command: {}", String.join(" ", command));

        ProcessBuilder pb = new ProcessBuilder(command);
        pb.directory(Paths.get(System.getProperty("user.dir")).toFile());  // Run from root directory
        pb.redirectErrorStream(true);
        
        // Check the size of the specification file
        long specSize = Files.size(specPath);
        log.debug("Spec file size: {} bytes", specSize);
        
        List<String> verificationLog = verificationLogService.getVerificationLog();
        log.debug("Verification log contains {} entries", verificationLog.size());
        
        // For large logs (more than 50 states), issue a warning
        if (verificationLog.size() > 50) {
            log.warn("Large verification log with {} entries. TLC verification may be slow.", verificationLog.size());
        }
        
        // Set a timeout for the process
        log.debug("Starting TLC process");
        long startTime = System.currentTimeMillis();
        Process proc = pb.start();
        log.debug("TLC process started in {} ms", System.currentTimeMillis() - startTime);
        
        // Start reading output immediately in a separate thread to prevent blocking
        StringBuilder output = new StringBuilder();
        Thread outputReader = new Thread(() -> {
            try (BufferedReader reader = new BufferedReader(new InputStreamReader(proc.getInputStream()))) {
                String line;
                while ((line = reader.readLine()) != null) {
                    log.debug("TLC output: {}", line);
                    output.append(line).append(System.lineSeparator());
                }
            } catch (IOException e) {
                log.error("Error reading TLC output", e);
            }
            log.debug("TLC output reader thread finished");
        });
        outputReader.setDaemon(true);
        outputReader.start();
        
        log.debug("Waiting for TLC process to complete (timeout: 300 seconds)");
        // Use a timeout of 300 seconds
        boolean completed = proc.waitFor(300, TimeUnit.SECONDS);
        log.debug("TLC process wait completed: timeout={}, elapsed={}ms", !completed, System.currentTimeMillis() - startTime);
        
        if (!completed) {
            // If the process didn't complete in time, kill it
            log.warn("TLC verification timed out after 300 seconds, killing process");
            proc.destroyForcibly();
            
            // Wait for the output reader to finish
            log.debug("Waiting for output reader thread to finish");
            try {
                outputReader.join(1000);
            } catch (InterruptedException e) {
                log.error("Interrupted while waiting for output reader", e);
            }
            
            output.append("TLC verification timed out after 300 seconds.\n");
            output.append("This likely means the state space is too large to explore efficiently.\n");
            output.append("Consider using fewer states in your trace or running TLC manually.\n");
            
            log.debug("Returning timeout result");
            // Return a result indicating timeout
            return new TlcResult(false, new ArrayList<>(), output.toString(), true);
        }

        int exitCode = proc.exitValue();
        log.debug("TLC process completed with exit code: {}", exitCode);
        boolean invariantHolds = (exitCode == 0);
        log.debug("Invariant holds: {}", invariantHolds);

        log.debug("Parsing TLC trace from output");
        List<Map<String, String>> traceStates = parseTlcTrace(output.toString());
        log.debug("Found {} trace states", traceStates.size());
        
        log.debug("TLC verification completed in {} ms", System.currentTimeMillis() - startTime);
        return new TlcResult(invariantHolds, traceStates, output.toString(), false);
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

    /**
     * Directly checks the verification log for safety violations without running TLC.
     * This is useful for checking if the actual execution trace violates safety properties.
     */
    public SafetyCheckResult checkSafetyInLog() {
        List<String> verificationLog = verificationLogService.getVerificationLog();
        List<String> stateEntries = verificationLog.stream()
            .filter(entry -> entry.contains("(* State:"))
            .collect(Collectors.toList());
        
        List<LogViolation> violations = new ArrayList<>();
        int stateNum = 0;
        
        for (String stateEntry : stateEntries) {
            String doorState = extractValue(stateEntry, "door");
            String radiationState = extractValue(stateEntry, "radiation");
            
            // Check for door open with radiation on
            if (doorState.equals("OPEN") && radiationState.equals("ON")) {
                String stateLabel = "";
                if (stateEntry.contains("(* State:")) {
                    stateLabel = stateEntry.substring(
                        stateEntry.indexOf("(* State:") + 10, 
                        stateEntry.indexOf("*)")
                    ).trim();
                }
                
                violations.add(new LogViolation(
                    stateNum,
                    stateLabel,
                    "Door OPEN with Radiation ON",
                    extractStateMap(stateEntry)
                ));
            }
            stateNum++;
        }
        
        return new SafetyCheckResult(violations.isEmpty(), violations);
    }
    
    private Map<String, String> extractStateMap(String stateEntry) {
        Map<String, String> stateMap = new LinkedHashMap<>();
        stateMap.put("door", extractValue(stateEntry, "door"));
        stateMap.put("time", extractValue(stateEntry, "time"));
        stateMap.put("radiation", extractValue(stateEntry, "radiation"));
        stateMap.put("power", extractValue(stateEntry, "power"));
        return stateMap;
    }
    
    /**
     * Result of checking safety properties directly in the log.
     */
    public static class SafetyCheckResult {
        public final boolean safetyHolds;
        public final List<LogViolation> violations;
        
        public SafetyCheckResult(boolean safetyHolds, List<LogViolation> violations) {
            this.safetyHolds = safetyHolds;
            this.violations = violations;
        }
    }
    
    /**
     * Represents a safety violation found in the log.
     */
    public static class LogViolation {
        public final int stateNum;
        public final String stateLabel;
        public final String violationDesc;
        public final Map<String, String> state;
        
        public LogViolation(int stateNum, String stateLabel, String violationDesc, Map<String, String> state) {
            this.stateNum = stateNum;
            this.stateLabel = stateLabel;
            this.violationDesc = violationDesc;
            this.state = state;
        }
    }

    public static class TlcResult {
        public final boolean invariantHolds;
        public final List<Map<String, String>> traceStates;
        public final String rawOutput;
        public final boolean timedOut;

        public TlcResult(boolean invariantHolds, List<Map<String, String>> traceStates, String rawOutput, boolean timedOut) {
            this.invariantHolds = invariantHolds;
            this.traceStates = traceStates;
            this.rawOutput = rawOutput;
            this.timedOut = timedOut;
        }
    }

    /**
     * Verifies a specific execution trace against the TLA+ specification
     * by creating a special TraceMicrowave.tla file that extends the main spec.
     * 
     * @param trace The execution trace as a list of state maps
     * @return A TlcResult object indicating if the trace satisfies the spec
     */
    public TlcResult verifyExecutionTrace(List<Map<String, String>> trace) throws IOException, InterruptedException {
        log.debug("Verifying execution trace with {} states", trace.size());
        
        // Generate the TraceMicrowave.tla file
        StringBuilder specBuilder = new StringBuilder();
        specBuilder.append("---- MODULE TraceMicrowave ----\n")
                   .append("EXTENDS Naturals, TLC\n\n")
                   .append("VARIABLES door, time, radiation, power\n\n")
                   .append("CONSTANTS OPEN, CLOSED, ON, OFF\n\n")
                   .append("(* Trace to be verified *)\n")
                   .append("Trace == [\n")
                   .append("  n \\in 1..").append(trace.size()).append(" |-> CASE\n");
        
        // Add each state of the trace as a case
        for (int i = 0; i < trace.size(); i++) {
            Map<String, String> state = trace.get(i);
            specBuilder.append("    n = ").append(i + 1).append(" -> [")
                       .append("door |-> ").append(state.get("door"))
                       .append(", time |-> ").append(state.get("time"))
                       .append(", radiation |-> ").append(state.get("radiation"))
                       .append(", power |-> ").append(state.get("power"))
                       .append("]");
            if (i < trace.size() - 1) {
                specBuilder.append("\n");
            }
        }
        
        specBuilder.append("\n  ]\n\n");
        
        // Define a constraint-based specification that only checks the specific trace
        specBuilder.append("Init ==\n")
                   .append("  /\\ door = Trace[1].door\n")
                   .append("  /\\ time = Trace[1].time\n")
                   .append("  /\\ radiation = Trace[1].radiation\n")
                   .append("  /\\ power = Trace[1].power\n\n");
        
        specBuilder.append("Next ==\n")
                   .append("  \\E i \\in 1..").append(trace.size() - 1).append(":\n")
                   .append("    /\\ door = Trace[i].door\n")
                   .append("    /\\ time = Trace[i].time\n")
                   .append("    /\\ radiation = Trace[i].radiation\n")
                   .append("    /\\ power = Trace[i].power\n")
                   .append("    /\\ door' = Trace[i+1].door\n")
                   .append("    /\\ time' = Trace[i+1].time\n")
                   .append("    /\\ radiation' = Trace[i+1].radiation\n")
                   .append("    /\\ power' = Trace[i+1].power\n\n");

        // Define safety property - radiation should not be ON when door is OPEN
        specBuilder.append("Safe == ~(radiation = ON /\\ door = OPEN)\n\n");
        
        // Define the behavior spec to check ONLY the trace
        specBuilder.append("vars == <<door, time, radiation, power>>\n\n")
                   .append("(* Specification that only allows exactly the states in the trace *)\n")
                   .append("TraceSpec == Init /\\ [][Next]_vars /\\ <>Trace[").append(trace.size()).append("] = [door |-> door, time |-> time, radiation |-> radiation, power |-> power]\n\n")
                   .append("(* Constraints to ONLY check this trace and no others *)\n")
                   .append("StateConstraint ==\n")
                   .append("  \\E i \\in 1..").append(trace.size()).append(":\n")
                   .append("    /\\ door = Trace[i].door\n")
                   .append("    /\\ time = Trace[i].time\n")
                   .append("    /\\ radiation = Trace[i].radiation\n")
                   .append("    /\\ power = Trace[i].power\n\n")
                   .append("====\n");
        
        // Write TraceMicrowave.tla
        Path traceSpecPath = Paths.get(System.getProperty("user.dir"), "TraceMicrowave.tla");
        Files.writeString(traceSpecPath, specBuilder.toString());
        log.debug("Generated trace specification at {}", traceSpecPath);
        
        // Write TraceMicrowave.cfg with constraints
        StringBuilder cfgBuilder = new StringBuilder();
        cfgBuilder.append("SPECIFICATION TraceSpec\n")
                 .append("INVARIANT Safe\n")
                 .append("CONSTANTS\n")
                 .append("  OPEN = \"OPEN\"\n")
                 .append("  CLOSED = \"CLOSED\"\n")
                 .append("  ON = \"ON\"\n")
                 .append("  OFF = \"OFF\"\n")
                 .append("CONSTRAINT StateConstraint\n")
                 .append("CHECK_DEADLOCK FALSE\n")  // Don't check for deadlocks
                 .append("SYMMETRY_REDUCTION FALSE\n")  // Disable symmetry reduction for speed
                 .append("VIEW vars\n")              // Show all variables in output
                 .append("POSTCONDITION Trace[").append(trace.size()).append("] = [door |-> door, time |-> time, radiation |-> radiation, power |-> power]\n");
                 
        Path traceCfgPath = Paths.get(System.getProperty("user.dir"), "TraceMicrowave.cfg");
        Files.writeString(traceCfgPath, cfgBuilder.toString());
        log.debug("Generated trace configuration at {}", traceCfgPath);
        
        try {
            // Run TLC with more aggressive performance settings
            List<String> command = new ArrayList<>();
            Path scriptPath = Paths.get(System.getProperty("user.dir"), "run-tlc.sh");
            command.add(scriptPath.toString());
            command.add(traceSpecPath.toString());
            command.add("-config");
            command.add(traceCfgPath.toString());
            command.add("-difftrace");  // Show exactly where traces differ
            command.add("-coverage");   // Check coverage
            command.add("0");           // Minimum coverage threshold - no threshold
            command.add("-workers");
            command.add("1");           // Just one worker is enough for trace checking
            command.add("-nowarning");  // Skip warnings for speed
            command.add("-maxSetSize");
            command.add("100");         // Limit set size
            
            log.debug("Executing TLC command for trace verification: {}", String.join(" ", command));
            
            ProcessBuilder pb = new ProcessBuilder(command);
            pb.directory(Paths.get(System.getProperty("user.dir")).toFile());
            pb.redirectErrorStream(true);
            
            Process proc = pb.start();
            StringBuilder output = new StringBuilder();
            
            // Read output in the main thread
            try (BufferedReader reader = new BufferedReader(new InputStreamReader(proc.getInputStream()))) {
                String line;
                while ((line = reader.readLine()) != null) {
                    log.debug("TLC trace verification output: {}", line);
                    output.append(line).append(System.lineSeparator());
                }
            }
            
            // Wait with a timeout - trace checking should be fast
            boolean completed = proc.waitFor(30, TimeUnit.SECONDS);  // 30 seconds is plenty for trace checking
            if (!completed) {
                log.warn("TLC trace verification timed out after 30 seconds, killing process");
                proc.destroyForcibly();
                return new TlcResult(false, new ArrayList<>(), 
                    "TLC trace verification timed out after 30 seconds. This shouldn't happen for trace checking and indicates a problem.", true);
            }
            
            int exitCode = proc.exitValue();
            String outputStr = output.toString();
            
            // Check if the trace is valid
            boolean traceConforms = exitCode == 0 && !outputStr.contains("Error:");
            
            // Extract specific error information if available
            String errorInfo = "";
            if (!traceConforms) {
                // Look for violations in the output
                if (outputStr.contains("Invariant Safe is violated")) {
                    // Safety violation
                    errorInfo = "Safety property violated: radiation is ON while door is OPEN";
                    
                    // Try to extract the specific state
                    Pattern statePattern = Pattern.compile("State (\\d+).*?radiation = ON.*?door = OPEN", 
                                           Pattern.DOTALL | Pattern.MULTILINE);
                    Matcher stateMatcher = statePattern.matcher(outputStr);
                    if (stateMatcher.find()) {
                        errorInfo += " at state " + stateMatcher.group(1);
                    }
                } else if (outputStr.contains("does not satisfy the temporal formula")) {
                    // Trace doesn't follow specification
                    errorInfo = "Trace does not follow the microwave specification";
                    
                    // Look for step information
                    Pattern stepPattern = Pattern.compile("step (\\d+)");
                    Matcher stepMatcher = stepPattern.matcher(outputStr);
                    if (stepMatcher.find()) {
                        errorInfo += " at step " + stepMatcher.group(1);
                    }
                } else {
                    errorInfo = "Unknown verification error";
                }
            }
            
            log.debug("Trace verification result: conforms={}, error={}", 
                    traceConforms, errorInfo.isEmpty() ? "none" : errorInfo);
            
            return new TlcResult(traceConforms, trace, 
                errorInfo.isEmpty() ? outputStr : errorInfo + "\n\n" + outputStr, false);
            
        } finally {
            // Clean up temporary files
            try {
                Files.deleteIfExists(traceSpecPath);
                Files.deleteIfExists(traceCfgPath);
                log.debug("Cleaned up temporary trace verification files");
            } catch (IOException e) {
                log.warn("Failed to clean up trace verification files: {}", e.getMessage());
            }
        }
    }
}
