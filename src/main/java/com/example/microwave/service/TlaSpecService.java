package com.example.microwave.service;

import com.example.microwave.fsm.MicrowaveFSM;
import java.io.*;
import java.nio.file.*;
import java.util.*;
import org.springframework.stereotype.Service;

@Service
public class TlaSpecService {

    // Relative path to the bundled tla2tools.jar (resolved as absolute at runtime)
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
    
    // Returns the complete default TLA+ spec (using string concatenation).
    public String loadDefaultSpec() {
        return "\\*34567890123456789012345678901234567890123456789012\n" +
               "-------------------------- MODULE MicrowaveSpec  --------------------------\n" +
               "\n" +
               "EXTENDS TLC, Integers\n" +
               "\n" +
               "CONSTANTS\n" +
               "  \\* Flag for enabling safety check upon starting radiation\n" +
               "  ImplementStartSafety,\n" +
               "  \\* Flag for enabling safety check upon opening door\n" +
               "  ImplementOpenDoorSafety\n" +
               "\n" +
               "VARIABLES\n" +
               "  \\* See TypeOK below for type constraints\n" +
               "  door,\n" +
               "  radiation,\n" +
               "  timeRemaining\n" +
               "\n" +
               "\\* Tuple of all variables\n" +
               "vars == << door, radiation, timeRemaining >>\n" +
               "\n" +
               "\\* Symbolic names for significant strings\n" +
               "OFF == \"off\"\n" +
               "ON == \"on\"\n" +
               "CLOSED == \"closed\"\n" +
               "OPEN == \"open\"\n" +
               "\n" +
               "\\* Dynamic type invariant\n" +
               "TypeOK == \n" +
               "  /\\ door \\in { CLOSED, OPEN }\n" +
               "  /\\ radiation \\in { OFF, ON }\n" +
               "  /\\ timeRemaining \\in Nat\n" +
               "\n" +
               "MaxTime == 60\n" +
               "\n" +
               "\\* Valid initial state(s)\n" +
               "Init ==\n" +
               "  /\\ door \\in { OPEN, CLOSED }\n" +
               "  /\\ radiation = OFF\n" +
               "  /\\ timeRemaining = 0\n" +
               "\n" +
               "\\* Increment remaining time by one second\n" +
               "IncTime ==\n" +
               "  /\\ radiation = OFF\n" +
               "  /\\ timeRemaining' = timeRemaining + 1\n" +
               "  /\\ timeRemaining' <= MaxTime\n" +
               "  /\\ UNCHANGED << door, radiation >>\n" +
               "\n" +
               "\\* Start radiation and time countdown\n" +
               "Start ==\n" +
               "  /\\ radiation = OFF\n" +
               "  /\\ ImplementStartSafety => door = CLOSED\n" +
               "  /\\ timeRemaining > 0\n" +
               "  /\\ radiation' = ON\n" +
               "  /\\ UNCHANGED << door, timeRemaining >>\n" +
               "\n" +
               "\\* Cancel radiation and reset remaining time\n" +
               "Cancel ==\n" +
               "  /\\ radiation' = OFF\n" +
               "  /\\ timeRemaining' = 0\n" +
               "  /\\ UNCHANGED << door >>\n" +
               "\n" +
               "\\* Internal clock tick for time countdown\n" +
               "Tick ==\n" +
               "  /\\ radiation = ON\n" +
               "  /\\ timeRemaining' = timeRemaining - 1\n" +
               "  /\\ timeRemaining' >= 0\n" +
               "  /\\ IF timeRemaining' = 0 \n" +
               "     THEN radiation' = OFF \n" +
               "     ELSE UNCHANGED << radiation >>\n" +
               "  /\\ UNCHANGED << door >>\n" +
               "\n" +
               "\\* Open door\n" +
               "OpenDoor ==\n" +
               "  /\\ door' = OPEN\n" +
               "  /\\ IF ImplementOpenDoorSafety \n" +
               "     THEN radiation' = OFF \n" +
               "     ELSE UNCHANGED << radiation >>\n" +
               "  /\\ UNCHANGED << timeRemaining >>\n" +
               "\n" +
               "\\* Close door\n" +
               "CloseDoor ==\n" +
               "  /\\ door' = CLOSED\n" +
               "  /\\ UNCHANGED << radiation, timeRemaining >>\n" +
               "\n" +
               "\\* All valid actions (state transitions)\n" +
               "Next ==\n" +
               "  \\/ IncTime\n" +
               "  \\/ Start\n" +
               "  \\/ Cancel\n" +
               "  \\/ OpenDoor\n" +
               "  \\/ CloseDoor\n" +
               "  \\/ Tick\n" +
               "\n" +
               "\\* All valid system behaviors starting from the initial state\n" +
               "Spec == Init /\\ [][Next]_vars\n" +
               "\n" +
               "\\* Valid system behaviors with weak fairness to disallow stuttering\n" +
               "FSpec == Spec /\\ WF_vars(Tick)\n" +
               "\n" +
               "\\* Safety check to detect radiation with door open\n" +
               "DoorSafety == door = OPEN => radiation = OFF\n" +
               "\n" +
               "\\* Temporal check to detect indefinite radiation\n" +
               "HeatLiveness == radiation = ON ~> radiation = OFF\n" +
               "\n" +
               "RunsUntilDoneOrInterrupted == \n" +
               "  [][radiation = ON => radiation' = ON \\/ timeRemaining' = 0 \\/ door' = OPEN]_vars\n" +
               "\n" +
               "====\n" +
               "\n" +
               "(* other possible events\n" +
               "    action := \"10min\"\n" +
               "    action := \"1min\"\n" +
               "    action := \"10sec\"\n" +
               "    action := \"power\"\n" +
               "    action := \"timer\"\n" +
               "*)\n" +
               "\n" +
               "\\* DoorSafety == RequireSafety => radiation = ON => door = CLOSED";
    }
    
    // Returns the default CFG file as a string.
    public String loadDefaultCfg() {
        return "CONSTANTS\n" +
               "  ImplementStartSafety = FALSE\n" +
               "  ImplementOpenDoorSafety = FALSE\n" +
               "\n" +
               "SPECIFICATION \n" +
               "  Spec\n" +
               "  \\* FSpec\n" +
               "\n" +
               "INVARIANTS \n" +
               "  TypeOK\n" +
               "  \\* DoorSafety\n" +
               "\n" +
               "PROPERTIES \n" +
               "  \\* HeatLiveness\n" +
               "  \\* RunsUntilDoneOrInterrupted\n";
    }
    
    // Helper: Generate a clause overriding Init from the current FSM state.
    private String generateFSMInitClause(MicrowaveFSM fsm) {
        // Map the Java FSM state to TLA+ string values.
        // Assume: if state is DOOR_OPEN, then door = "open", else door = "closed"
        // Likewise, if state is COOKING, radiation = "on", else "off"
        String doorValue = (fsm.getState() == MicrowaveFSM.State.DOOR_OPEN) ? "open" : "closed";
        String radiationValue = (fsm.getState() == MicrowaveFSM.State.COOKING) ? "on" : "off";
        int time = fsm.getTimer();
        return "OverriddenInit ==\n" +
               "  /\\ door = \"" + doorValue + "\"\n" +
               "  /\\ radiation = \"" + radiationValue + "\"\n" +
               "  /\\ timeRemaining = " + time + "\n";
    }
    
    // Helper: Generate a clause that forces the next action to equal the attempted one.
    // Here we assume that the attempted action directly corresponds to one of the TLA+ actions, e.g., OpenDoor.
    private String generateOverriddenNextClause(String action) {
        return "OverriddenNext == " + action + "\n";
    }
    
    // Validate a given transition (action) by generating a modified spec with the current FSM state.
    public String validateTransition(String action, MicrowaveFSM fsm) {
        // Get the default spec.
        String defaultSpec = loadDefaultSpec();
        // Generate the overridden clauses.
        String initClause = generateFSMInitClause(fsm);
        String nextClause = generateOverriddenNextClause(action);
        // Assemble a modified spec that overrides Init and Next.
        // We add definitions for OverriddenInit and OverriddenNext and then define OverriddenSpec.
        String modifiedSpec = defaultSpec + "\n" +
                              initClause + "\n" +
                              nextClause + "\n" +
                              "OverriddenSpec == OverriddenInit /\\ [][OverriddenNext]_vars\n";
        // Run TLC on the modified spec using the default CFG.
        return runTLC(modifiedSpec, loadDefaultCfg());
    }
}
