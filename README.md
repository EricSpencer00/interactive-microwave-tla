# TLA+ Microwave Simulator

[https://espencer.me/projects/2025/interactive-microwave-tla/](https://espencer.me/projects/2025/interactive-microwave-tla/)

This is a Spring Boot + Vaadin application that simulates a microwave oven with TLA+ verification. The application demonstrates state machine behavior and safety properties.

## Features

- Microwave state simulation with door, radiation, power, and timer
- TLA+ verification output for each state transition
- Real-time UI updates
- Safety property enforcement
- Feature toggles for enabling/disabling components
- Dangerous mode for experimenting with safety violations
- Configurable simulation parameters

## Requirements

- Java 17 or higher
- Maven 3.6 or higher

## Running the Application

1. Clone the repo:
   ```bash
   git clone https://github.com/yourusername/interactive-microwave-tla.git
   cd interactive-microwave-tla
   ```

2. Download TLA+ tools:
   ```bash
   ./download-tla.sh
   ```

3. Build the project:
   ```bash
   mvn clean install
   ```

4. Run the application:
   ```bash
   mvn spring-boot:run
   ```
   
   If port 8080 is already in use, you can specify a different port:
   ```bash
   mvn spring-boot:run -Dspring-boot.run.arguments=--server.port=8081
   ```

5. Open the application in your browser:
   - Default: [http://localhost:8080](http://localhost:8080)
   - Custom port: [http://localhost:8081](http://localhost:8081) (or whatever port you specified)

6. Interact with the microwave and click "Verify with TLC" to check safety properties.

Note: The TLA+ tools are included in the project as a local JAR file. No additional installation is required.

## Feature Toggles

The application includes a feature toggle panel on the left side that allows you to:

1. **Power Button Toggle**:
   - When enabled (default): Power button is visible and the microwave requires power to operate
   - When disabled: Power button is hidden, power indicator is removed, and TLA+ specification is simplified

2. **Dangerous Mode Toggle**:
   - When disabled (default): Safety properties are enforced (radiation turns off when door opens)
   - When enabled: Safety properties can be violated (radiation can stay on when door opens)

These toggles allow you to experiment with different microwave behaviors and TLA+ specifications.

## TLA+ Guide

The application includes a TLA+ Guide panel accessible from the left sidebar tabs. This guide provides:

1. **Tutorial Tab**:
   - Introduction to the microwave simulator
   - How to use the microwave controls
   - Explanation of feature toggles
   - Description of safety properties
   - Suggestions for experiments to try

2. **TLA+ Cheatsheet Tab**:
   - Basic TLA+ syntax reference
   - Common operators and their usage
   - State predicates and specifications
   - Microwave-specific TLA+ examples
   - TLC commands for verification

This guide is especially useful for those new to TLA+ or formal verification concepts.

## State Machine Properties

### State Variables
- Door: OPEN/CLOSED
- Radiation: ON/OFF
- Power: ON/OFF (when power button is enabled)
- Time Remaining: 0-60 seconds

### Actions
- Toggle Power (when power button is enabled)
- Increment Time (+3s)
- Start
- Cancel
- Open/Close Door
- Tick (automatic)

### Safety Properties
- Door Safety: Radiation cannot be ON when door is OPEN
- Start Safety: Can only start when door is CLOSED and time > 0
- Open Door Safety: Radiation turns OFF when door opens

## TLA+ Verification

The application logs each state transition in TLA+ format, showing:
- Action performed
- Pre-state
- Post-state
- Safety property verification

The TLA+ specification automatically adjusts based on enabled features:
- When power button is enabled: Full specification with power variable
- When power button is disabled: Simplified specification without power

## Configuration

The application can be configured through application.properties:
- `microwave.max-time`: Maximum cooking time (default: 60)
- `microwave.tick-interval`: Tick interval in milliseconds (default: 1000)

## Troubleshooting

- If you encounter port conflicts, use the custom port option mentioned above
- If verification fails, check the logs for detailed error messages
- For development, you can run the application in debug mode with:
  ```bash
  mvn spring-boot:run -Dspring-boot.run.jvmArguments="-Xdebug -Xrunjdwp:transport=dt_socket,server=y,suspend=n,address=5005"
  ``` 
