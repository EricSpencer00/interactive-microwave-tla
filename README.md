# TLA+ Microwave Simulator

This is a Spring Boot + Vaadin application that simulates a microwave oven with TLA+ verification. The application demonstrates state machine behavior and safety properties.

## Features

- Microwave state simulation with door, radiation, and timer
- TLA+ verification output for each state transition
- Real-time UI updates
- Safety property enforcement
- Configurable simulation parameters

## Requirements

- Java 17 or higher
- Maven 3.6 or higher

## Running the Application

1. Clone the repository
2. Navigate to the project directory
3. Run the application:
   ```bash
   ./mvnw spring-boot:run
   ```
4. Open your browser and navigate to `http://localhost:8080`

## State Machine Properties

### State Variables
- Door: OPEN/CLOSED
- Radiation: ON/OFF
- Time Remaining: 0-60 seconds

### Actions
- Increment Time (+1s)
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

## Configuration

The application can be configured through application.properties:
- `microwave.max-time`: Maximum cooking time (default: 60)
- `microwave.tick-interval`: Tick interval in milliseconds (default: 1000) 