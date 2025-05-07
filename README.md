# Interactive Microwave TLA+ Application

This application demonstrates a microwave oven's behavior using TLA+ formal specification and provides an interactive UI to simulate and verify the behavior.

## Prerequisites

- Java 17 or later
- Maven 3.9.x or later
- Node.js 18.x or later
- TLA+ Tools (tla2tools.jar)

## Setup

1. Clone the repository:
   ```bash
   git clone https://github.com/yourusername/interactive-microwave-tla.git
   cd interactive-microwave-tla
   ```

2. Download tla2tools.jar:
   ```bash
   mkdir -p lib
   curl -L -o lib/tla2tools.jar https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar
   ```

3. Install dependencies:
   ```bash
   # Install Java dependencies
   mvn clean install
   
   # Install frontend dependencies
   npm install
   ```

## Running the Application

1. Start the Spring Boot application:
   ```bash
   mvn spring-boot:run
   ```

2. The application will be available at http://localhost:8080

## Development

- Java source code is in `src/main/java`
- TLA+ specifications are in `src/main/resources`
- Frontend code is in `frontend/`
- Static resources (images) are in `src/main/resources/static`

## Building

```bash
# Build Java application
mvn clean package

# Build frontend
npm run build
```

## Testing

```bash
# Run Java tests
mvn test

# Run frontend tests
npm test
```

## Project Structure

```
.
├── frontend/           # Frontend source code
├── lib/               # External dependencies
├── src/
│   └── main/
│       ├── java/      # Java source code
│       └── resources/ # TLA+ specs and static resources
├── pom.xml            # Maven configuration
├── package.json       # NPM configuration
└── README.md          # This file
```

## License

This project is licensed under the MIT License - see the LICENSE file for details.
