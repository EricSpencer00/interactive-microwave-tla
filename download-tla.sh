#!/bin/bash

# Create lib directory
mkdir -p lib

# Download TLA+ tools
curl -L "https://github.com/tlaplus/tlaplus/releases/download/v1.7.0/tla2tools.jar" -o lib/tla2tools.jar

echo "TLA+ tools downloaded to lib/tla2tools.jar" 