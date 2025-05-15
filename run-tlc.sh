#!/bin/bash

# Get the directory where this script is located
SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

# Use the local JAR file with absolute path
TLA_JAR="$SCRIPT_DIR/lib/tla2tools.jar"

if [ ! -f "$TLA_JAR" ]; then
    echo "Error: TLA+ tools JAR not found. Please run './download-tla.sh' first."
    exit 1
fi

# Run TLC with the provided arguments
java -jar "$TLA_JAR" "$@" 