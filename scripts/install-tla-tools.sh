#!/bin/bash

# Create Maven repository directory
mkdir -p lib/maven-repo/org/lamport/tla2tools/1.8.0

# Install TLA+ tools into local Maven repository
mvn install:install-file \
    -Dfile=lib/tla2tools.jar \
    -DgroupId=org.lamport \
    -DartifactId=tla2tools \
    -Dversion=1.8.0 \
    -Dpackaging=jar \
    -DlocalRepositoryPath=lib/maven-repo

echo "TLA+ tools installed into local Maven repository" 