# Use official Python base image
FROM python:3.11-slim

# Set working directory
WORKDIR /workspaces/FormaLLM

# Install system dependencies
RUN apt-get update && apt-get install -y \
    openjdk-25-jdk \
    wget \
    curl \
    unzip \
    git \
    && rm -rf /var/lib/apt/lists/*

# Set environment variable for TLA+ tools
ENV TLA_TOOLS_DIR=/opt/tla

# Download and extract TLA+ tools (fail-safe)
RUN mkdir -p $TLA_TOOLS_DIR && \
    wget -q --show-progress --retry-connrefused --waitretry=1 --read-timeout=20 --timeout=15 -t 3 \
    https://github.com/tlaplus/tlaplus/releases/latest/download/tla2tools.jar -O $TLA_TOOLS_DIR/tla2tools.jar

# Add TLC launcher script to PATH
RUN echo '#!/bin/bash\nexec java -cp /opt/tla/tla2tools.jar tlc2.TLC "$@"' > /usr/local/bin/tlc && \
    chmod +x /usr/local/bin/tlc

# Copy project files
COPY . .

# Upgrade pip and install dependencies
RUN pip install --upgrade pip
RUN pip install -r requirements.txt

# Default command
CMD ["bash"]
