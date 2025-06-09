FROM nvidia/cuda:12.8.1-base-ubuntu24.04

# Install Miniconda
ENV CONDA_DIR /opt/conda
RUN apt-get update && apt-get install -y \
    wget \
    curl \
    bzip2 \
    ca-certificates \
    git \
    && rm -rf /var/lib/apt/lists/* && \
    wget https://repo.anaconda.com/miniconda/Miniconda3-latest-Linux-x86_64.sh -O /tmp/miniconda.sh && \
    bash /tmp/miniconda.sh -b -p $CONDA_DIR && \
    rm /tmp/miniconda.sh && \
    ln -s $CONDA_DIR/etc/profile.d/conda.sh /etc/profile.d/conda.sh

ENV PATH=$CONDA_DIR/bin:$PATH


# Copy environment.yml (if found) to a temp location so we update the environment. Also
# copy "noop.txt" so the COPY instruction does not fail if no environment.yml exists.
COPY environment.yml* .devcontainer/noop.txt /tmp/conda-tmp/
RUN if [ -f "/tmp/conda-tmp/environment.yml" ]; then umask 0002 && /opt/conda/bin/conda env update -n tla-llm -f /tmp/conda-tmp/environment.yml; fi \
    && rm -rf /tmp/conda-tmp
RUN conda init
RUN echo "conda activate tla-llm" >> /root/.bashrc

# Install Java for TLC
RUN apt-get update && apt-get install -y openjdk-17-jdk wget unzip && \
    rm -rf /var/lib/apt/lists/*

# Set environment variable for TLA+ tools
ENV TLA_TOOLS_DIR=/opt/tla

# Download and extract TLA+ tools (fail-safe)
RUN mkdir -p $TLA_TOOLS_DIR && \
    wget -q --show-progress --retry-connrefused --waitretry=1 --read-timeout=20 --timeout=15 -t 3 \
    https://github.com/tlaplus/tlaplus/releases/latest/download/tla2tools.jar -O $TLA_TOOLS_DIR/tla2tools.jar

# Add TLC launcher script to PATH
RUN echo '#!/bin/bash\nexec java -cp /opt/tla/tla2tools.jar tlc2.TLC "$@"' > /usr/local/bin/tlc && \
    chmod +x /usr/local/bin/tlc
