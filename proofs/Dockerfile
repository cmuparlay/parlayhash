# Dockerfile to run TLA+ and verify TLAPS proofs in a container.
# U. Y. Yavuz, August 2024.
# Acknowledgement: This Dockerfile is based on the following Dockerfile by
# Kevin Sullivan (https://github.com/kevinsullivan/TLAPlusDocker.git).

FROM --platform=linux/amd64 ubuntu:24.04

SHELL ["/bin/bash", "-c"]

ENV DEBIAN_FRONTEND=noninteractive
RUN echo 'debconf debconf/frontend select Noninteractive' | debconf-set-selections

RUN apt-get clean && apt-get update -y && apt-get upgrade -y && apt-get update --fix-missing
RUN apt-get install -y locales && locale-gen en_US.UTF-8  
ENV LANG en_US.UTF-8  
ENV LANGUAGE en_US:en  
ENV LC_ALL en_US.UTF-8  

# Ubuntu basics
RUN apt-get -y install lsb-release build-essential git vim wget gnupg curl unzip libssl-dev libffi-dev libconfig-dev

# Waste less screen estate on the prompt.
RUN echo 'export PS1="$ "' >> $HOME/.bashrc

# Install everything in /opt
WORKDIR /opt

# Directory to install TLC and TLAPS
RUN mkdir -p tlaplus

# Install TLA+ Tools
RUN wget -qN https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar -P tlaplus/
RUN echo "alias tlcrepl='java -cp /opt/tools/tla2tools.jar:/opt/tools/tla2tools.jar tlc2.REPL'" >> $HOME/.bashrc
RUN echo "alias tlc='java -cp /opt/tools/tla2tools.jar:/opt/tools/tla2tools.jar tlc2.TLC'" >> $HOME/.bashrc

# Install TLAPS (proof system)
RUN wget -N https://github.com/tlaplus/tlapm/releases/download/v1.4.5/tlaps-1.4.5-x86_64-linux-gnu-inst.bin -P /tmp
RUN chmod +x /tmp/tlaps-1.4.5-x86_64-linux-gnu-inst.bin
RUN /tmp/tlaps-1.4.5-x86_64-linux-gnu-inst.bin -d tools/tlaps
RUN echo 'export PATH=$PATH:/opt/tools/tlaps/bin:/opt/tools/tlaps/bin' >> $HOME/.bashrc

# Java (at least for TLA+)
RUN apt -y install default-jre default-jdk
RUN echo "export JAVA_HOME=/usr/lib/jvm/java-11-openjdk-amd64" >> ~/.profile

# Clone proofs, no need to clone the entire repo
RUN git clone -n --depth=1 --filter=tree:0 https://github.com/uguryavuz/parlayhash.git
RUN cd parlayhash && git sparse-checkout set --no-cone "/proofs/*" '!/proofs/Dockerfile' && git checkout

# Set the working directory
WORKDIR /opt/parlayhash/proofs