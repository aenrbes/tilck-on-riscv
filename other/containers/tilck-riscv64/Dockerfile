# version: v1
FROM ubuntu:22.04

# We don't want any of the interactive features of apt, so we just disable them.
ENV DEBIAN_FRONTEND=noninteractive

# Install the required system packages
RUN apt update && apt upgrade -y && \
apt install -y git-core gcc g++ gcc-multilib g++-multilib clang cmake \
python3-minimal python3-serial python3-pip gawk unzip parted wget \
curl qemu-system-riscv64 bison flex libssl-dev device-tree-compiler

# Checkout the Tilck project to /tilck-tmp
RUN git clone https://github.com/vvaltchev/tilck.git /tilck-tmp

# -------------------------------------------------------------------------

# Create the shared directories we'll need for all the toolchains
RUN mkdir -p /tc/cache && \
mkdir -p /tc/host_x86_64 && \
mkdir -p /tc/noarch && \
mkdir -p /tc/toolchain2-gcc113 && \
mkdir -p /tc/toolchain2-gcc123 && \
mkdir -p /tc/toolchain2-gcc133 && \
ln -s /tc/cache /tc/toolchain2-gcc113/cache && \
ln -s /tc/cache /tc/toolchain2-gcc123/cache && \
ln -s /tc/cache /tc/toolchain2-gcc133/cache && \
ln -s /tc/noarch /tc/toolchain2-gcc113/noarch && \
ln -s /tc/noarch /tc/toolchain2-gcc123/noarch && \
ln -s /tc/noarch /tc/toolchain2-gcc133/noarch && \
ln -s /tc/host_x86_64 /tc/toolchain2-gcc113/host_x86_64 && \
ln -s /tc/host_x86_64 /tc/toolchain2-gcc123/host_x86_64 && \
ln -s /tc/host_x86_64 /tc/toolchain2-gcc133/host_x86_64


# -------------------------------------------------------------------------
ARG TCROOT=/tc/toolchain2-gcc113
ARG GCC_TC_VER=11.3.0
ARG ARCH=riscv64
RUN /tilck-tmp/scripts/build_toolchain && \
/tilck-tmp/scripts/build_toolchain
# -------------------------------------------------------------------------
ARG TCROOT=/tc/toolchain2-gcc123
ARG GCC_TC_VER=12.3.0
ARG ARCH=riscv64
RUN /tilck-tmp/scripts/build_toolchain && \
/tilck-tmp/scripts/build_toolchain
# -------------------------------------------------------------------------
ARG TCROOT=/tc/toolchain2-gcc133
ARG GCC_TC_VER=13.3.0
ARG ARCH=riscv64
RUN /tilck-tmp/scripts/build_toolchain && \
/tilck-tmp/scripts/build_toolchain

# Remove Tilck's source and the toolchain cache to save space
RUN rm -rf /tilck-tmp && rm -rf /tc/cache
