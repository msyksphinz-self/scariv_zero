FROM ubuntu:22.04

RUN apt update

RUN apt install -y autoconf automake autotools-dev curl libmpc-dev libmpfr-dev libgmp-dev gawk build-essential bison flex texinfo gperf libtool patchutils bc zlib1g-dev libexpat-dev
RUN apt install -y git perl python3 make autoconf g++ flex bison ccache gengetopt device-tree-compiler
RUN apt install -y libgoogle-perftools-dev numactl perl-doc
RUN apt install -y libfl2
RUN apt install -y libfl-dev
RUN apt install -y libgmp-dev libmpfr-dev libmpc-dev zlib1g-dev vim
RUN apt install -y ruby
RUN apt install -y clang ccache
RUN apt install -y git-lfs

ENV RISCV /work/riscv

# ------------------
# Install Verilator
# ------------------

RUN curl -L https://github.com/verilator/verilator/archive/refs/tags/v4.228.tar.gz | tar xz && \
    cd verilator-4.228/ && \
    autoconf && \
    ./configure && \
    make -j$(nproc) && \
    make install

# -----------------------------
# RISC-V GNUTools Install
# -----------------------------
WORKDIR /work/
RUN curl -L https://github.com/riscv-collab/riscv-gnu-toolchain/releases/download/2022.08.08/riscv64-elf-ubuntu-20.04-nightly-2022.08.08-nightly.tar.gz   | tar xz
# RUN curl -L https://github.com/riscv-collab/riscv-gnu-toolchain/releases/download/2022.08.08/riscv64-glibc-ubuntu-20.04-nightly-2022.08.08-nightly.tar.gz | tar xz
# RUN curl -L https://github.com/riscv-collab/riscv-gnu-toolchain/releases/download/2022.08.08/riscv64-musl-ubuntu-20.04-nightly-2022.08.08-nightly.tar.gz  | tar xz

ENV PATH            $RISCV/bin:$PATH
ENV LD_LIBRARY_PATH $RISCV/lib:$LD_LIBRARY_PATH
ENV CCACHE_DIR      "work/scariv/ccache"
