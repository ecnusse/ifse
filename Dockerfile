FROM ghcr.io/klee/llvm:130_O_D_A_ubuntu_jammy-20230126 as llvm_base
FROM ghcr.io/klee/gtest:1.11.0_ubuntu_jammy-20230126 as gtest_base
FROM ghcr.io/klee/uclibc:klee_uclibc_v1.3_130_ubuntu_jammy-20230126 as uclibc_base
FROM ghcr.io/klee/tcmalloc:2.9.1_ubuntu_jammy-20230126 as tcmalloc_base
FROM ghcr.io/klee/stp:2.3.3_ubuntu_jammy-20230126 as stp_base
FROM ghcr.io/klee/z3:4.8.15_ubuntu_jammy-20230126 as z3_base
FROM ghcr.io/klee/libcxx:130_ubuntu_jammy-20230126 as libcxx_base
FROM ghcr.io/klee/sqlite:3400100_ubuntu_jammy-20230126 as sqlite3_base

FROM llvm_base as ifse_base
COPY --from=gtest_base /tmp /tmp/
COPY --from=uclibc_base /tmp /tmp/
COPY --from=tcmalloc_base /tmp /tmp/
COPY --from=stp_base /tmp /tmp/
COPY --from=z3_base /tmp /tmp/
COPY --from=libcxx_base /tmp /tmp/
COPY --from=sqlite3_base /tmp /tmp/

RUN ln -s /tmp/llvm-130-install_O_D_A/lib/libLLVM-13.so /usr/lib/libLLVM-13.so

ENV COVERAGE=0
ENV USE_TCMALLOC=1
ENV BASE=/tmp
ENV LLVM_VERSION=13.0
ENV ENABLE_DOXYGEN=1
ENV ENABLE_OPTIMIZED=1
ENV ENABLE_DEBUG=1
ENV DISABLE_ASSERTIONS=0
ENV REQUIRES_RTTI=0
ENV SOLVERS=STP:Z3
ENV GTEST_VERSION=1.11.0
ENV UCLIBC_VERSION=klee_uclibc_v1.3
ENV TCMALLOC_VERSION=2.9.1
ENV SANITIZER_BUILD=
ENV STP_VERSION=2.3.3
ENV MINISAT_VERSION=master
ENV Z3_VERSION=4.8.15
ENV USE_LIBCXX=1
ENV KLEE_RUNTIME_BUILD="Debug+Asserts"
ENV SQLITE_VERSION=3400100
LABEL maintainer="KLEE Developers"

RUN sed -E 's/http:\/\/(archive|security)\.ubuntu\.com/http:\/\/mirror.sjtu.edu.cn/g' -i /etc/apt/sources.list

# TODO remove adding sudo package
# Create ``user`` user for container with password ``user``.
# and give it password-less sudo access (temporarily so we can use the CI scripts)
RUN apt update && DEBIAN_FRONTEND=noninteractive apt -y --no-install-recommends install sudo emacs-nox vim-nox file python3-dateutil && \
    rm -rf /var/lib/apt/lists/* && \
    useradd -m user && \
    echo user:user | chpasswd && \
    cp /etc/sudoers /etc/sudoers.bak && \
    echo 'user  ALL=(root) NOPASSWD: ALL' >> /etc/sudoers

ENV PATH="$PATH:/tmp/llvm-130-install_O_D_A/bin/"

USER user
WORKDIR /home/user

FROM ifse_base as development

RUN sudo ln -s "/tmp/"

RUN sudo apt-get update && sudo apt-get install -y openssh-server gdb gdbserver rsync vim git cmake \
    ninja-build libgoogle-perftools-dev libsqlite3-dev python3-pip python-is-python3 gcc-multilib \
    g++-multilib python3-tabulate clangd curl
RUN sudo pip config set global.index-url https://mirror.nju.edu.cn/pypi/web/simple
RUN sudo pip install lit

RUN echo "root:user" | sudo chpasswd
RUN sudo sed -r -i 's/#?\s*PermitRootLogin prohibit-password/PermitRootLogin yes/' /etc/ssh/sshd_config

RUN mkdir -p /home/user/ifse
RUN sudo chsh root -s /bin/bash
RUN sudo ln -s /home/user/ifse /root/ifse
WORKDIR /home/user/ifse

USER root
RUN curl --proto '=https' --tlsv1.2 https://sh.rustup.rs -sSf > /tmp/rustup-init.sh
RUN sh /tmp/rustup-init.sh -y --default-toolchain 1.78.0

RUN apt install libncurses-dev -y
WORKDIR /tmp/klee-uclibc-130
RUN make clean
RUN sed -E 's/include \$\(libc_DIR\)\/string\/Makefile.in/#\0/' -i libc/Makefile.in
RUN mv /tmp/klee-uclibc-130/libc/string /tmp/klee-uclibc-130/libc/_string
RUN ./configure -l
RUN make
RUN rm -rf /root/.cargo/registry/index
RUN rm -rf /root/.cargo/registry/cache

# COPY ./ifse /home/user/ifse
# COPY ./coreutils-test /home/user/coreutils-test
# COPY ./README.md /home/user/README.md

COPY ./ /home/user/

WORKDIR /home/user/ifse
