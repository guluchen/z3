FROM ubuntu:16.04

RUN apt-get update && \
	apt-get install build-essential software-properties-common -y && \
	add-apt-repository ppa:ubuntu-toolchain-r/test && \
	apt-get update && \
	apt-get install -y -f gcc-6 g++-6 && \
	update-alternatives --install /usr/bin/gcc gcc /usr/bin/gcc-6 60 --slave  /usr/bin/g++ g++ /usr/bin/g++-6 && \
    apt-get -y --no-install-recommends install \
        binutils \
        cmake \
        doxygen \
        default-jdk \
        gcc-multilib \
        git \
        wget \
        tar \
        graphviz \
        g++-multilib \
        libgmp-dev \
        libgomp1 \
        libomp5 \
        libomp-dev \
        llvm \
        m4 \
        ppl-dev \
        libmpfr-dev \
        make \
        mono-devel \
        ninja-build \
        python3 \
        python3-setuptools \
        python2.7 \
        python-setuptools \
        sudo

# Create `user` user for container with password `user`.  and give it
# password-less sudo access
RUN useradd -m user && \
    echo user:user | chpasswd && \
    cp /etc/sudoers /etc/sudoers.bak && \
    echo 'user  ALL=(root) NOPASSWD: ALL' >> /etc/sudoers
USER user
WORKDIR /home/user
