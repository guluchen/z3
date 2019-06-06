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
        gcc-6-multilib \
        git \
        wget \
        tar \
        graphviz \
        g++-6-multilib \
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

# Install dotnet runtime
RUN wget -q https://packages.microsoft.com/config/ubuntu/16.04/packages-microsoft-prod.deb && \
    dpkg -i packages-microsoft-prod.deb && \
    apt-get install apt-transport-https && \
    add-apt-repository universe && \
    apt-get update && \
    apt-get -y install dotnet-sdk-2.2

# Install clang6.0
RUN wget -O - https://apt.llvm.org/llvm-snapshot.gpg.key | apt-key add - && \
	apt-add-repository "deb http://apt.llvm.org/xenial/ llvm-toolchain-xenial-6.0 main" && \
	apt-get update && \
	apt-get install -y clang-6.0 && \
	update-alternatives --install /usr/bin/clang clang /usr/bin/clang-6.0 60 --slave  /usr/bin/clang++ clang++ /usr/bin/clang++-6

# Create `user` user for container with password `user`.  and give it
# password-less sudo access
RUN useradd -m user && \
    echo user:user | chpasswd && \
    cp /etc/sudoers /etc/sudoers.bak && \
    echo 'user  ALL=(root) NOPASSWD: ALL' >> /etc/sudoers
USER user
WORKDIR /home/user
ENV ASAN_SYMBOLIZER_PATH=/usr/lib/llvm-3.9/bin/llvm-symbolizer

# Install Openfst and Apron
RUN \
    wget http://www.openfst.org/twiki/pub/FST/FstDownload/openfst-1.7.1.tar.gz && \
    tar zxvf openfst-1.7.1.tar.gz && \
    cd openfst-1.7.1 && \
    ./configure && \
    make && \
    sudo make install

RUN \
    git clone https://github.com/antoinemine/apron.git && \
    cd apron && \
    ./configure && \
    make && \
    sudo make install

# Clean up $HOME
RUN rm -rf /home/user/*

