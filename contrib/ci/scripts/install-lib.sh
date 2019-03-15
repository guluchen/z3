#!/bin/bash

function install_openfst {
	wget http://www.openfst.org/twiki/pub/FST/FstDownload/openfst-1.7.1.tar.gz
	tar zxvf openfst-1.7.1.tar.gz
	cd openfst-1.7.1
	./configure
	make
	sudo make install
	cd ../
}

function install_apron {
	git clone https://github.com/antoinemine/apron.git
	cd apron
	./configure
	make
	sudo make install
	cd ../
}

SCRIPT_DIR="$( cd ${BASH_SOURCE[0]%/*} ; echo $PWD )"
. ${SCRIPT_DIR}/run_quiet.sh

set -x
set -e
set -o pipefail

# Install openfst
echo "Installing Openfst..."
install_openfst

# Install Apron
echo "Installing Apron..."
install_apron
