#!/bin/bash

function install_ppl {
	wget ftp://ftp.cs.unipr.it/pub/ppl/releases/1.2/ppl-1.2.tar.xz
	tar -xf ppl-1.2.tar.xz
	cp ${SCRIPT_DIR}/ppl-1.2.patches ./
	patch -p0 < ppl-1.2.patches
	cd ppl-1.2
	./configure
	make && sudo make install
}

SCRIPT_DIR="$( cd ${BASH_SOURCE[0]%/*} ; echo $PWD )"

set -x
set -e
set -o pipefail

install_ppl
