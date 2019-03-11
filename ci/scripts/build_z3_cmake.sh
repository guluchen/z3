#!/bin/bash

SCRIPT_DIR="$( cd ${BASH_SOURCE[0]%/*} ; echo $PWD )"

set -x
set -e
set -o pipefail

: ${Z3_SRC_DIR?"Z3_SRC_DIR must be specified"}
: ${Z3_BUILD_DIR?"Z3_BUILD_DIR must be specified"}

mkdir -p "${Z3_BUILD_DIR}"
cd "${Z3_BUILD_DIR}"
cmake "${Z3_SRC_DIR}"
make
