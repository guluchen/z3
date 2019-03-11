#!/bin/bash

# Based on contrib/ci/scripts/travis_ci_entry_point.sh

SCRIPT_DIR="$( cd ${BASH_SOURCE[0]%/*} ; echo $PWD )"

set -x
set -e
set -o pipefail

: ${TRAVIS_OS_NAME?"TRAVIS_OS_NAME should be set"}

if [ "${TRAVIS_OS_NAME}" = "osx" ]; then
  echo "Unsupported OS \"${TRAVIS_OS_NAME}\""
  exit 1
elif [ "${TRAVIS_OS_NAME}" = "linux" ]; then
  ${SCRIPT_DIR}/travis_ci_linux_entry_point.sh
else
  echo "Unsupported OS \"${TRAVIS_OS_NAME}\""
  exit 1
fi
