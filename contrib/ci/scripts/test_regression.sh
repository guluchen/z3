#!/bin/bash

function run_test() { #line
    _TARGET=$1
    if [ "$(echo $_TARGET | grep unsat)" == "" ]
    then
        _EXPECT="sat"
    else
        _EXPECT="unsat"
    fi
    _TARGET_F=${Z3_BENCHMARK_DIR}/regression/$_TARGET
    _LOG=ans.log
    if [ "${TRAVIS_OS_NAME}" = "osx" ]; then
        gtimeout 20 ${Z3_BUILD_DIR}/z3 smt.string_solver=z3str3 $_TARGET_F &> $_LOG
    else
        timeout 20 ${Z3_BUILD_DIR}/z3 smt.string_solver=z3str3 $_TARGET_F &> $_LOG
    fi
    _ANS="$(cat ${_LOG} | tail -n 1)"

    if [ "$_ANS" == "" ]
    then
        echo "==="
        echo ""
        echo "$_TARGET timeout"
        echo "LOG: "
        cat $_LOG
        exit 1
    elif [ "$_ANS" == "$_EXPECT" ]
    then
        echo "SUCCESS: $_TARGET"
    else
        echo "==="
        echo ""
        echo "$_TARGET shoud be '$_EXPECT' but return '$_ANS'"
        echo "LOG: "
        cat $_LOG
        exit 1
    fi
}

SCRIPT_DIR="$( cd ${BASH_SOURCE[0]%/*} ; echo $PWD )"
set -o pipefail

echo "Starting regression test..."

GET_TARGETS="ls ${Z3_BENCHMARK_DIR}/regression/"
$GET_TARGETS | while read -r line; do \
    run_test $line; done
