#!/usr/bin/env python3

"""
A Python script to handle given problem set with our tool, and standard cvc4, z3 (found in PATH),
then compare their outcomes.

Usage:
    check_ans.py path_to_problems

Note:
    The problem set should be contained in a directory (as specified).
    Each problem file name should have file extension `.smt2`.

Result output:
    The result will be written in a file named `path_to_problems.result`.
"""

import os

from argparse import ArgumentParser
from os.path import abspath, dirname
from subprocess import STDOUT, check_output, CalledProcessError, TimeoutExpired
from typing import Tuple, List

TOP = dirname(dirname(abspath(__file__)))
TOOL_DEFAULT_PATH = os.path.join(TOP, 'build', 'z3')
TOOL = os.getenv('TOOL', TOOL_DEFAULT_PATH)
CVC4 = os.getenv('CVC4', 'cvc4')
Z3 = os.getenv('Z3', 'z3')
Z3STR3_OPT = 'smt.string_solver=z3str3'
TIMEOUT = 30  # in seconds

Result = Tuple[str, str, str, str, str]  # filename & the 4 outcomes
AnsNote = Tuple[str, str]  # filename & the almost sure answer


def run_tool(filename: str) -> str:
    try:
        r = str(check_output([TOOL, Z3STR3_OPT, filename], stderr=STDOUT, timeout=TIMEOUT))
    except CalledProcessError as err:
        r = str(err.output)
    except TimeoutExpired:
        return 'timeout'
    if 'unsat' in r:
        return 'unsat'
    elif 'sat' in r:
        return 'sat'
    else:
        return 'unknown'


def run_cvc4(filename: str) -> str:
    try:
        r = str(check_output([CVC4, '--lang', 'smt', filename], stderr=STDOUT, timeout=TIMEOUT))
    except CalledProcessError as err:
        r = str(err.output)
    except TimeoutExpired:
        return 'timeout'
    if 'unsat' in r:
        return 'unsat'
    elif 'sat' in r:
        return 'sat'
    else:
        return 'unknown'


def run_z3str3(filename: str) -> str:
    try:
        r = str(check_output([Z3, Z3STR3_OPT, filename], stderr=STDOUT, timeout=TIMEOUT))
    except CalledProcessError as err:
        r = str(err.output)
    except TimeoutExpired:
        return 'timeout'
    if 'unsat' in r:
        return 'unsat'
    elif 'sat' in r:
        return 'sat'
    else:
        return 'unknown'


def run_z3(filename: str) -> str:
    try:
        r = str(check_output([Z3, filename], stderr=STDOUT, timeout=TIMEOUT))
    except CalledProcessError as err:
        r = str(err.output)
    except TimeoutExpired:
        return 'timeout'
    if 'unsat' in r:
        return 'unsat'
    elif 'sat' in r:
        return 'sat'
    else:
        return 'unknown'


def write_check_result(prob_set_path: str, prob_count: int, maybe_wrong: List[Result],
                       timeout: List[Result], inconsistent: List[Result]):
    with open(f'{os.path.basename(prob_set_path)}.result', 'w') as fp:
        fp.write(f'problem set path: {prob_set_path}\n')
        fp.write(f'problems processed: {prob_count}\n')
        fp.write(f'\nmaybe wrong: {len(maybe_wrong)}.  format: (prob, tool, cvc4, z3, z3str3)\n')
        for e in maybe_wrong:
            fp.write(f'({e[0]}, {e[1]}, {e[2]}, {e[3]}, {e[4]})\n')
        fp.write(
            f'\ntimeout: {len(timeout)}.  format: (prob, tool, cvc4, z3, z3str3)\n')
        for e in timeout:
            fp.write(f'({e[0]}, {e[1]}, {e[2]}, {e[3]}, {e[4]})\n')
        fp.write(f'\ninconsistent: {len(inconsistent)}.  format: (prob, tool, cvc4, z3, z3str3)\n')
        for e in inconsistent:
            fp.write(f'({e[0]}, {e[1]}, {e[2]}, {e[3]}, {e[4]})\n')


def write_ans_note(prob_set_path: str, note: List[AnsNote]):
    with open(f'{os.path.basename(prob_set_path)}.note', 'w') as fp:
        for e in note:
            fp.write(f'{e[0]} {e[1]}\n')


def check_ans(prob_set_path: str, prob_names: List[str]):
    tool_maybe_wrong: List[Result] = []
    tool_timeout: List[Result] = []
    inconsistent: List[Result] = []
    ans_note: List[AnsNote] = []
    count = 0

    for name in prob_names:
        filename = f'{prob_set_path}/{name}'
        tool = run_tool(filename)
        cvc4 = run_cvc4(filename)
        z3 = run_z3(filename)
        z3str3 = run_z3str3(filename)
        print(f'({name}, tool, cvc4, z3, z3str3): (..., {tool}, {cvc4}, {z3}, {z3str3})')

        result = (name, tool, cvc4, z3, z3str3)
        if cvc4 == z3 and z3 == z3str3:
            ans_note.append((name, cvc4))
        if (tool != cvc4 or tool != z3 or tool != z3str3 or
                cvc4 != z3 or cvc4 != z3str3 or z3 != z3str3):
            inconsistent.append(result)
        if tool == 'timeout':
            tool_timeout.append(result)
        if ((tool == 'sat' and cvc4 == 'unsat') or (tool == 'unsat' and cvc4 == 'sat') or
                (tool == 'sat' and z3 == 'unsat') or (tool == 'unsat' and z3 == 'sat') or
                (tool == 'sat' and z3str3 == 'unsat') or (tool == 'unsat' and z3str3 == 'sat')):
            tool_maybe_wrong.append(result)

        count += 1
        if count % 1000 == 0:  # write partial result
            write_ans_note(prob_set_path, ans_note)
            write_check_result(prob_set_path, count, tool_maybe_wrong, tool_timeout, inconsistent)

    # write final result
    write_ans_note(prob_set_path, ans_note)
    write_check_result(prob_set_path, count, tool_maybe_wrong, tool_timeout, inconsistent)


def main():
    # Set argument parser
    arg_parser = ArgumentParser(prog=None,
                                usage=None,
                                description="Handle given problems with our tool, cvc4, z3 and "
                                            "compare them.",
                                epilog=None)
    arg_parser.add_argument("prob_set_path", help="path to the problems")
    args = arg_parser.parse_args()

    # Run the check
    prob_set_path = os.path.normpath(args.prob_set_path)
    prob_names = sorted([f for f in os.listdir(prob_set_path) if '.smt2' in f])
    prob_count = len(prob_names)
    print(f'  problem set path: {prob_set_path}')
    print(f'number of problems: {prob_count}')

    check_ans(prob_set_path, prob_names)


if __name__ == '__main__':
    main()
