#!/usr/bin/env python3

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


class Result:
    def __init__(self, value: str, not_care: bool = False):
        self.value: str = value
        self.not_care: bool = not_care

    def __repr__(self):
        return '--' if self.not_care else self.value

    def __eq__(self, other):
        if isinstance(other, self.__class__):
            return self.not_care or other.not_care or other.value == self.value
        return False

    def denied_by(self, other: 'Result'):
        return ((other.value == 'sat' and self.value == 'unsat') or
                (other.value == 'unsat' and self.value == 'sat'))


RESULT_SAT = Result('sat')
RESULT_UNSAT = Result('unsat')
RESULT_UNKNOWN = Result('unknown')
RESULT_TIMEOUT = Result('timeout')
RESULT_NOT_CARE = Result('--', True)

Record = Tuple[str, Result, Result, Result, Result]  # prob_name, and the 4 Result
Answer = Tuple[str, Result]  # prob_name, expected_ans


def run_tool(filename: str) -> Result:
    try:
        r = str(check_output([TOOL, Z3STR3_OPT, filename], stderr=STDOUT, timeout=TIMEOUT))
    except CalledProcessError as err:
        r = str(err.output)
    except TimeoutExpired:
        return RESULT_TIMEOUT
    if 'unsat' in r:
        return RESULT_UNSAT
    elif 'sat' in r:
        return RESULT_SAT
    else:
        return RESULT_UNKNOWN


def run_cvc4(filename: str) -> Result:
    try:
        r = str(check_output([CVC4, '--lang', 'smt', filename], stderr=STDOUT, timeout=TIMEOUT))
    except CalledProcessError as err:
        r = str(err.output)
    except TimeoutExpired:
        return RESULT_TIMEOUT
    if 'unsat' in r:
        return RESULT_UNSAT
    elif 'sat' in r:
        return RESULT_SAT
    else:
        return RESULT_UNKNOWN


def run_z3str3(filename: str) -> Result:
    try:
        r = str(check_output([Z3, Z3STR3_OPT, filename], stderr=STDOUT, timeout=TIMEOUT))
    except CalledProcessError as err:
        r = str(err.output)
    except TimeoutExpired:
        return RESULT_TIMEOUT
    if 'unsat' in r:
        return RESULT_UNSAT
    elif 'sat' in r:
        return RESULT_SAT
    else:
        return RESULT_UNKNOWN


def run_z3seq(filename: str) -> Result:
    try:
        r = str(check_output([Z3, filename], stderr=STDOUT, timeout=TIMEOUT))
    except CalledProcessError as err:
        r = str(err.output)
    except TimeoutExpired:
        return RESULT_TIMEOUT
    if 'unsat' in r:
        return RESULT_UNSAT
    elif 'sat' in r:
        return RESULT_SAT
    else:
        return RESULT_UNKNOWN


def write_check_result(prob_set_path: str, prob_count: int, maybe_wrong: List[Record],
                       timeout: List[Record], inconsistent: List[Record]):
    with open(f'{os.path.basename(prob_set_path)}.result', 'w') as fp:
        fp.write(f'problem set dir: {prob_set_path}\n')
        fp.write(f'problems processed: {prob_count}\n')
        fp.write(f'\nmaybe wrong: {len(maybe_wrong)}.  (prob, tool, cvc4, z3seq, z3str3)\n')
        for e in maybe_wrong:
            fp.write(f'({e[0]}, {e[1]}, {e[2]}, {e[3]}, {e[4]})\n')
        fp.write(f'\ntimeout: {len(timeout)}.  (prob, tool, cvc4, z3seq, z3str3)\n')
        for e in timeout:
            fp.write(f'({e[0]}, {e[1]}, {e[2]}, {e[3]}, {e[4]})\n')
        fp.write(f'\ninconsistent: {len(inconsistent)}.  (prob, tool, cvc4, z3seq, z3str3)\n')
        for e in inconsistent:
            fp.write(f'({e[0]}, {e[1]}, {e[2]}, {e[3]}, {e[4]})\n')


def write_ans_note(prob_set_path: str, note: List[Answer]):
    with open(f'{os.path.basename(prob_set_path)}.note', 'w') as fp:
        for e in note:
            fp.write(f'{e[0]} {e[1]}\n')


def check_ans(prob_set_dir: str, prob_files: List[str], args):
    tool_maybe_wrong: List[Record] = []
    tool_timeout: List[Record] = []
    inconsistent: List[Record] = []
    ans_note: List[Answer] = []
    count = 0

    for file in prob_files:
        filename = f'{prob_set_dir}/{file}'
        tool = run_tool(filename)
        cvc4 = run_cvc4(filename) if args.cvc4 else RESULT_NOT_CARE
        z3seq = run_z3seq(filename) if args.z3seq else RESULT_NOT_CARE
        z3str3 = run_z3str3(filename) if args.z3str3 else RESULT_NOT_CARE
        print(f'({file}, tool, cvc4, z3seq, z3str3): (..., {tool}, {cvc4}, {z3seq}, {z3str3})')

        result = (file, tool, cvc4, z3seq, z3str3)
        if cvc4 == z3seq and cvc4 == z3str3 and z3seq == z3str3:
            ans_note.append((file, cvc4))
        if (tool != cvc4 or tool != z3seq or tool != z3str3 or
                cvc4 != z3seq or cvc4 != z3str3 or z3seq != z3str3):
            inconsistent.append(result)
        if tool == 'timeout':
            tool_timeout.append(result)
        if tool.denied_by(cvc4) or tool.denied_by(z3seq) or tool.denied_by(z3str3):
            tool_maybe_wrong.append(result)

        count += 1
        if count % 100 == 0:  # write partial result
            write_ans_note(prob_set_dir, ans_note)
            write_check_result(prob_set_dir, count, tool_maybe_wrong, tool_timeout, inconsistent)

    # write final result
    write_ans_note(prob_set_dir, ans_note)
    write_check_result(prob_set_dir, count, tool_maybe_wrong, tool_timeout, inconsistent)


def main():
    # Set argument parser
    arg_parser = ArgumentParser(description='Check the results of the tools on given problem set')
    arg_parser.add_argument('DIR', help='directory of the problem set')
    arg_parser.add_argument('--cvc4', help='run with CVC4', dest='cvc4', action='store_true')
    arg_parser.add_argument('--z3seq', help='run with z3seq', dest='z3seq', action='store_true')
    arg_parser.add_argument('--z3str3', help='run with z3str3', dest='z3str3', action='store_true')
    args = arg_parser.parse_args()

    # Run the check
    prob_set_dir = os.path.normpath(args.DIR)
    prob_files = sorted([f for f in os.listdir(prob_set_dir) if '.smt2' in f])
    prob_count = len(prob_files)
    print(f'problem set dir: {prob_set_dir}')
    print(f'    problem num: {prob_count}')
    print(f'      tool path: {TOOL}')
    print(f'        timeout: {TIMEOUT}s')

    check_ans(prob_set_dir, prob_files, args)


if __name__ == '__main__':
    main()
