#!/usr/bin/env python3

import os

from argparse import ArgumentParser
from os.path import abspath, dirname
from subprocess import STDOUT, check_output, CalledProcessError, TimeoutExpired
from typing import List

TOP = dirname(dirname(abspath(__file__)))
TOOL_DEFAULT_PATH = os.path.join(TOP, 'build', 'z3')
TOOL = os.getenv('TOOL', TOOL_DEFAULT_PATH)
Z3STR3_OPT = 'smt.string_solver=z3str3'
TIMEOUT = 30  # in seconds

Answer = List[str]  # prob_name, expected_ans


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


def check(prob_set_dir: str, prob_notes: List[Answer]):
    print(f'problem expected actual')
    all_checked = True
    for prob, ans in prob_notes:
        result = run_tool(f'{prob_set_dir}/{prob}')
        if result != ans:
            all_checked = False
            print(f'{prob} {ans} {result}')
    if all_checked:
        print('all checked')


def main():
    # Set argument parser
    arg_parser = ArgumentParser(description='Verify our tool using problems with known answers')
    arg_parser.add_argument('DIR', help='directory of the problems')
    arg_parser.add_argument('NOTE', help='path to the corresponding answer note')
    args = arg_parser.parse_args()

    # Run the check
    prob_set_dir = os.path.normpath(args.DIR)
    print(f'problem set dir: {prob_set_dir}')
    print(f'      tool path: {TOOL}')
    print(f'        timeout: {TIMEOUT}s')
    prob_ans_note = os.path.normpath(args.NOTE)
    note_file = open(prob_ans_note)
    prob_notes = [line.strip().split() for line in note_file.readlines()]
    check(prob_set_dir, prob_notes)


if __name__ == '__main__':
    main()
