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


def check(prob_set_path: str, prob_notes: List[List[str]]):
    print(f'problem expected actual')
    all_checked = True
    for prob, ans in prob_notes:
        result = run_tool(f'{prob_set_path}/{prob}')
        if result != ans:
            all_checked = False
            print(f'{prob} {ans} {result}')
    if all_checked:
        print('all checked')


def main():
    # Set argument parser
    arg_parser = ArgumentParser(prog=None,
                                usage=None,
                                description="Verify our tool using problems with known answers",
                                epilog=None)
    arg_parser.add_argument("prob_set_path", help="path to the problems")
    arg_parser.add_argument("prob_ans_note", help="path to the answer note")
    args = arg_parser.parse_args()

    # Run the check
    prob_set_path = os.path.normpath(args.prob_set_path)
    print(f'problem set path: {prob_set_path}')
    prob_ans_note = os.path.normpath(args.prob_ans_note)
    note_file = open(prob_ans_note)
    prob_notes = [line.strip().split() for line in note_file.readlines()]
    check(prob_set_path, prob_notes)


if __name__ == '__main__':
    main()
