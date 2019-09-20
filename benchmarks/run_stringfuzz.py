#!/usr/bin/env python3

import os

from argparse import ArgumentParser
from glob import glob
from os.path import abspath, dirname
from subprocess import STDOUT, CalledProcessError, check_output

WORKSPACE_DIR = dirname(dirname(dirname(abspath(__file__))))
STRINGFUZZ_DEFAULT_PATH = os.path.join(WORKSPACE_DIR, 'stringfuzz', 'bin')
STRINGFUZZ_PATH = os.getenv('STRINGFUZZ_PATH', STRINGFUZZ_DEFAULT_PATH)
GENERATOR = os.path.join(STRINGFUZZ_PATH, 'stringfuzzg')
MERGER = os.path.join(STRINGFUZZ_PATH, 'stringmerge')


def handle_merge(args):
    output_dir = args.d
    output_prefix = args.p
    tgt_files = []
    for d in args.DIR:
        tgt_files.append(sorted(glob(os.path.join(d, '*.smt2'))))
    workspace = os.getcwd()
    os.makedirs(output_dir) if not os.path.exists(output_dir) else None
    os.chdir(output_dir)

    available_merge_num = min(map(len, tgt_files))
    for i in range(available_merge_num):
        files = list(map(lambda l: os.path.join(workspace, l.pop(0)), tgt_files))
        cmd = [MERGER, *files, 'simple']
        output_name = f'{output_prefix}{str(i).zfill(len(str(available_merge_num)))}.smt2'
        with open(output_name, 'w') as fp:
            try:
                fp.write(check_output(cmd, stderr=STDOUT, universal_newlines=True))
            except CalledProcessError as err:
                print('Called process error:')
                print(err.output)


def handle_equality(args):
    output_dir = args.d
    output_prefix = args.p
    prob_num = int(args.NUM)
    expr_num = args.ne
    os.makedirs(output_dir) if not os.path.exists(output_dir) else None
    os.chdir(output_dir)

    param = ['-t', '4', '-n', expr_num, '-p', '2', '-s', '2', '-rm']  # default
    cmd = [GENERATOR, '-r', 'equality'] + param
    for i in range(prob_num):
        output_name = f'{output_prefix}{str(i).zfill(len(str(prob_num)))}.smt2'
        with open(output_name, 'w') as fp:
            try:
                fp.write(check_output(cmd, stderr=STDOUT, universal_newlines=True))
            except CalledProcessError as err:
                print('Called process error:')
                print(err.output)


def handle_regex(args):
    output_dir = args.d
    output_prefix = args.p
    prob_num = int(args.NUM)
    tgt_var = 'var' + args.v
    os.makedirs(output_dir) if not os.path.exists(output_dir) else None
    os.chdir(output_dir)

    param = ['-d', '1', '-o', 'spuic', '-i', 'random']  # default
    cmd = [GENERATOR, '-r', 'regex'] + param
    for i in range(prob_num):
        output_name = f'{output_prefix}{str(i).zfill(len(str(prob_num)))}.smt2'
        with open(output_name, 'w') as fp:
            try:
                result = check_output(cmd, stderr=STDOUT, universal_newlines=True)
                fp.write(result.replace('var0', tgt_var))
            except CalledProcessError as err:
                print('Called process error:')
                print(err.output)


def main():
    parser = ArgumentParser(description='A SMT string problem generator backed by StringFuzz')
    parser.add_argument('-d', '--dir',
                        help='path to output problems (default: \'./prob\')',
                        dest='d', default='./prob')
    parser.add_argument('-p', '--prefix',
                        help='prefix of the output names (default: \'ttt_\')',
                        dest='p', default='ttt_')

    subparsers = parser.add_subparsers(title='available actions', help='choose the action')
    parser_merge = subparsers.add_parser('merge', help='run stringmerge')
    parser_merge.add_argument('DIR', nargs='+', help='problem sets to merge')
    parser_merge.set_defaults(func=handle_merge)
    parser_equality = subparsers.add_parser('equality', help='run stringfuzzg equality')
    parser_equality.add_argument('NUM', help='number of the problems to generate')
    parser_equality.add_argument('-n', '--num-expr',
                                 help='number of the expressions included (default: 2)',
                                 dest='ne', default='2')
    parser_equality.set_defaults(func=handle_equality)
    parser_regex = subparsers.add_parser('regex', help='run stringfuzzg regex')
    parser_regex.add_argument('NUM', help='number of the problems to generate')
    parser_regex.add_argument('-v', '--tgt-var',
                              help='target variable id (default: 0)',
                              dest='v', default='0')
    parser_regex.set_defaults(func=handle_regex)

    args = parser.parse_args()
    print(f'file prefix: {args.p}')
    print(f' output dir: {args.d}')
    args.func(args)


if __name__ == '__main__':
    main()
