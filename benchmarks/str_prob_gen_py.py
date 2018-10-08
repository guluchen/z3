#!/usr/bin/env python3

import sys
import os
import random
from argparse import ArgumentParser
from typing import Tuple, List

symbols = ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h']
max_num_we = 3
max_len_we = 3


Elem = Tuple[int, int]


def num_occurrence(l: List[Elem], c: Elem):
    return len([e for e in l if e == c])


def gen_elem_random() -> Elem:
    return random.randrange(0, len(symbols)), random.randrange(0, 2)  # 0 for variable, 1 for character


def print_elem(e: Elem) -> str:
    if e[1] == 0:
        return f'V({symbols[e[0]]})'
    else:
        return f'C({symbols[e[0]]})'


class ElemList:
    def __init__(self):
        self.lhs: List[Elem] = list()
        self.rhs: List[Elem] = list()

    def assign(self, l1: List[Elem], l2: List[Elem]):
        self.lhs: List[Elem] = l1
        self.rhs: List[Elem] = l2

    def __len__(self) -> int:
        return len(self.lhs) + len(self.rhs)

    def __eq__(self, other):
        if not isinstance(other, ElemList):
            return False
        if len(self) != len(other):
            return False
        if self.lhs == other.lhs and self.rhs == other.rhs:
            return True
        else:
            return False

    def __str__(self):
        return ''.join([print_elem(e) for e in self.lhs]) + ' = ' + ''.join([print_elem(e) for e in self.rhs])

    def __repr__(self):
        return str(self)

    def __hash__(self):
        return hash(str(self))

    def is_full(self):
        return len(self.lhs) == max_len_we and len(self.rhs) == max_len_we

    def num_occurrence(self, e: Elem):
        return num_occurrence(self.lhs, e) + num_occurrence(self.rhs, e)

    def put_elem(self, e: Elem) -> bool:
        if len(self.lhs) < max_len_we:
            self.lhs.append(e)
            return True
        elif len(self.rhs) < max_len_we:
            self.rhs.append(e)
            return True
        else:
            return False

    def export_smt_3(self):  # assume length is 3
        if not self.is_full():
            return ''

        elem_1 = export_elem_smt(self.lhs[0])
        elem_2 = export_elem_smt(self.lhs[1])
        elem_3 = export_elem_smt(self.lhs[2])
        elem_4 = export_elem_smt(self.rhs[0])
        elem_5 = export_elem_smt(self.rhs[1])
        elem_6 = export_elem_smt(self.rhs[2])
        return f'(assert (= (str.++ {elem_1} (str.++ {elem_2} {elem_3})) (str.++ {elem_4} (str.++ {elem_5} {elem_6}))))'

    def export_smt(self):  # assume length is 3
        if not self.is_full():
            return ''

        def export_smt_inner(idx: int, exp_str_l: str = '', exp_str_r: str = '') -> Tuple[str, str]:
            if max_len_we - idx == 1:
                assert exp_str_l == '' and exp_str_r == ''
                return export_elem_smt(self.lhs[idx]), export_elem_smt(self.rhs[idx])
            else:
                return f'(str.++ {export_elem_smt(self.lhs[idx])} {exp_str_l})', \
                       f'(str.++ {export_elem_smt(self.rhs[idx])} {exp_str_r})'

        lhs_str = ''
        rhs_str = ''
        for idx in reversed(range(max_len_we)):
            lhs_str, rhs_str = export_smt_inner(idx, lhs_str, rhs_str)

        return f'(assert (= {lhs_str} {rhs_str}))'


def export_elem_smt(e: Elem) -> str:
    if e[1] == 0:  # variable
        return symbols[e[0]]
    else:
        return f'\"{symbols[e[0]]}\"'


def export_concat(str1: str, str2: str) -> str:
    return f'(str.++ {str1} {str2})'


class Problem:
    def __init__(self):
        self.we_list: List[ElemList] = list()
        for i in range(0, max_num_we):
            self.we_list.append(ElemList())

    def __eq__(self, other) -> bool:
        if isinstance(other, Problem):
            return self.we_list == other.we_list
        else:
            return False

    def __str__(self):
        return '\n'.join([str(w) for w in self.we_list])

    def __repr__(self):
        return '.'.join([repr(w) for w in self.we_list])

    def __hash__(self):
        return hash(repr(self))

    def is_elem_quadratic_ok(self, e: Elem) -> bool:
        if sum([w.num_occurrence(e) for w in self.we_list]) < 2:
            return True
        else:
            return False

    def is_full(self):
        if len([w for w in self.we_list if not w.is_full()]) > 0:
            return False
        else:
            return True

    def put_elem(self, e: Elem):
        vacancy = [w for w in self.we_list if not w.is_full()]
        if len(vacancy) > 0:
            return vacancy[0].put_elem(e)
        else:
            return False

    def generate(self):
        while not self.is_full():
            elem = gen_elem_random()
            if elem[1] == 0:  # variable
                if self.is_elem_quadratic_ok(elem):
                    self.put_elem(elem)
            else:  # char
                self.put_elem(elem)
        return self

    def reset(self):  # same as __init__
        self.we_list: List[ElemList] = list()
        for i in range(0, max_num_we):
            self.we_list.append(ElemList())

    def variables(self):
        return {symbols[e[0]] for w in self.we_list for e in w.lhs + w.rhs if e[1] == 0}

    def export_smt(self) -> str:
        if not self.is_full():
            return ''
        var = self.variables()
        ret = ''
        for v in var:
            ret += f'(declare-fun {v} () String)\n'
        for w in self.we_list:
            ret += f'{w.export_smt()}\n'
        ret += '(check-sat)\n(get-model)'
        return ret


def main(argv):
    # Set argument parser
    arg_parser = ArgumentParser(prog=None,
                                usage=None,
                                description="A simple SMT quadratic string problem generator. "
                                            "A problem generated has three word equations "
                                            "and each word equation has three elements "
                                            "(variable or character) each side.",
                                epilog=None)
    arg_parser.add_argument("-d", "--dir", help="Path to generate problems, default is ./", dest="path", default="./")
    arg_parser.add_argument("-p", "--prefix", help="Prefix of files to be generated, default is test_",
                            dest="prefix", default="ttt_")
    arg_parser.add_argument("-n", "--num", help="Number of problems to be generated, default is 100",
                            dest="num", default="100", type=int)
    args = arg_parser.parse_args()

    print('Generating problems....')
    print(f'    dir   : {args.path}')
    print(f'    prefix: {args.prefix}')
    print(f'    num   : {args.num}')

    # short test
    # p = Problem().generate()
    # print(p)
    # print(p.export_smt())
    # exit(0)

    # Proceed problem generation
    problem_set = set()
    while len(problem_set) < args.num:
        problem_set.add(Problem().generate())
    if not os.path.exists(args.path):
        os.makedirs(args.path)
    os.chdir(args.path)
    num = 1
    for p in problem_set:
        filename = f'{args.prefix}{str(num).zfill(len(str(args.num)))}.smt2'
        with open(filename, 'w') as fp:
            fp.write(p.export_smt())
        num += 1


if __name__ == '__main__':
    main(sys.argv)
