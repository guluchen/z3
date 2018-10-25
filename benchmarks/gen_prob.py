#!/usr/bin/env python3

import random
import os

from argparse import ArgumentParser
from typing import Tuple, List

Elem = Tuple[int, int]
symbols = ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h']
max_elems = 6
min_elems = 1
max_num_we = 3


def random_elem_len() -> int:
    return random.randrange(min_elems, max_elems + 1)


def num_occurrence(l: List[Elem], c: Elem):
    return len([e for e in l if e == c])


def gen_elem_random() -> Elem:
    return random.randrange(0, len(symbols)), random.randrange(0, 2)  # 0: var, 1: const


def print_elem(e: Elem) -> str:
    if e[1] == 0:
        return f'V({symbols[e[0]]})'
    else:
        return f'C({symbols[e[0]]})'


class ElemList:
    def __init__(self):
        self.lhs: List[Elem] = list()
        self.rhs: List[Elem] = list()
        self.lhs_len = random_elem_len()
        self.rhs_len = random_elem_len()

    def assign(self, l1: List[Elem], l2: List[Elem]):
        self.lhs: List[Elem] = l1
        self.rhs: List[Elem] = l2
        self.lhs_len = len(l1)
        self.rhs_len = len(l2)

    def __len__(self) -> int:
        return len(self.lhs) + len(self.rhs)

    def __eq__(self, other):
        if not isinstance(other, ElemList):
            return False
        if len(self) != len(
                other) or self.lhs_len != other.lhs_len or self.rhs_len != other.rhs_len:
            return False
        if self.lhs == other.lhs and self.rhs == other.rhs:
            return True
        else:
            return False

    def __str__(self):
        return ''.join([print_elem(e) for e in self.lhs]) + ' = ' + ''.join(
            [print_elem(e) for e in self.rhs])

    def __repr__(self):
        return str(self)

    def __hash__(self):
        return hash(str(self))

    def is_full(self):
        return len(self.lhs) == self.lhs_len and len(self.rhs) == self.rhs_len

    def num_occurrence(self, e: Elem):
        return num_occurrence(self.lhs, e) + num_occurrence(self.rhs, e)

    def put_elem(self, e: Elem) -> bool:
        if len(self.lhs) < self.lhs_len:
            self.lhs.append(e)
            return True
        elif len(self.rhs) < self.rhs_len:
            self.rhs.append(e)
            return True
        else:
            return False

    def export_smt(self):
        assert self.is_full()

        if self.lhs_len == 1:
            lhs_str = export_elem_smt(self.lhs[0])
        else:
            lhs_str = '(str.++ ' + ' '.join([export_elem_smt(e) for e in self.lhs]) + ')'
        if self.rhs_len == 1:
            rhs_str = export_elem_smt(self.rhs[0])
        else:
            rhs_str = '(str.++ ' + ' '.join([export_elem_smt(e) for e in self.rhs]) + ')'

        return f'(assert (= {lhs_str} {rhs_str}))'


def export_elem_smt(e: Elem) -> str:
    if e[1] == 0:  # variable
        return symbols[e[0]]
    else:
        return f'\"{symbols[e[0]]}\"'


def export_smt_elems(idx: int, max_len: int, elems: List[Elem], exp_str: str = '') -> str:
    if max_len - idx == 1:
        assert exp_str == ''
        return export_elem_smt(elems[idx])
    else:
        return f'(str.++ {export_elem_smt(elems[idx])} {exp_str})'


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

    def num_occurrence(self, e: Elem) -> int:
        return sum([w.num_occurrence(e) for w in self.we_list])

    def is_quadratic(self):
        return True in \
               {self.num_occurrence(v) <= 2 for v in
                {e for w in self.we_list for e in w.lhs + w.rhs if e[1] == 0}}

    def put_elem(self, e: Elem):
        vacancy = [w for w in self.we_list if not w.is_full()]
        if len(vacancy) > 0:
            return vacancy[0].put_elem(e)
        else:
            return False

    def generate_quadratic(self):
        while not self.is_full():
            elem = gen_elem_random()
            if elem[1] == 0 and self.is_elem_quadratic_ok(elem):  # check quadratic before add
                self.put_elem(elem)
            else:  # char or quadratic not set
                self.put_elem(elem)
        return self

    def generate(self):
        while not self.is_full():
            elem = gen_elem_random()
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


def main():
    # Set argument parser
    arg_parser = ArgumentParser(prog=None,
                                usage=None,
                                description="A simple SMT (quadratic) string problem generator.",
                                epilog=None)
    arg_parser.add_argument("-d", "--dir", help="path to generate problems, default is `./`",
                            dest="path", default="./")
    arg_parser.add_argument("-p", "--prefix",
                            help="prefix of files to be generated, default is `ttt_`",
                            dest="prefix", default="ttt_")
    arg_parser.add_argument("-n", "--num",
                            help="number of problems to be generated, default is 100",
                            dest="num", default="100", type=int)
    arg_parser.add_argument("-q", "--quadratic",
                            help="generate quadratic problems, default is on",
                            dest="quadratic", default="on")
    args = arg_parser.parse_args()

    print('Generating problems....')
    print(f'   output dir: {args.path}')
    print(f'  file prefix: {args.prefix}')
    print(f'  problem num: {args.num}')
    print(f'    quadratic: {args.quadratic}')

    # Proceed problem generation
    problem_set = set()
    quadratic_flag = args.quadratic == 'on'
    if quadratic_flag:  # generate set of quadratic problems
        while len(problem_set) < args.num:
            problem_set.add(Problem().generate_quadratic())
    else:  # generate set of non-quadratic problems (at least one variable is non-quadratic)
        while len(problem_set) < args.num:
            prob = Problem().generate()
            if not prob.is_quadratic():
                problem_set.add(prob)
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
    main()
