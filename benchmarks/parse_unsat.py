#!/usr/bin/env python3
import sys
import os
_base_dir = os.path.dirname(os.path.realpath(__file__))

def main(path):
    files = sorted([os.path.join(root, file)
                              for root, dirs, files in os.walk(path) for file in files])
    
    cmd = "cvc4 --tlimit=15000 --dump-unsat-cores-full --lang smt --strings-exp --quiet "

    for f in files:
        res = os.popen(cmd + f).readlines()
        if "unsat" in res[0]:
            save = False
            for r in res:
                if "int.to.re" in r or "str.to.int" in r:
                    save = True
                    print(f)
                    break
            if not save:
                print(f + " neg")
                os.system("rm " + f)
        else:
            print(f + " " + res[0].replace("\n", ""))


if __name__ == '__main__':
    main(sys.argv[1])
