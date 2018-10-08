for f in $(find * -name '*.smt2'); do
        echo $f
        /Users/yfc/fromGit/z3/cmake-build-debug/z3 -tr:str smt.string_solver=z3str3 $f|grep unsat|wc -l
	/opt/local/bin/cvc4 $f 2>/dev/null |grep unsat|wc -l
done
