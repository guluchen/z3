#include "smt/smt_context.h"
#include "smt/theory_trau.h"

namespace smt {
    static void test_name() {
        ast_manager   m_manager;
        theory_str_params params;

        theory_trau solver(m_manager, params);
        SASSERT(solver.get_name() == "trau");


    }

    static void test_your_test_here() {

    }


}

void tst_theory_trau() {
    smt::test_name();
    smt::test_your_test_here();
}
