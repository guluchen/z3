#include "smt/theory_str/theory_str2.h"
#include "util/debug.h"
#include "smt/smt_context.h"
#include "ast/seq_decl_plugin.h"
#include "ast/reg_decl_plugins.h"
#include "ast/ast_pp.h"
#include <sstream>
#include <iostream>
#include <fstream>
class string_fuzzer {
    ast_manager& m;
    smt_params params;
    smt::context& ctx;
    seq_util m_util_s;

public:
    string_fuzzer(ast_manager& m, smt::context& ctx): m{m}, ctx{ctx}, m_util_s{m} {
        srand(time(NULL));
    }


    void print_hello() {
        std::cout<<"hello\n";
    }


};

static void test_int_expr_solver(){
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_model = true;
    smt::context ctx(m, params);
    string_fuzzer str(m,ctx);

    smt::int_expr_solver m_int_solver(m, ctx.get_fparams());

    str.print_hello();

    ENSURE(false);
}




void tst_theory_str() {
    test_int_expr_solver();
}
