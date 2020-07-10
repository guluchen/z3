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
    string_fuzzer(ast_manager& m, smt::context& ctx) : m{ m }, ctx{ ctx }, m_util_s{ m } {
        srand(time(NULL));
    }


    void print_hello() {
        std::cout << "hello\n";
    }


};

static void test_int_expr_solver() {
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_model = true;
    smt::context ctx(m, params);
    string_fuzzer str(m, ctx);

    arith_util m_util_a(m);
    seq_util m_util_s(m);
    

    //smt::theory_str2 theory_str_2_class(m, params);

    smt::int_expr_solver m_int_solver(m, ctx.get_fparams());

    //
    // Part 1
    //
    expr_ref int_formula(m.mk_true(), m);

    int n = 5;
    expr_ref x_sum(smt::theory_str2::mk_int_var("x0", ctx, m, m_util_a, m_util_s), m);
    for (int i = 0; i < n; i++)
    {
        expr_ref x(smt::theory_str2::mk_int_var("x" + std::to_string(i), ctx, m, m_util_a, m_util_s), m);
        int_formula = m.mk_and(int_formula, m_util_a.mk_eq(m_util_a.mk_int(1), x));
    }
    for (int i = 1; i < n; i++)
    {
        expr_ref x(smt::theory_str2::mk_int_var("x" + std::to_string(i), ctx, m, m_util_a, m_util_s), m);
        x_sum = m_util_a.mk_add(x_sum, x);
    }
    int_formula = m.mk_and(int_formula, m_util_a.mk_eq(x_sum, m_util_a.mk_int(5)));


    bool result = m_int_solver.check_sat(int_formula) == lbool::l_true;
    
    ENSURE(result);
    std::cout << "test_int_expr_solver (Part-1): tested.\n";

    //
    // Part 2
    //
    expr_ref int_formula_2(m.mk_true(), m);

    expr_ref y_sum(smt::theory_str2::mk_int_var("y0", ctx, m, m_util_a, m_util_s), m);
    for (int i = 0; i < n; i++)
    {
        expr_ref y(smt::theory_str2::mk_int_var("y" + std::to_string(i), ctx, m, m_util_a, m_util_s), m);
        int_formula_2 = m.mk_and(int_formula_2, m_util_a.mk_eq(m_util_a.mk_int(1), y));
    }
    int_formula_2 = m.mk_and(int_formula_2, m_util_a.mk_eq(y_sum, m_util_a.mk_int(1)));
    for (int i = 1; i < n; i++)
    {
        expr_ref y(smt::theory_str2::mk_int_var("y" + std::to_string(i), ctx, m, m_util_a, m_util_s), m);
        y_sum = m_util_a.mk_add(y_sum, y);
        int_formula_2 = m.mk_and(int_formula_2, m_util_a.mk_ge(y_sum, m_util_a.mk_int(i+1)));
    }
    //int_formula_2 = m.mk_and(int_formula_2, m_util_a.mk_eq(y_sum, m_util_a.mk_int(5)));

    result = m_int_solver.check_sat(int_formula_2) == lbool::l_true;

    ENSURE(result);
    std::cout << "test_int_expr_solver (Part-2): tested.\n";
}



static void func_test_word_term_to_list() {

    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_model = true;
    smt::context ctx(m, params);

    arith_util m_util_a(m);
    seq_util m_util_s(m);

    smt::int_expr_solver m_int_solver(m, ctx.get_fparams());

    unsigned loop_size = 2;
    unsigned num_loop = 1;

    std::list<std::pair<char, std::string>>  L_term, R_term;
    L_term.push_back(std::make_pair('V', "x"));
    R_term.push_back(std::make_pair('S', "abc"));

    smt::theory_str2 str2_class(m, ctx.get_fparams());



    //bool result = m_int_solver.check_sat(int_formula) == lbool::l_true;
    bool result = false;
    ENSURE(result);
    std::cout << "func_test_word_term_to_list: tested.\n";
}


static void str_str_symbol_match_to_expr_ref_func_test_1(){
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_model = true;
    smt::context ctx(m, params);

    arith_util m_util_a(m);
    seq_util m_util_s(m);

    smt::theory_str2 str2_class(m, ctx.get_fparams());
    smt::int_expr_solver m_int_solver(m, ctx.get_fparams());



    //
    // Part 1
    //
    expr_ref int_formula(m.mk_true(), m);
    expr_ref L_pre_len(smt::theory_str2::mk_int_var("L_pre_len", ctx, m, m_util_a, m_util_s), m);
    int_formula = m.mk_and(int_formula, m_util_a.mk_eq(L_pre_len, m_util_a.mk_int(0)));
    expr_ref R_pre_len(smt::theory_str2::mk_int_var("R_pre_len", ctx, m, m_util_a, m_util_s), m);
    int_formula = m.mk_and(int_formula, m_util_a.mk_eq(R_pre_len, m_util_a.mk_int(0)));



    str2_class.str_str_symbol_match_to_expr_ref(int_formula, L_pre_len, R_pre_len, "abc", "abcde", ctx, m);

    

    bool result = m_int_solver.check_sat(int_formula) == lbool::l_true;
    ENSURE(result);
}

static void str_str_symbol_match_to_expr_ref_func_test_2() {
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_model = true;
    smt::context ctx(m, params);

    arith_util m_util_a(m);
    seq_util m_util_s(m);

    smt::theory_str2 str2_class(m, ctx.get_fparams());
    smt::int_expr_solver m_int_solver(m, ctx.get_fparams());


    expr_ref int_formula(m.mk_true(), m);
    expr_ref L_pre_len(smt::theory_str2::mk_int_var("L_pre_len", ctx, m, m_util_a, m_util_s), m);
    int_formula = m.mk_and(int_formula, m_util_a.mk_eq(L_pre_len, m_util_a.mk_int(0)));
    expr_ref R_pre_len(smt::theory_str2::mk_int_var("R_pre_len", ctx, m, m_util_a, m_util_s), m);
    int_formula = m.mk_and(int_formula, m_util_a.mk_eq(R_pre_len, m_util_a.mk_int(0)));



    str2_class.str_str_symbol_match_to_expr_ref(int_formula, L_pre_len, R_pre_len, "afc", "abcde", ctx, m);

    int_formula = m.mk_not(int_formula);

    bool result = m_int_solver.check_sat(int_formula) == lbool::l_true;
    ENSURE(result);
}


static void str_str_symbol_match_to_expr_ref_func_test_3() {
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_model = true;
    smt::context ctx(m, params);

    arith_util m_util_a(m);
    seq_util m_util_s(m);

    smt::theory_str2 str2_class(m, ctx.get_fparams());
    smt::int_expr_solver m_int_solver(m, ctx.get_fparams());


    expr_ref int_formula(m.mk_true(), m);
    expr_ref L_pre_len(smt::theory_str2::mk_int_var("L_pre_len", ctx, m, m_util_a, m_util_s), m);
    int_formula = m.mk_and(int_formula, m_util_a.mk_eq(L_pre_len, m_util_a.mk_int(1)));
    expr_ref R_pre_len(smt::theory_str2::mk_int_var("R_pre_len", ctx, m, m_util_a, m_util_s), m);
    int_formula = m.mk_and(int_formula, m_util_a.mk_eq(R_pre_len, m_util_a.mk_int(0)));


    str2_class.str_str_symbol_match_to_expr_ref(int_formula, L_pre_len, R_pre_len, "abc", "abcde", ctx, m);

    int_formula = m.mk_not(int_formula);

    bool result = m_int_solver.check_sat(int_formula) == lbool::l_true;
    ENSURE(result);
}


static void str_str_symbol_match_to_expr_ref_func_test_4() {
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_model = true;
    smt::context ctx(m, params);

    arith_util m_util_a(m);
    seq_util m_util_s(m);

    smt::theory_str2 str2_class(m, ctx.get_fparams());
    smt::int_expr_solver m_int_solver(m, ctx.get_fparams());


    expr_ref int_formula(m.mk_true(), m);
    expr_ref L_pre_len(smt::theory_str2::mk_int_var("L_pre_len", ctx, m, m_util_a, m_util_s), m);
    int_formula = m.mk_and(int_formula, m_util_a.mk_eq(L_pre_len, m_util_a.mk_int(6)));
    expr_ref R_pre_len(smt::theory_str2::mk_int_var("R_pre_len", ctx, m, m_util_a, m_util_s), m);
    int_formula = m.mk_and(int_formula, m_util_a.mk_eq(R_pre_len, m_util_a.mk_int(0)));

    std::string s = "";
    std::string t = "";
    for (unsigned i = 0; i < 10; i++)
    {
        s.append("abcd");
        t.append("cdab");
    }


    str2_class.str_str_symbol_match_to_expr_ref(int_formula, L_pre_len, R_pre_len, s, t, ctx, m);



    bool result = m_int_solver.check_sat(int_formula) == lbool::l_true;
    ENSURE(result);
}

static void str_var_symbol_match_to_expr_ref_func_test_1()
{
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_model = true;
    smt::context ctx(m, params);

    arith_util m_util_a(m);
    seq_util m_util_s(m);

    smt::theory_str2 str2_class(m, ctx.get_fparams());
    smt::int_expr_solver m_int_solver(m, ctx.get_fparams());


    expr_ref int_formula(m.mk_true(), m);
    expr_ref L_pre_len(m_util_a.mk_int(0), m);
    expr_ref R_pre_len(m_util_a.mk_int(0), m);


    std::string L_str = "abcd";
    std::string R_var = "x";
    unsigned loop_size = 4;
    unsigned num_loop = 2;

    str2_class.str_var_symbol_match_to_expr_ref(int_formula, L_pre_len, R_pre_len, L_str, R_var, loop_size, num_loop, ctx, m);


    expr_ref x_0_1(smt::theory_str2::mk_int_var("x_0_1", ctx, m, m_util_a, m_util_s), m);
    int_formula = m.mk_and(int_formula, m_util_a.mk_gt(x_0_1, m_util_a.mk_int(0)));
    expr_ref x_loop_0(smt::theory_str2::mk_int_var("x_loop_0", ctx, m, m_util_a, m_util_s), m);
    int_formula = m.mk_and(int_formula, m_util_a.mk_gt(x_loop_0, m_util_a.mk_int(0)));


    bool result = m_int_solver.check_sat(int_formula) == lbool::l_true;
    ENSURE(result);
}


static void str_var_symbol_match_to_expr_ref_func_test_2()
{
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_model = true;
    smt::context ctx(m, params);

    arith_util m_util_a(m);
    seq_util m_util_s(m);

    smt::theory_str2 str2_class(m, ctx.get_fparams());
    smt::int_expr_solver m_int_solver(m, ctx.get_fparams());

    expr_ref int_formula(m.mk_true(), m);
    expr_ref L_pre_len(m_util_a.mk_int(0), m);
    expr_ref R_pre_len(m_util_a.mk_int(0), m);

    std::string L_str = "";
    for (unsigned i = 0; i < 10; i++)
    {
        L_str.append("abc");
    }
    std::string R_var = "x";
    unsigned loop_size = 5;
    unsigned num_loop = 2;

    str2_class.str_var_symbol_match_to_expr_ref(int_formula, L_pre_len, R_pre_len, L_str, R_var, loop_size, num_loop, ctx, m);

    expr_ref x_0_0(smt::theory_str2::mk_int_var("x_0_0", ctx, m, m_util_a, m_util_s), m);
    int_formula = m.mk_and(int_formula, m_util_a.mk_gt(x_0_0, m_util_a.mk_int(0)));
    expr_ref x_0_1(smt::theory_str2::mk_int_var("x_0_1", ctx, m, m_util_a, m_util_s), m);
    int_formula = m.mk_and(int_formula, m_util_a.mk_gt(x_0_1, m_util_a.mk_int(0)));
    expr_ref x_0_2(smt::theory_str2::mk_int_var("x_0_2", ctx, m, m_util_a, m_util_s), m);
    int_formula = m.mk_and(int_formula, m_util_a.mk_gt(x_0_2, m_util_a.mk_int(0)));
    expr_ref x_0_3(smt::theory_str2::mk_int_var("x_0_3", ctx, m, m_util_a, m_util_s), m);
    int_formula = m.mk_and(int_formula, m_util_a.mk_gt(x_0_3, m_util_a.mk_int(0)));
    expr_ref x_loop_0(smt::theory_str2::mk_int_var("x_loop_0", ctx, m, m_util_a, m_util_s), m);
    int_formula = m.mk_and(int_formula, m_util_a.mk_gt(x_loop_0, m_util_a.mk_int(0)));


    bool result = m_int_solver.check_sat(int_formula) == lbool::l_true;
    ENSURE(result);
}



static void str_var_symbol_match_to_expr_ref_func_test_3()
{
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_model = true;
    smt::context ctx(m, params);

    arith_util m_util_a(m);
    seq_util m_util_s(m);

    smt::theory_str2 str2_class(m, ctx.get_fparams());
    smt::int_expr_solver m_int_solver(m, ctx.get_fparams());


    expr_ref int_formula(m.mk_true(), m);
    expr_ref L_pre_len(m_util_a.mk_int(0), m);
    expr_ref R_pre_len(m_util_a.mk_int(0), m);

    std::string L_str = "";
    for (unsigned i = 0; i < 10; i++)
    {
        L_str.append("abc");
    }
    std::string R_var = "x";
    unsigned loop_size = 5;
    unsigned num_loop = 2;

    str2_class.str_var_symbol_match_to_expr_ref(int_formula, L_pre_len, R_pre_len, L_str, R_var, loop_size, num_loop, ctx, m);

    expr_ref x_0_0(smt::theory_str2::mk_int_var("x_0_0", ctx, m, m_util_a, m_util_s), m);
    int_formula = m.mk_and(int_formula, m_util_a.mk_gt(x_0_0, m_util_a.mk_int(0)));
    expr_ref x_0_1(smt::theory_str2::mk_int_var("x_0_1", ctx, m, m_util_a, m_util_s), m);
    int_formula = m.mk_and(int_formula, m_util_a.mk_gt(x_0_1, m_util_a.mk_int(0)));
    expr_ref x_0_2(smt::theory_str2::mk_int_var("x_0_2", ctx, m, m_util_a, m_util_s), m);
    int_formula = m.mk_and(int_formula, m_util_a.mk_gt(x_0_2, m_util_a.mk_int(0)));
    expr_ref x_0_3(smt::theory_str2::mk_int_var("x_0_3", ctx, m, m_util_a, m_util_s), m);
    int_formula = m.mk_and(int_formula, m_util_a.mk_gt(x_0_3, m_util_a.mk_int(0)));
    expr_ref x_loop_0(smt::theory_str2::mk_int_var("x_loop_0", ctx, m, m_util_a, m_util_s), m);
    int_formula = m.mk_and(int_formula, m_util_a.mk_gt(x_loop_0, m_util_a.mk_int(1)));

    int_formula = m.mk_not(int_formula);

    bool result = m_int_solver.check_sat(int_formula) == lbool::l_true;
    ENSURE(result);
}



static void str_var_symbol_match_to_expr_ref_func_test_4()
{
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_model = true;
    smt::context ctx(m, params);

    arith_util m_util_a(m);
    seq_util m_util_s(m);

    smt::theory_str2 str2_class(m, ctx.get_fparams());
    smt::int_expr_solver m_int_solver(m, ctx.get_fparams());


    expr_ref int_formula(m.mk_true(), m);
    expr_ref L_pre_len(m_util_a.mk_int(0), m);
    expr_ref R_pre_len(m_util_a.mk_int(0), m);

    std::string L_str = "";
    for (unsigned i = 0; i < 10; i++)
    {
        L_str.append("abc");
    }
    std::string R_var = "x";
    unsigned loop_size = 5;
    unsigned num_loop = 5;

    str2_class.str_var_symbol_match_to_expr_ref(int_formula, L_pre_len, R_pre_len, L_str, R_var, loop_size, num_loop, ctx, m);


    bool result = m_int_solver.check_sat(int_formula) == lbool::l_true;
    ENSURE(result);
}


static void var_str_symbol_match_to_expr_ref_func_test_1() {
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_model = true;
    smt::context ctx(m, params);

    arith_util m_util_a(m);
    seq_util m_util_s(m);

    smt::theory_str2 str2_class(m, ctx.get_fparams());
    smt::int_expr_solver m_int_solver(m, ctx.get_fparams());


    expr_ref int_formula(m.mk_true(), m);
    expr_ref L_pre_len(m_util_a.mk_int(0), m);
    expr_ref R_pre_len(m_util_a.mk_int(0), m);

    
    std::string L_var = "x";
    std::string R_str = "abcd";
    unsigned loop_size = 4;
    unsigned num_loop = 2;

    str2_class.var_str_symbol_match_to_expr_ref(int_formula, L_pre_len, R_pre_len, L_var, R_str, loop_size, num_loop, ctx, m);


    expr_ref x_0_1(smt::theory_str2::mk_int_var("x_0_1", ctx, m, m_util_a, m_util_s), m);
    int_formula = m.mk_and(int_formula, m_util_a.mk_gt(x_0_1, m_util_a.mk_int(0)));
    expr_ref x_loop_0(smt::theory_str2::mk_int_var("x_loop_0", ctx, m, m_util_a, m_util_s), m);
    int_formula = m.mk_and(int_formula, m_util_a.mk_gt(x_loop_0, m_util_a.mk_int(0)));


    bool result = m_int_solver.check_sat(int_formula) == lbool::l_true;
    ENSURE(result);
}


static void var_str_symbol_match_to_expr_ref_func_test_2() {
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_model = true;
    smt::context ctx(m, params);

    arith_util m_util_a(m);
    seq_util m_util_s(m);

    smt::theory_str2 str2_class(m, ctx.get_fparams());
    smt::int_expr_solver m_int_solver(m, ctx.get_fparams());


    expr_ref int_formula(m.mk_true(), m);
    expr_ref L_pre_len(m_util_a.mk_int(2), m);
    expr_ref R_pre_len(m_util_a.mk_int(0), m);


    std::string L_var = "x";
    std::string R_str = "abcd";
    unsigned loop_size = 4;
    unsigned num_loop = 2;

    str2_class.var_str_symbol_match_to_expr_ref(int_formula, L_pre_len, R_pre_len, L_var, R_str, loop_size, num_loop, ctx, m);

    expr_ref x_0_0(smt::theory_str2::mk_int_var("x_0_0", ctx, m, m_util_a, m_util_s), m);
    int_formula = m.mk_and(int_formula, m_util_a.mk_eq(x_0_0, m_util_a.mk_int(13)));
    expr_ref x_0_1(smt::theory_str2::mk_int_var("x_0_1", ctx, m, m_util_a, m_util_s), m);
    int_formula = m.mk_and(int_formula, m_util_a.mk_gt(x_0_1, m_util_a.mk_int(0)));
    expr_ref x_0_2(smt::theory_str2::mk_int_var("x_0_2", ctx, m, m_util_a, m_util_s), m);
    int_formula = m.mk_and(int_formula, m_util_a.mk_gt(x_0_2, m_util_a.mk_int(0)));
    expr_ref x_0_3(smt::theory_str2::mk_int_var("x_0_3", ctx, m, m_util_a, m_util_s), m);
    int_formula = m.mk_and(int_formula, m_util_a.mk_gt(x_0_3, m_util_a.mk_int(0)));
    expr_ref x_loop_0(smt::theory_str2::mk_int_var("x_loop_0", ctx, m, m_util_a, m_util_s), m);
    int_formula = m.mk_and(int_formula, m_util_a.mk_eq(x_loop_0, m_util_a.mk_int(1)));
    
    int_formula = m.mk_not(int_formula);

    bool result = m_int_solver.check_sat(int_formula) == lbool::l_true;
    ENSURE(result);
}


static void var_str_symbol_match_to_expr_ref_func_test_3() {
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_model = true;
    smt::context ctx(m, params);

    arith_util m_util_a(m);
    seq_util m_util_s(m);

    smt::theory_str2 str2_class(m, ctx.get_fparams());
    smt::int_expr_solver m_int_solver(m, ctx.get_fparams());


    expr_ref int_formula(m.mk_true(), m);
    expr_ref L_pre_len(m_util_a.mk_int(0), m);
    expr_ref R_pre_len(m_util_a.mk_int(0), m);


    std::string L_var = "x";
    std::string R_str = "abc";
    unsigned loop_size = 5;
    unsigned num_loop = 2;

    str2_class.var_str_symbol_match_to_expr_ref(int_formula, L_pre_len, R_pre_len, L_var, R_str, loop_size, num_loop, ctx, m);



    expr_ref x_0_2(smt::theory_str2::mk_int_var("x_0_2", ctx, m, m_util_a, m_util_s), m);
    int_formula = m.mk_and(int_formula, m_util_a.mk_gt(x_0_2, m_util_a.mk_int(0)));
    expr_ref x_0_3(smt::theory_str2::mk_int_var("x_0_3", ctx, m, m_util_a, m_util_s), m);
    int_formula = m.mk_and(int_formula, m_util_a.mk_eq(x_0_3, m_util_a.mk_int(0)));
    expr_ref x_loop_0_len(smt::theory_str2::mk_int_var("x_loop_0_len", ctx, m, m_util_a, m_util_s), m);
    int_formula = m.mk_and(int_formula, m_util_a.mk_eq(x_loop_0_len, m_util_a.mk_int(3)));
    expr_ref x_loop_0(smt::theory_str2::mk_int_var("x_loop_0", ctx, m, m_util_a, m_util_s), m);
    int_formula = m.mk_and(int_formula, m_util_a.mk_eq(x_loop_0, m_util_a.mk_int(1)));


    bool result = m_int_solver.check_sat(int_formula) == lbool::l_true;
    ENSURE(result);
}



static void var_str_symbol_match_to_expr_ref_func_test_4() {
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_model = true;
    smt::context ctx(m, params);

    arith_util m_util_a(m);
    seq_util m_util_s(m);

    smt::theory_str2 str2_class(m, ctx.get_fparams());
    smt::int_expr_solver m_int_solver(m, ctx.get_fparams());


    expr_ref int_formula(m.mk_true(), m);
    expr_ref L_pre_len(m_util_a.mk_int(0), m);
    expr_ref R_pre_len(m_util_a.mk_int(0), m);


    std::string L_var = "x";
    std::string R_str = "abc";
    unsigned loop_size = 5;
    unsigned num_loop = 2;

    str2_class.var_str_symbol_match_to_expr_ref(int_formula, L_pre_len, R_pre_len, L_var, R_str, loop_size, num_loop, ctx, m);



    expr_ref x_0_2(smt::theory_str2::mk_int_var("x_0_2", ctx, m, m_util_a, m_util_s), m);
    int_formula = m.mk_and(int_formula, m_util_a.mk_gt(x_0_2, m_util_a.mk_int(0)));
    expr_ref x_0_3(smt::theory_str2::mk_int_var("x_0_3", ctx, m, m_util_a, m_util_s), m);
    int_formula = m.mk_and(int_formula, m_util_a.mk_eq(x_0_3, m_util_a.mk_int(0)));
    expr_ref x_loop_0_len(smt::theory_str2::mk_int_var("x_loop_0_len", ctx, m, m_util_a, m_util_s), m);
    int_formula = m.mk_and(int_formula, m_util_a.mk_eq(x_loop_0_len, m_util_a.mk_int(5)));
    expr_ref x_loop_0(smt::theory_str2::mk_int_var("x_loop_0", ctx, m, m_util_a, m_util_s), m);
    int_formula = m.mk_and(int_formula, m_util_a.mk_eq(x_loop_0, m_util_a.mk_int(1)));

    int_formula = m.mk_not(int_formula);

    bool result = m_int_solver.check_sat(int_formula) == lbool::l_true;
    ENSURE(result);
}


static void var_str_symbol_match_to_expr_ref_func_test_5() {
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_model = true;
    smt::context ctx(m, params);

    arith_util m_util_a(m);
    seq_util m_util_s(m);

    smt::theory_str2 str2_class(m, ctx.get_fparams());
    smt::int_expr_solver m_int_solver(m, ctx.get_fparams());


    expr_ref int_formula(m.mk_true(), m);
    expr_ref L_pre_len(m_util_a.mk_int(0), m);
    expr_ref R_pre_len(m_util_a.mk_int(0), m);


    std::string L_var = "x";
    std::string R_str = "abcdabcd";
    unsigned loop_size = 5;
    unsigned num_loop = 2;

    str2_class.var_str_symbol_match_to_expr_ref(int_formula, L_pre_len, R_pre_len, L_var, R_str, loop_size, num_loop, ctx, m);




    expr_ref x_loop_0_len(smt::theory_str2::mk_int_var("x_loop_0_len", ctx, m, m_util_a, m_util_s), m);
    int_formula = m.mk_and(int_formula, m_util_a.mk_eq(x_loop_0_len, m_util_a.mk_int(4)));
    expr_ref x_loop_0(smt::theory_str2::mk_int_var("x_loop_0", ctx, m, m_util_a, m_util_s), m);
    int_formula = m.mk_and(int_formula, m_util_a.mk_eq(x_loop_0, m_util_a.mk_int(2)));


    bool result = m_int_solver.check_sat(int_formula) == lbool::l_true;
    ENSURE(result);
}



static void var_str_symbol_match_to_expr_ref_func_test_6() {
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_model = true;
    smt::context ctx(m, params);

    arith_util m_util_a(m);
    seq_util m_util_s(m);

    smt::theory_str2 str2_class(m, ctx.get_fparams());
    smt::int_expr_solver m_int_solver(m, ctx.get_fparams());


    expr_ref int_formula(m.mk_true(), m);
    expr_ref L_pre_len(m_util_a.mk_int(0), m);
    expr_ref R_pre_len(m_util_a.mk_int(0), m);


    std::string L_var = "x";
    std::string R_str = "abc";
    unsigned loop_size = 1;
    unsigned num_loop = 2;

    str2_class.var_str_symbol_match_to_expr_ref(int_formula, L_pre_len, R_pre_len, L_var, R_str, loop_size, num_loop, ctx, m);


    expr_ref x_loop_0_len(smt::theory_str2::mk_int_var("x_loop_0_len", ctx, m, m_util_a, m_util_s), m);
    int_formula = m.mk_and(int_formula, m_util_a.mk_gt(x_loop_0_len, m_util_a.mk_int(1)));
    int_formula = m.mk_not(int_formula);


    bool result = m_int_solver.check_sat(int_formula) == lbool::l_true;
    ENSURE(result);
}


static void var_var_symbol_match_to_expr_ref_func_test1() {
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_model = true;
    smt::context ctx(m, params);

    arith_util m_util_a(m);
    seq_util m_util_s(m);

    smt::theory_str2 str2_class(m, ctx.get_fparams());
    smt::int_expr_solver m_int_solver(m, ctx.get_fparams());


    expr_ref int_formula(m.mk_true(), m);
    expr_ref L_pre_len(m_util_a.mk_int(0), m);
    expr_ref R_pre_len(m_util_a.mk_int(1), m);
    expr_ref R_str_pre_len(m_util_a.mk_int(0), m);



    std::string L_var = "x";
    std::string R_var = "y";
    std::string R_str = "ab";
    unsigned loop_size = 2;
    unsigned num_loop = 1;

    str2_class.var_var_symbol_match_to_expr_ref(int_formula, L_pre_len, R_pre_len, L_var, R_var, loop_size, num_loop, ctx, m);
    str2_class.var_str_symbol_match_to_expr_ref(int_formula, L_pre_len, R_str_pre_len, L_var, R_str, loop_size, num_loop, ctx, m);


    expr_ref x_loop_0(smt::theory_str2::mk_int_var("x_loop_0", ctx, m, m_util_a, m_util_s), m);
    int_formula = m.mk_and(int_formula, m_util_a.mk_eq(x_loop_0, m_util_a.mk_int(1)));
    expr_ref x_loop_0_len(smt::theory_str2::mk_int_var("x_loop_0_len", ctx, m, m_util_a, m_util_s), m);
    int_formula = m.mk_and(int_formula, m_util_a.mk_eq(x_loop_0_len, m_util_a.mk_int(2)));
    expr_ref y_loop_0(smt::theory_str2::mk_int_var("y_loop_0", ctx, m, m_util_a, m_util_s), m);
    int_formula = m.mk_and(int_formula, m_util_a.mk_eq(y_loop_0, m_util_a.mk_int(1)));
    expr_ref y_loop_0_len(smt::theory_str2::mk_int_var("y_loop_0_len", ctx, m, m_util_a, m_util_s), m);
    int_formula = m.mk_and(int_formula, m_util_a.mk_eq(y_loop_0_len, m_util_a.mk_int(2)));

    bool result = m_int_solver.check_sat(int_formula) == lbool::l_true;
    ENSURE(result);
}





static void var_var_symbol_match_to_expr_ref_func_test2() {
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_model = true;
    smt::context ctx(m, params);

    arith_util m_util_a(m);
    seq_util m_util_s(m);

    smt::theory_str2 str2_class(m, ctx.get_fparams());
    smt::int_expr_solver m_int_solver(m, ctx.get_fparams());


    expr_ref int_formula(m.mk_true(), m);
    expr_ref L_pre_len(m_util_a.mk_int(0), m);
    expr_ref R_pre_len(m_util_a.mk_int(0), m);


    std::string L_var = "x";
    std::string R_var = "y";
    std::string R_str = "ab";
    std::string L_str = "ac";
    unsigned loop_size = 2;
    unsigned num_loop = 1;

    str2_class.var_var_symbol_match_to_expr_ref(int_formula, L_pre_len, R_pre_len, L_var, R_var, loop_size, num_loop, ctx, m);
    str2_class.str_var_symbol_match_to_expr_ref(int_formula, L_pre_len, R_pre_len, L_str, R_var, loop_size, num_loop, ctx, m);
    str2_class.var_str_symbol_match_to_expr_ref(int_formula, L_pre_len, R_pre_len, L_var, R_str, loop_size, num_loop, ctx, m);


    expr_ref x_loop_0(smt::theory_str2::mk_int_var("x_loop_0", ctx, m, m_util_a, m_util_s), m);
    int_formula = m.mk_and(int_formula, m_util_a.mk_eq(x_loop_0, m_util_a.mk_int(1)));
    expr_ref x_loop_0_len(smt::theory_str2::mk_int_var("x_loop_0_len", ctx, m, m_util_a, m_util_s), m);
    int_formula = m.mk_and(int_formula, m_util_a.mk_eq(x_loop_0_len, m_util_a.mk_int(2)));
    expr_ref y_loop_0(smt::theory_str2::mk_int_var("y_loop_0", ctx, m, m_util_a, m_util_s), m);
    int_formula = m.mk_and(int_formula, m_util_a.mk_eq(y_loop_0, m_util_a.mk_int(1)));
    expr_ref y_loop_0_len(smt::theory_str2::mk_int_var("y_loop_0_len", ctx, m, m_util_a, m_util_s), m);
    int_formula = m.mk_and(int_formula, m_util_a.mk_eq(y_loop_0_len, m_util_a.mk_int(2)));
    int_formula = m.mk_not(int_formula);


    bool result = m_int_solver.check_sat(int_formula) == lbool::l_true;
    ENSURE(result);
}




static void var_var_symbol_match_to_expr_ref_func_test3() {
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_model = true;
    smt::context ctx(m, params);

    arith_util m_util_a(m);
    seq_util m_util_s(m);

    smt::theory_str2 str2_class(m, ctx.get_fparams());
    smt::int_expr_solver m_int_solver(m, ctx.get_fparams());


    expr_ref int_formula(m.mk_true(), m);
    expr_ref L_pre_len(m_util_a.mk_int(0), m);
    expr_ref R_pre_len(m_util_a.mk_int(0), m);


    std::string L_var = "x";
    std::string R_var = "y";
    std::string R_str = "";
    for (int i = 0; i < 5; i++)
    {
        R_str.append("ab");
    }
    unsigned loop_size = 3;
    unsigned num_loop = 2;

    str2_class.var_var_symbol_match_to_expr_ref(int_formula, L_pre_len, R_pre_len, L_var, R_var, loop_size, num_loop, ctx, m);
    str2_class.var_str_symbol_match_to_expr_ref(int_formula, L_pre_len, R_pre_len, L_var, R_str, loop_size, num_loop, ctx, m);


    expr_ref x_loop_0(smt::theory_str2::mk_int_var("x_loop_0", ctx, m, m_util_a, m_util_s), m);
    int_formula = m.mk_and(int_formula, m_util_a.mk_ge(x_loop_0, m_util_a.mk_int(1)));
    expr_ref x_loop_0_len(smt::theory_str2::mk_int_var("x_loop_0_len", ctx, m, m_util_a, m_util_s), m);
    int_formula = m.mk_and(int_formula, m_util_a.mk_eq(x_loop_0_len, m_util_a.mk_int(2)));

    bool result = m_int_solver.check_sat(int_formula) == lbool::l_true;
    ENSURE(result);
}


static void len_update_func_test1() {
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_model = true;
    smt::context ctx(m, params);
    arith_util m_util_a(m);
    seq_util m_util_s(m);
    smt::theory_str2 str2_class(m, ctx.get_fparams());
    smt::int_expr_solver m_int_solver(m, ctx.get_fparams());


    expr_ref int_formula(m.mk_true(), m);
    unsigned loop_size = 3;
    unsigned num_loop = 2;
    std::list<std::pair<char, std::string>>  word_term_1;
    expr_ref word_term_1_pre_len(m_util_a.mk_int(0), m);
    std::list<std::pair<char, std::string>>  word_term_2;
    expr_ref word_term_2_pre_len(m_util_a.mk_int(0), m);
    std::list<std::pair<char, std::string>>  word_term_3;
    expr_ref word_term_3_pre_len(m_util_a.mk_int(0), m);
    for (int i = 0; i < 5; i++)
        word_term_1.push_back(std::make_pair('S', "ab"));
    word_term_2.push_back(std::make_pair('V', "x"));
    word_term_2.push_back(std::make_pair('V', "y"));
    word_term_3.push_back(std::make_pair('E', "ab"));

    for (std::list<std::pair<char, std::string>>::iterator it = word_term_1.begin(); it != word_term_1.end(); ++it)
    {
        str2_class.len_update(word_term_1_pre_len, (*it).first, (*it).second, num_loop, ctx, m);
    }
    for (std::list<std::pair<char, std::string>>::iterator it = word_term_2.begin(); it != word_term_2.end(); ++it)
    {
        str2_class.len_update(word_term_2_pre_len, (*it).first, (*it).second, num_loop, ctx, m);
    }
    for (std::list<std::pair<char, std::string>>::iterator it = word_term_3.begin(); it != word_term_3.end(); ++it)
    {
        str2_class.len_update(word_term_3_pre_len, (*it).first, (*it).second, num_loop, ctx, m);
    }

    int_formula = m.mk_and(int_formula, m_util_a.mk_eq(word_term_1_pre_len, m_util_a.mk_int(10)));
    int_formula = m.mk_and(int_formula, m_util_a.mk_eq(word_term_3_pre_len, m_util_a.mk_int(0)));



    expr_ref x_loop_0(smt::theory_str2::mk_int_var("x_loop_" + std::to_string(0), ctx, m, m_util_a, m_util_s), m);
    expr_ref x_loop_0_len(smt::theory_str2::mk_int_var("x_loop_" + std::to_string(0) + "_len", ctx, m, m_util_a, m_util_s), m);
    expr_ref x_loop_1(smt::theory_str2::mk_int_var("x_loop_" + std::to_string(1), ctx, m, m_util_a, m_util_s), m);
    expr_ref x_loop_1_len(smt::theory_str2::mk_int_var("x_loop_" + std::to_string(1) + "_len", ctx, m, m_util_a, m_util_s), m);
    expr_ref y_loop_0(smt::theory_str2::mk_int_var("y_loop_" + std::to_string(0), ctx, m, m_util_a, m_util_s), m);
    expr_ref y_loop_0_len(smt::theory_str2::mk_int_var("y_loop_" + std::to_string(0) + "_len", ctx, m, m_util_a, m_util_s), m);
    expr_ref y_loop_1(smt::theory_str2::mk_int_var("y_loop_" + std::to_string(1), ctx, m, m_util_a, m_util_s), m);
    expr_ref y_loop_1_len(smt::theory_str2::mk_int_var("y_loop_" + std::to_string(1) + "_len", ctx, m, m_util_a, m_util_s), m);
    expr_ref word_term_2_total_len(m_util_a.mk_mul(x_loop_0, x_loop_0_len), m);
    word_term_2_total_len = m_util_a.mk_add(word_term_2_total_len, m_util_a.mk_mul(x_loop_1, x_loop_1_len));
    word_term_2_total_len = m_util_a.mk_add(word_term_2_total_len, m_util_a.mk_mul(y_loop_0, y_loop_0_len));
    word_term_2_total_len = m_util_a.mk_add(word_term_2_total_len, m_util_a.mk_mul(y_loop_1, y_loop_1_len));
    word_term_2_total_len = m_util_a.mk_add(word_term_2_total_len, m_util_a.mk_int(1));
    int_formula = m.mk_and(int_formula, m.mk_not(m_util_a.mk_eq(word_term_2_pre_len, word_term_2_total_len)));


    bool result = m_int_solver.check_sat(int_formula) == lbool::l_true;
    ENSURE(result);
}


static void eq_word_term_lists_to_expr_ref_func_test1() {
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_model = true;
    smt::context ctx(m, params);
    arith_util m_util_a(m);
    seq_util m_util_s(m);
    smt::theory_str2 str2_class(m, ctx.get_fparams());
    smt::int_expr_solver m_int_solver(m, ctx.get_fparams());

    unsigned loop_size = 3;
    unsigned num_loop = 2;

    std::list<std::pair<char, std::string>> L_word_term_list, R_word_term_list;


    L_word_term_list.push_back(std::make_pair('S', "ab"));
    R_word_term_list.push_back(std::make_pair('S', "ab"));
    
    expr_ref int_formula = str2_class.eq_word_term_lists_to_expr_ref(ctx, m, L_word_term_list, R_word_term_list, loop_size, num_loop);
    L_word_term_list.pop_front();
    R_word_term_list.pop_front();


    L_word_term_list.push_back(std::make_pair('S', "ab"));
    L_word_term_list.push_back(std::make_pair('S', "ab"));
    R_word_term_list.push_back(std::make_pair('S', "ab"));
    int_formula = m.mk_and(int_formula, m.mk_not(str2_class.eq_word_term_lists_to_expr_ref(ctx, m, L_word_term_list, R_word_term_list, loop_size, num_loop)));
    L_word_term_list.pop_front();
    L_word_term_list.pop_front();
    R_word_term_list.pop_front();


    L_word_term_list.push_back(std::make_pair('S', "ac"));
    R_word_term_list.push_back(std::make_pair('S', "ab"));
    int_formula = m.mk_and(int_formula, m.mk_not(str2_class.eq_word_term_lists_to_expr_ref(ctx, m, L_word_term_list, R_word_term_list, loop_size, num_loop)));
    L_word_term_list.pop_front();
    R_word_term_list.pop_front();


    bool result = m_int_solver.check_sat(int_formula) == lbool::l_true;
    ENSURE(result);
}



static void eq_word_term_lists_to_expr_ref_func_test2() {
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_model = true;
    smt::context ctx(m, params);
    arith_util m_util_a(m);
    seq_util m_util_s(m);
    smt::theory_str2 str2_class(m, ctx.get_fparams());
    smt::int_expr_solver m_int_solver(m, ctx.get_fparams());

    unsigned loop_size = 3;
    unsigned num_loop = 2;

    std::list<std::pair<char, std::string>> L_word_term_list, R_word_term_list;


    L_word_term_list.push_back(std::make_pair('V', "x"));
    R_word_term_list.push_back(std::make_pair('V', "y"));

    expr_ref int_formula = str2_class.eq_word_term_lists_to_expr_ref(ctx, m, L_word_term_list, R_word_term_list, loop_size, num_loop);
    L_word_term_list.pop_front();
    R_word_term_list.pop_front();


    L_word_term_list.push_back(std::make_pair('V', "z"));
    R_word_term_list.push_back(std::make_pair('S', "ab"));
    int_formula = m.mk_and(int_formula, str2_class.eq_word_term_lists_to_expr_ref(ctx, m, L_word_term_list, R_word_term_list, loop_size, num_loop));
    L_word_term_list.pop_front();
    R_word_term_list.pop_front();


    bool result = m_int_solver.check_sat(int_formula) == lbool::l_true;
    ENSURE(result);
}


static void eq_word_term_lists_to_expr_ref_func_test3() {
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_model = true;
    smt::context ctx(m, params);
    arith_util m_util_a(m);
    seq_util m_util_s(m);
    smt::theory_str2 str2_class(m, ctx.get_fparams());
    smt::int_expr_solver m_int_solver(m, ctx.get_fparams());

    unsigned loop_size = 3;
    unsigned num_loop = 2;

    std::list<std::pair<char, std::string>> L_word_term_list, R_word_term_list;
    std::list<std::pair<char, std::string>> L_word_term_list_2, R_word_term_list_2;

    L_word_term_list.push_back(std::make_pair('S', "ab"));
    L_word_term_list.push_back(std::make_pair('V', "x"));
    L_word_term_list.push_back(std::make_pair('S', "de"));
    R_word_term_list.push_back(std::make_pair('S', "abcde"));

    expr_ref int_formula = str2_class.eq_word_term_lists_to_expr_ref(ctx, m, L_word_term_list, R_word_term_list, loop_size, num_loop);
    L_word_term_list.pop_front();
    L_word_term_list.pop_front();
    L_word_term_list.pop_front();
    R_word_term_list.pop_front();



    // part 2
    L_word_term_list.push_back(std::make_pair('S', "ab"));
    L_word_term_list.push_back(std::make_pair('V', "z"));
    L_word_term_list.push_back(std::make_pair('S', "de"));
    R_word_term_list.push_back(std::make_pair('S', "abcde"));
    expr_ref temp_formula = str2_class.eq_word_term_lists_to_expr_ref(ctx, m, L_word_term_list, R_word_term_list, loop_size, num_loop);
    L_word_term_list_2.push_back(std::make_pair('V', "z"));
    R_word_term_list_2.push_back(std::make_pair('V', "z"));
    R_word_term_list_2.push_back(std::make_pair('V', "z"));
    temp_formula = m.mk_and(temp_formula, str2_class.eq_word_term_lists_to_expr_ref(ctx, m, L_word_term_list_2, R_word_term_list_2, loop_size, num_loop));

    int_formula = m.mk_and(int_formula, m.mk_not(temp_formula));

    bool result = m_int_solver.check_sat(int_formula) == lbool::l_true;
    ENSURE(result);
}


static void str_str_symbol_not_match_to_expr_ref_func_test() {
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_model = true;
    smt::context ctx(m, params);

    arith_util m_util_a(m);
    seq_util m_util_s(m);

    smt::theory_str2 str2_class(m, ctx.get_fparams());
    smt::int_expr_solver m_int_solver(m, ctx.get_fparams());


    expr_ref int_formula(m.mk_false(), m);
    expr_ref L_pre_len(m_util_a.mk_int(0), m);
    expr_ref R_pre_len(m_util_a.mk_int(0), m);

    std::string s = "abcd";
    std::string t = "abdd";

    str2_class.str_str_symbol_not_match_to_expr_ref(int_formula, L_pre_len, R_pre_len, s, t, ctx, m);


    bool result = m_int_solver.check_sat(int_formula) == lbool::l_true;
    ENSURE(result);


    //part 2

    int_formula = m.mk_false();

    s = "abc";
    t = "abc";

    str2_class.str_str_symbol_not_match_to_expr_ref(int_formula, L_pre_len, R_pre_len, s, t, ctx, m);


    result = m_int_solver.check_sat(m.mk_not(int_formula)) == lbool::l_true;
    ENSURE(result);
}



static void str_var_symbol_not_match_to_expr_ref_func_test_1()
{
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_model = true;
    smt::context ctx(m, params);

    arith_util m_util_a(m);
    seq_util m_util_s(m);

    smt::theory_str2 str2_class(m, ctx.get_fparams());
    smt::int_expr_solver m_int_solver(m, ctx.get_fparams());


    expr_ref int_formula_pos_cond(m.mk_false(), m);
    expr_ref int_formula_len_cond(m.mk_true(), m);
    expr_ref L_pre_len(m_util_a.mk_int(0), m);
    expr_ref R_pre_len(m_util_a.mk_int(0), m);


    std::string L_str = "abcd";
    std::string R_var = "x";
    unsigned loop_size = 4;
    unsigned num_loop = 1;

    str2_class.str_var_symbol_not_match_to_expr_ref(int_formula_pos_cond, int_formula_len_cond, L_pre_len, R_pre_len, L_str, R_var, loop_size, num_loop, ctx, m);



    expr_ref x_loop_0(smt::theory_str2::mk_int_var("x_loop_0", ctx, m, m_util_a, m_util_s), m);
    int_formula_len_cond = m.mk_and(int_formula_len_cond, m_util_a.mk_gt(x_loop_0, m_util_a.mk_int(0)));
    expr_ref x_loop_0_len(smt::theory_str2::mk_int_var("x_loop_0_len", ctx, m, m_util_a, m_util_s), m);
    int_formula_len_cond = m.mk_and(int_formula_len_cond, m_util_a.mk_gt(x_loop_0_len, m_util_a.mk_int(0)));


    bool result = m_int_solver.check_sat(m.mk_and(int_formula_len_cond,int_formula_pos_cond)) == lbool::l_true;
    ENSURE(result);



    // part 2
    expr_ref int_formula(m.mk_true(), m);
    int_formula_pos_cond = m.mk_false();
    int_formula_len_cond = m.mk_true();

    L_str = "abc";
    R_var = "x";
    std::string L_str_2 = "agc";

    str2_class.str_var_symbol_match_to_expr_ref(int_formula, L_pre_len, R_pre_len, L_str_2, R_var, loop_size, num_loop, ctx, m);
    str2_class.str_var_symbol_not_match_to_expr_ref(int_formula_pos_cond, int_formula_len_cond, L_pre_len, R_pre_len, L_str, R_var, loop_size, num_loop, ctx, m);

    int_formula = m.mk_and(int_formula, m.mk_and(int_formula_len_cond, int_formula_pos_cond));


    result = m_int_solver.check_sat(int_formula) == lbool::l_true;
    ENSURE(result);


    // part 3
    int_formula= m.mk_true();
    int_formula_pos_cond = m.mk_false();
    int_formula_len_cond = m.mk_true();


    str2_class.str_var_symbol_match_to_expr_ref(int_formula, L_pre_len, R_pre_len, L_str, R_var, loop_size, num_loop, ctx, m);
    str2_class.str_var_symbol_not_match_to_expr_ref(int_formula_pos_cond, int_formula_len_cond, L_pre_len, R_pre_len, L_str, R_var, loop_size, num_loop, ctx, m);

    int_formula = m.mk_and(int_formula, m.mk_and(int_formula_len_cond, int_formula_pos_cond));


    result = m_int_solver.check_sat(m.mk_not(int_formula)) == lbool::l_true;
    ENSURE(result);
}


static void var_str_symbol_not_match_to_expr_ref_func_test()
{
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_model = true;
    smt::context ctx(m, params);

    arith_util m_util_a(m);
    seq_util m_util_s(m);

    smt::theory_str2 str2_class(m, ctx.get_fparams());
    smt::int_expr_solver m_int_solver(m, ctx.get_fparams());

    expr_ref int_formula(m.mk_true(), m);
    expr_ref int_formula_pos_cond(m.mk_false(), m);
    expr_ref int_formula_len_cond(m.mk_true(), m);
    expr_ref L_pre_len(m_util_a.mk_int(0), m);
    expr_ref R_pre_len(m_util_a.mk_int(0), m);


    std::string L_var = "x";
    std::string R_str = "";
    for (int i = 0; i < 10; i++)
        R_str.append("abc");
    std::string R_str_2 = "abc";
    unsigned loop_size = 2;
    unsigned num_loop = 15;

    str2_class.var_str_symbol_match_to_expr_ref(int_formula, L_pre_len, R_pre_len, L_var, R_str_2, loop_size, num_loop, ctx, m);
    str2_class.var_str_symbol_not_match_to_expr_ref(int_formula_pos_cond, int_formula_len_cond, L_pre_len, R_pre_len, L_var, R_str, loop_size, num_loop, ctx, m);



    int_formula = m.mk_and(int_formula, m.mk_and(int_formula_len_cond, int_formula_pos_cond));

    bool result = m_int_solver.check_sat(int_formula) == lbool::l_true;
    ENSURE(result);
}


static void var_var_symbol_not_match_to_expr_ref_func_test()
{
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_model = true;
    smt::context ctx(m, params);

    arith_util m_util_a(m);
    seq_util m_util_s(m);

    smt::theory_str2 str2_class(m, ctx.get_fparams());
    smt::int_expr_solver m_int_solver(m, ctx.get_fparams());

    expr_ref int_formula(m.mk_true(), m);
    expr_ref int_formula_pos_cond(m.mk_false(), m);
    expr_ref int_formula_len_cond(m.mk_true(), m);
    expr_ref L_pre_len(m_util_a.mk_int(0), m);
    expr_ref R_pre_len(m_util_a.mk_int(0), m);


    std::string L_str = "abc";
    std::string L_var = "y";
    std::string R_var = "x";
    std::string R_str = "agc";
    unsigned loop_size = 4;
    unsigned num_loop = 1;

    str2_class.str_var_symbol_match_to_expr_ref(int_formula, L_pre_len, R_pre_len, L_str, R_var, loop_size, num_loop, ctx, m);
    str2_class.var_str_symbol_match_to_expr_ref(int_formula, L_pre_len, R_pre_len, L_var, R_str, loop_size, num_loop, ctx, m);
    str2_class.var_var_symbol_not_match_to_expr_ref(int_formula_pos_cond, int_formula_len_cond, L_pre_len, R_pre_len, L_var, R_var, loop_size, num_loop, ctx, m);

    int_formula = m.mk_and(int_formula, m.mk_and(int_formula_len_cond, int_formula_pos_cond));

    bool result = m_int_solver.check_sat(int_formula) == lbool::l_true;
    ENSURE(result);


    // part 2
    int_formula = m.mk_true();
    int_formula_pos_cond = m.mk_false();
    int_formula_len_cond = m.mk_true();
    L_str = "abcd";
    R_str = "abcd";

    str2_class.str_var_symbol_match_to_expr_ref(int_formula, L_pre_len, R_pre_len, L_str, R_var, loop_size, num_loop, ctx, m);
    str2_class.var_str_symbol_match_to_expr_ref(int_formula, L_pre_len, R_pre_len, L_var, R_str, loop_size, num_loop, ctx, m);
    str2_class.var_var_symbol_not_match_to_expr_ref(int_formula_pos_cond, int_formula_len_cond, L_pre_len, R_pre_len, L_var, R_var, loop_size, num_loop, ctx, m);

    int_formula = m.mk_and(int_formula, m.mk_and(int_formula_len_cond, int_formula_pos_cond));

    result = m_int_solver.check_sat(m.mk_not(int_formula)) == lbool::l_true;
    ENSURE(result);
}


void tst_theory_str() {
    //test_int_expr_solver();
    //func_test_word_term_to_list();
    /*
    str_str_symbol_match_to_expr_ref_func_test_1();
    std::cout << "str_str_symbol_match_to_expr_ref_func_test_1: tested.\n";
    str_str_symbol_match_to_expr_ref_func_test_2();
    std::cout << "str_str_symbol_match_to_expr_ref_func_test_2: tested.\n";
    str_str_symbol_match_to_expr_ref_func_test_3();
    std::cout << "str_str_symbol_match_to_expr_ref_func_test_3: tested.\n";
    str_str_symbol_match_to_expr_ref_func_test_4();
    std::cout << "str_str_symbol_match_to_expr_ref_func_test_4: tested.\n";
    //*/
    /*
    str_var_symbol_match_to_expr_ref_func_test_1();
    std::cout << "str_var_symbol_match_to_expr_ref_func_test_1: tested.\n";
    str_var_symbol_match_to_expr_ref_func_test_2();
    std::cout << "str_var_symbol_match_to_expr_ref_func_test_2: tested.\n";
    str_var_symbol_match_to_expr_ref_func_test_3();
    std::cout << "str_var_symbol_match_to_expr_ref_func_test_3: tested.\n";
    std::cout << "str_var_symbol_match_to_expr_ref_func_test_4: testing.\n";
    str_var_symbol_match_to_expr_ref_func_test_4();
    std::cout << "str_var_symbol_match_to_expr_ref_func_test_4: tested.\n";
    //*/
    /*
    var_str_symbol_match_to_expr_ref_func_test_1();
    std::cout << "var_str_symbol_match_to_expr_ref_func_test_1: tested.\n";
    var_str_symbol_match_to_expr_ref_func_test_2();
    std::cout << "var_str_symbol_match_to_expr_ref_func_test_2: tested.\n";
    var_str_symbol_match_to_expr_ref_func_test_3();
    std::cout << "var_str_symbol_match_to_expr_ref_func_test_3: tested.\n";
    var_str_symbol_match_to_expr_ref_func_test_4();
    std::cout << "var_str_symbol_match_to_expr_ref_func_test_4: tested.\n";
    var_str_symbol_match_to_expr_ref_func_test_5();
    std::cout << "var_str_symbol_match_to_expr_ref_func_test_5: tested.\n";
    var_str_symbol_match_to_expr_ref_func_test_6();
    std::cout << "var_str_symbol_match_to_expr_ref_func_test_6: tested.\n";
    //*/
    /*
    var_var_symbol_match_to_expr_ref_func_test1();
    std::cout << "var_var_symbol_match_to_expr_ref_func_test1: tested. \n";
    var_var_symbol_match_to_expr_ref_func_test2();
    std::cout << "var_var_symbol_match_to_expr_ref_func_test2: tested. \n";
    std::cout << "var_var_symbol_match_to_expr_ref_func_test3: testing. \n";
    var_var_symbol_match_to_expr_ref_func_test3();
    std::cout << "var_var_symbol_match_to_expr_ref_func_test3: tested. \n";
    //*/
    /*
    len_update_func_test1();
    std::cout << "len_update_func_test1: tested. \n";
    //*/
    /*
    eq_word_term_lists_to_expr_ref_func_test1();
    std::cout << "eq_word_term_lists_to_expr_ref_func_test1(): tested\n";
    eq_word_term_lists_to_expr_ref_func_test2();
    std::cout << "eq_word_term_lists_to_expr_ref_func_test2(): tested\n";
    eq_word_term_lists_to_expr_ref_func_test3();
    std::cout << "eq_word_term_lists_to_expr_ref_func_test3(): tested\n";
    //*/
    /*
    str_str_symbol_not_match_to_expr_ref_func_test();
    std::cout << "str_str_symbol_not_match_to_expr_ref_func_test: tested.\n";
    str_var_symbol_not_match_to_expr_ref_func_test_1();
    std::cout << "str_var_symbol_not_match_to_expr_ref_func_test_1(): tested\n";
    var_str_symbol_not_match_to_expr_ref_func_test();
    std::cout << "var_str_symbol_not_match_to_expr_ref_func_test_(): tested\n";
    std::cout << "var_var_symbol_not_match_to_expr_ref_func_test_(): testing\n";
    var_var_symbol_not_match_to_expr_ref_func_test();
    std::cout << "var_var_symbol_not_match_to_expr_ref_func_test_(): tested\n";
    //*/
    
    str_var_symbol_match_to_expr_ref_func_test_4();
    //ineq_word_term_lists_to_expr_ref_func_test1();
    //std::cout << "ineq_word_term_lists_to_expr_ref_func_test1(): tested\n";
    
}

/*
static void ineq_word_term_lists_to_expr_ref_func_test1() {
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_model = true;
    smt::context ctx(m, params);
    arith_util m_util_a(m);
    seq_util m_util_s(m);
    smt::theory_str2 str2_class(m, ctx.get_fparams());
    smt::int_expr_solver m_int_solver(m, ctx.get_fparams());

    unsigned loop_size = 3;
    unsigned num_loop = 2;

    std::list<std::pair<char, std::string>> L_word_term_list, R_word_term_list;
    std::list<std::pair<char, std::string>> L_word_term_list_2, R_word_term_list_2;

    L_word_term_list.push_back(std::make_pair('S', "ab"));
    L_word_term_list.push_back(std::make_pair('V', "x"));
    L_word_term_list.push_back(std::make_pair('S', "de"));
    R_word_term_list.push_back(std::make_pair('S', "abcde"));

    expr_ref temp_formula = str2_class.ineq_word_term_lists_to_expr_ref(ctx, m, L_word_term_list, R_word_term_list, loop_size, num_loop);
    L_word_term_list.pop_front();
    L_word_term_list.pop_front();
    L_word_term_list.pop_front();
    R_word_term_list.pop_front();



    // part 2


    L_word_term_list.push_back(std::make_pair('S', "ab"));
    L_word_term_list.push_back(std::make_pair('V', "z"));
    L_word_term_list.push_back(std::make_pair('S', "de"));
    R_word_term_list.push_back(std::make_pair('S', "abcde"));
    expr_ref int_formula = str2_class.ineq_word_term_lists_to_expr_ref(ctx, m, L_word_term_list, R_word_term_list, loop_size, num_loop);
    L_word_term_list_2.push_back(std::make_pair('V', "z"));
    R_word_term_list_2.push_back(std::make_pair('V', "z"));
    R_word_term_list_2.push_back(std::make_pair('V', "z"));
    int_formula = m.mk_and(int_formula, str2_class.eq_word_term_lists_to_expr_ref(ctx, m, L_word_term_list_2, R_word_term_list_2, loop_size, num_loop));


    int_formula = m.mk_and(int_formula, temp_formula);

    bool result = m_int_solver.check_sat(int_formula) == lbool::l_true;
    ENSURE(result);
}*/