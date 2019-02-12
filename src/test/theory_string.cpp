#include "smt/theory_str.h"
#include "util/debug.h"
#include "smt/smt_context.h"
#include "ast/seq_decl_plugin.h"
#include "ast/reg_decl_plugins.h"
#include "ast/ast_pp.h"
#include <sstream>
class string_fuzzer {
    ast_manager& m;
    smt_params params;
    smt::context& ctx;
    seq_util m_util_s;

public:
    string_fuzzer(ast_manager& m, smt::context& ctx): m{m}, ctx{ctx}, m_util_s{m} {
        srand (time(NULL));
    }


    void testoaut(){
        expr_ref string_exp= genRandomExpr(2);
        std::cout<<mk_pp(string_exp,m)<<std::endl;
        smt::str::oaut_adaptor m_oaut_imp(m);
        smt::str::automaton::sptr aut = m_oaut_imp.mk_from_re_expr(string_exp);
        aut->display(std::cout);

    }
    void testzaut(){
        expr_ref string_exp= genRandomExpr(2);
        std::cout<<mk_pp(string_exp,m)<<std::endl;
        smt::str::zaut_adaptor m_zaut_imp(m,ctx);
        smt::str::automaton::sptr aut = m_zaut_imp.mk_from_re_expr(string_exp);
        aut->display(std::cout);

    }

    void crosscheck(){
        expr_ref string_exp= genRandomExpr(2);
        std::cout<<mk_pp(string_exp,m)<<std::endl;
        smt::str::zaut_adaptor m_zaut_imp(m,ctx);
        smt::str::automaton::sptr zaut = m_zaut_imp.mk_from_re_expr(string_exp);
//        smt::str::oaut_adaptor m_oaut_imp(m);
//        smt::str::automaton::sptr oaut = m_oaut_imp.mk_from_re_expr(string_exp);

        for(auto& prefix:  getTestStrings( 5, 2)){
            std::cout<<prefix<<std::endl;
            std::list<smt::str::automaton::ptr> prefix_automata = zaut->remove_prefix(prefix);
            std::cout<<"remove_prefix: Done"<<std::endl;


//            bool oaut_has_this_word=!oaut->remove_prefix(prefix).empty();
//            std::cout<<"oaut_has_this_word:"<<oaut_has_this_word<<std::endl;

//            if(zaut_has_this_word != oaut_has_this_word){
//                std::cout<<prefix<<std::endl;
//
//            }
        }

    }
private:
    std::set<zstring> getTestStrings(size_t len, size_t width){
        const unsigned int maximal_char = smt::str::automaton::maximal_char;
        std::set<zstring> results;

        if(len == 0){
            results.insert("");
            return results;
        }
        for(auto& prefix:  getTestStrings( len-1, width)){
            for(int i = 0 ;i < width; i++) {
                int charSelection = random() % (maximal_char * 2) - 128;
                charSelection = (charSelection > 0) ? charSelection : 0;
                charSelection = (charSelection > maximal_char) ? maximal_char : charSelection;
                results.insert(prefix + (char) charSelection);
            }
        }

        return results;

    }
    expr_ref genRandomExpr(int depth){

        if(depth == 0){
            int option = random() % 4;

            switch (option) {
//                case 0: {//range
//
//                    int low = random()%230;
//
//                    std::stringstream ss;
//                    ss << low;
//                    zstring low_str(ss.str().c_str());
//                    expr_ref low_bound_expr ={m_util_s.re.mk_to_re(m_util_s.str.mk_string(low_str)), m};
//                    ss.clear();
//                    ss << (low+10);
//                    zstring high_str(ss.str().c_str());
//                    expr_ref high_bound_expr ={m_util_s.re.mk_to_re(m_util_s.str.mk_string(high_str)), m};
//
//                    expr_ref range = {m_util_s.re.mk_range(low_bound_expr,high_bound_expr), m};
//                    return range;
//                }
//                case 1: {//full char
//                    expr_ref full_c = {m_util_s.re.mk_full_char(m_util_s.str.mk_string_sort()), m};
//                    return full_c;
//                }
//                case 2: {//full seq
//                    expr_ref full_c = {m_util_s.re.mk_full_seq(m_util_s.str.mk_string_sort()), m};
//                    return full_c;
//                }
                default: {//constant string
                    int len = rand() % 9 +1;
                    zstring content = "";
                    for (int i = 0; i < len; i++) {
                        char nextChar = rand() % 256;
                        content = content + nextChar;
                    }
//                    std::cout<<content<<std::endl;
                    expr_ref con_string = {m_util_s.re.mk_to_re(m_util_s.str.mk_string(content)), m};
                    return con_string;
                }
            }
        }else {

            int option = random() % 6;

            switch (option) {
//                case 0: {
//                    expr_ref exp = genRandomExpr(depth - 1);
//                    expr_ref comp = {m_util_s.re.mk_complement(exp), m};
//                    return comp;
//
//                }
                case 1: {// union
                    expr_ref exp1 = genRandomExpr(depth - 1);
                    expr_ref exp2 = genRandomExpr(depth - 1);
                    expr_ref union_re = {m_util_s.re.mk_union(exp1, exp2), m};
                    return union_re;
                }
//                case 2: {// intersection
//                    expr_ref exp1 = genRandomExpr(depth - 1);
//                    expr_ref exp2 = genRandomExpr(depth - 1);
//                    expr_ref inter_re = {m_util_s.re.mk_inter(exp1, exp2), m};
//                    return inter_re;
//                }
                case 3: {// star
                    expr_ref exp = genRandomExpr(depth - 1);
                    expr_ref star = {m_util_s.re.mk_star(exp), m};
                    return star;
                }
//                case 4: {// plus
//                    expr_ref exp = genRandomExpr(depth - 1);
//                    expr_ref plus = {m_util_s.re.mk_plus(exp), m};
//                    return plus;
//                }
//                case 5: {// opt
//
//                    expr_ref exp = genRandomExpr(depth - 1);
//                    expr_ref opt = {m_util_s.re.mk_opt(exp), m};
//                    return opt;
//                }
                default: {// concat
                    expr_ref exp1 = genRandomExpr(depth - 1);
                    expr_ref exp2 = genRandomExpr(depth - 1);
                    expr_ref concat = {m_util_s.re.mk_concat(exp1, exp2), m};
                    return concat;
                }
            }
        }
    }
};

static void zaut_adaptor_test(){


    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_model = true;
    smt::context ctx(m, params);
    string_fuzzer str(m,ctx);

    for(int i=0;i<100;i++){
        str.testzaut();
    }
}


static void zaut_oaut_crosscheck_test(){


    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_model = true;
    smt::context ctx(m, params);
    string_fuzzer str(m,ctx);

    for(int i=0;i<100;i++){
        str.crosscheck();
    }
}

static void oaut_adaptor_test(){

    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_model = true;
    smt::context ctx(m, params);
    string_fuzzer str(m,ctx);

    for(int i=0;i<100;i++){
        str.testoaut();
    }
}


static void oaut_tst(){
    using namespace smt::str;
    const float One = 0;
    fst::StdVectorFst f;
    f.AddState();   // 1st state will be state 0 (returned by AddState)
    f.AddState();
    f.AddState();
    f.AddState();
    f.AddState();
    f.SetStart(0);
    f.AddArc(0, fst::StdArc('a', 'a', One, 1));
    f.AddArc(0, fst::StdArc('b', 'b', One, 2));
    f.AddArc(1, fst::StdArc('b', 'b', One, 3));
    f.AddArc(2, fst::StdArc('a', 'a', One, 4));
    f.AddArc(3, fst::StdArc('a', 'a', One, 1));
    f.AddArc(4, fst::StdArc('b', 'b', One, 2));
    f.SetFinal(3, One);
    f.SetFinal(4, One);

    std::shared_ptr<oaut> result = std::make_shared<smt::str::oaut>(f);

    fst::StdVectorFst g;
    g.AddState();
    g.AddState();
    g.AddState();
    g.AddState();
    g.AddState();
    g.AddState();
    g.AddState();
    g.SetStart(0);
    g.AddArc(0, fst::StdArc('a', 'a', One, 1));
    g.AddArc(0, fst::StdArc('b', 'b', One, 2));
    g.AddArc(1, fst::StdArc('b', 'b', One, 3));
    g.AddArc(2, fst::StdArc('a', 'a', One, 4));
    g.AddArc(3, fst::StdArc('a', 'a', One, 5));
    g.AddArc(4, fst::StdArc('b', 'b', One, 6));
    g.AddArc(5, fst::StdArc('b', 'b', One, 3));
    g.AddArc(6, fst::StdArc('a', 'a', One, 4));

    g.SetFinal(3, One);
    g.SetFinal(4, One);


    std::shared_ptr<oaut> result2 = std::make_shared<smt::str::oaut>(g);

    bool equivalent_test_result=(*result == *result2);
    std::cout<<"Equalivalent function test: "<<equivalent_test_result<<std::endl;
    ENSURE(equivalent_test_result);

    g.AddArc(1, fst::StdArc('c', 'c', One, 3));
    result2 = std::make_shared<smt::str::oaut>(g);

    bool equivalent_test_result2=(*result != *result2);
    std::cout<<"Equalivalent function test2: "<<equivalent_test_result2<<std::endl;
    ENSURE(equivalent_test_result2);

    bool is_deterministic_test_result=(result->is_deterministic());
    std::cout<<"Is_deterministic function test: "<<is_deterministic_test_result<<std::endl;
    ENSURE(is_deterministic_test_result);

    g.AddArc(1, fst::StdArc('c', 'c', One, 2));
    result2 = std::make_shared<smt::str::oaut>(g);
    bool is_deterministic_test_result2=(!result2->is_deterministic());
    std::cout<<"Is_deterministic function test: "<<is_deterministic_test_result2<<std::endl;
    ENSURE(is_deterministic_test_result2);

    std::shared_ptr<smt::str::automaton> result3=result2->determinize();
    bool clone_and_determinize_test_result = (*result3 == *result2);
    std::cout<<"Clone and determinize functions test: "<<clone_and_determinize_test_result<<std::endl;
    ENSURE(clone_and_determinize_test_result);

    std::shared_ptr<smt::str::automaton> result4 = result3->complement();
    std::shared_ptr<smt::str::automaton> result5 = result4->intersect_with(result3);
    bool complement_intersection_and_is_empty_test_result=result5->is_empty();
    std::cout<<"Complement, intersection, and is_empty functions test: "<<complement_intersection_and_is_empty_test_result<<std::endl;
    ENSURE(complement_intersection_and_is_empty_test_result);

    std::shared_ptr<smt::str::automaton> result6 = result4->union_with(result3);
    std::shared_ptr<smt::str::automaton> result7 = result6->complement();
    bool complement_union_and_is_empty_test_result=result7->is_empty();
    std::cout<<"Complement, union, and is_empty functions test: "<<complement_union_and_is_empty_test_result<<std::endl;
    ENSURE(complement_union_and_is_empty_test_result);

    std::set<smt::str::automaton::state> reachable = (result2->reachable_states(result2->get_init()));
    std::set<smt::str::automaton::state> onestep_reachable = (result2->successors(result2->get_init()));
    std::set<smt::str::automaton::state> onestep_a_reachable = (result2->successors(result2->get_init(), "a"));
    std::set<smt::str::automaton::state> out;
    std::set<smt::str::automaton::state> out2;
    std::set_difference(onestep_reachable.begin(), onestep_reachable.end(),
                        reachable.begin(), reachable.end(),
                        std::inserter(out, out.begin()));
    std::set_difference(reachable.begin(), reachable.end(),
                        onestep_reachable.begin(), onestep_reachable.end(),
                        std::inserter(out2, out2.begin()));
    bool reachable_states_and_successors_test_result1= ((out.empty()) && (!out2.empty()));
    std::cout<<"Reachable_states and successors functions test1: "<<reachable_states_and_successors_test_result1<<std::endl;
    ENSURE(reachable_states_and_successors_test_result1);

    std::set_difference(onestep_a_reachable.begin(), onestep_a_reachable.end(),
                        onestep_reachable.begin(), onestep_reachable.end(),
                        std::inserter(out, out.begin()));
    std::set_difference(onestep_reachable.begin(), onestep_reachable.end(),
                        onestep_a_reachable.begin(), onestep_a_reachable.end(),
                        std::inserter(out2, out2.begin()));
    bool reachable_states_and_successors_test_result2= ((out.empty()) && (!out2.empty()));
    std::cout<<"Reachable_states and successors functions test2: "<<reachable_states_and_successors_test_result2<<std::endl;
    ENSURE(reachable_states_and_successors_test_result2);

    bool split_test_result=(result2->split().size()==result2->reachable_states(result2->get_init()).size());
    std::cout<<"Split function test: "<<split_test_result<<std::endl;
    ENSURE(split_test_result);

    bool remove_prefix_test_result=(result2->remove_prefix("ab").size()==1);
    std::cout<<"Remove_prefix function test: "<<remove_prefix_test_result<<std::endl;
    ENSURE(remove_prefix_test_result);


}

void tst_theory_string() {
    zaut_oaut_crosscheck_test();
//    oaut_tst();
//    oaut_adaptor_test();
//    zaut_adaptor_test();
}
