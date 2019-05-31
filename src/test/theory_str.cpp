#include "smt/theory_str/theory_str.h"
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


    void testoaut(){
        expr_ref string_exp= genRandomExpr(2);
        smt::str::oaut_adaptor m_oaut_imp(m);
        smt::str::automaton::sptr aut = m_oaut_imp.mk_from_re_expr(string_exp, true);

    }
    void testzaut(){
        expr_ref string_exp= genRandomExpr(2);
        smt::str::zaut_adaptor m_zaut_imp(m,ctx);
        smt::str::automaton::sptr aut = m_zaut_imp.mk_from_re_expr(string_exp, true);

    }

    void crosscheck(int i){
        expr_ref string_exp= genRandomExpr(2);
        smt::str::zaut_adaptor m_zaut_imp(m,ctx);
        smt::str::oaut_adaptor m_oaut_imp(m);

        smt::str::automaton::sptr zaut = m_zaut_imp.mk_from_re_expr(string_exp, true)->determinize();
        smt::str::automaton::sptr oaut = m_oaut_imp.mk_from_re_expr(string_exp, true);

        expr_ref string_exp2= genRandomExpr(2);
        smt::str::automaton::sptr zaut2 = m_zaut_imp.mk_from_re_expr(string_exp2, true)->determinize();
        smt::str::automaton::sptr oaut2 = m_oaut_imp.mk_from_re_expr(string_exp2, true);


        std::ofstream oaut_file, zaut_file, re_file;

        re_file.open ("re"+std::to_string(4*i)+".txt");
        re_file<<mk_pp(string_exp,m)<<std::endl;
        re_file<<mk_pp(string_exp2,m)<<std::endl;
        re_file.close();

        oaut_file.open ("oaut"+std::to_string(4*i)+".txt");
        std::cout<<"oaut re-to-automaton"<<std::endl;
        static_cast<smt::str::oaut*>(oaut.get())->display_timbuk(oaut_file);
        oaut_file.close();

        zaut_file.open ("zaut"+std::to_string(4*i)+".txt");
        std::cout<<"zaut re-to-automaton"<<std::endl;
        static_cast<smt::str::zaut*>(zaut.get())->display_timbuk(zaut_file);
        zaut_file.close();

        oaut_file.open ("oaut"+std::to_string(4*i+1)+".txt");
        std::cout<<"oaut complement"<<std::endl;
        static_cast<smt::str::oaut*>(oaut->complement().get())->display_timbuk(oaut_file);
        oaut_file.close();

        zaut_file.open ("zaut"+std::to_string(4*i+1)+".txt");
        std::cout<<"zaut complement"<<std::endl;
        static_cast<smt::str::zaut*>(zaut->complement().get())->display_timbuk(zaut_file);
        zaut_file.close();

        oaut_file.open ("oaut"+std::to_string(4*i+2)+".txt");
        std::cout<<"oaut determinize"<<std::endl;
        static_cast<smt::str::oaut*>(oaut->determinize().get())->display_timbuk(oaut_file);
        oaut_file.close();

        zaut_file.open ("zaut"+std::to_string(4*i+2)+".txt");
        std::cout<<"zaut determinize"<<std::endl;
        static_cast<smt::str::zaut*>(zaut->determinize().get())->display_timbuk(zaut_file);
        zaut_file.close();

        oaut_file.open ("oaut"+std::to_string(4*i+3)+".txt");
        std::cout<<"oaut intersection"<<std::endl;
        static_cast<smt::str::oaut*>(oaut->intersect_with(oaut2).get())->display_timbuk(oaut_file);
        oaut_file.close();

        zaut_file.open ("zaut"+std::to_string(4*i+3)+".txt");
        std::cout<<"zaut intersection"<<std::endl;
        static_cast<smt::str::zaut*>(zaut->intersect_with(zaut2).get())->display_timbuk(zaut_file);
        zaut_file.close();

//        oaut_file.open ("oaut"+std::to_string(5*i+4)+".txt");
//        std::cout<<"oaut append"<<std::endl;
//        static_cast<smt::str::oaut*>(oaut->append(oaut2).get())->display_timbuk(oaut_file);
//        oaut_file.close();
//
//        zaut_file.open ("zaut"+std::to_string(5*i+4)+".txt");
//        std::cout<<"zaut append"<<std::endl;
//        static_cast<smt::str::zaut*>(zaut->append(zaut2).get())->display_timbuk(zaut_file);
//        zaut_file.close();

//        for(auto& prefix:  getTestStrings( 2, 2)){
//            std::cout<<prefix<<std::endl;
//            std::list<smt::str::automaton::ptr> prefix_automata_oaut = oaut->remove_prefix(prefix);
//            std::cout<<"remove_prefix: Done"<<std::endl;
//            bool oaut_has_the_word =false;
//            for(auto& oa : prefix_automata_oaut){
//                if(!oa->is_empty()){
//                    oaut_has_the_word=true;
//                }
//            }
//            std::cout<<"oaut_has_this_word:"<<oaut_has_the_word<<std::endl;
//
////            bool oaut_has_this_word=!oaut->remove_prefix(prefix).empty();
////            std::cout<<"oaut_has_this_word:"<<oaut_has_this_word<<std::endl;
//
////            if(zaut_has_this_word != oaut_has_this_word){
////                std::cout<<prefix<<std::endl;
////
////            }
//        }

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
            for(int i = 0 ;i < maximal_char; i++) {
                results.insert(prefix + (char) i);
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
                    const unsigned int maximal_char = smt::str::automaton::maximal_char;
                    int len = rand() % 2 +1;
                    zstring content = "";
                    for (int i = 0; i < len; i++) {
                        int charSelection = random() % (maximal_char * 2) - 128;
                        charSelection = (charSelection > 0) ? charSelection : 0;
                        charSelection = (charSelection > maximal_char) ? maximal_char : charSelection;
                        content = content + (char)charSelection;
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

static void tst_zaut_adaptor(){


    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_model = true;
    smt::context ctx(m, params);
    string_fuzzer str(m,ctx);

    for(int i=0;i<100;i++){
        str.testzaut();
    }
    std::cout<<"zaut_adaptor test: 1"<<std::endl;

}


static void tst_zaut_oaut_crosscheck(){


    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_model = true;
    smt::context ctx(m, params);
    string_fuzzer str(m,ctx);

    for(int i=0;true;i++){
        str.crosscheck(i);
    }
    std::cout<<"zaut and oaut crosscheck test: 1"<<std::endl;
}

static void tst_oaut_adaptor(){

    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_model = true;
    smt::context ctx(m, params);
    string_fuzzer str(m,ctx);

    for(int i=0;i<100;i++){
        str.testoaut();
    }
    std::cout<<"oaut_adaptor test: 1"<<std::endl;

}


static void tst_oaut(){
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

static void tst_testtest() {
    std::cout << "testtest: 11111" << std::endl;
}

using namespace smt::str;




// parameters
std::map<int,char> tst_alphabets = {{0,'a'},{1,'b'},{2,'c'},{3,'d'},{4,'e'},{5,'f'},{6,'g'},{7,'h'}};  // use only these characters
unsigned int tst_strlen_max = 5;  // max length of a string (string constant or variable name)

static zstring gen_rnd_name() {
    unsigned int l_range = (rand() % tst_strlen_max);
    zstring ret_zstr = "";
    for (int i=0; i < l_range; i++) {
        ret_zstr = ret_zstr + tst_alphabets[rand() % tst_alphabets.size()];
    }
    std::cout << "gen_rnd_name: " << ret_zstr.encode() << std::endl;
    return ret_zstr;
}

class str_fuzzer {
    ast_manager& m;
    smt_params params;
    smt::context ctx;
    seq_util m_util_s;
    arith_util m_util_a;

public:
    str_fuzzer(ast_manager& m): m(m), ctx(m,params), m_util_s(m), m_util_a(m) {
        params.m_model = true;
        params.m_pb_enable_simplex = true;
    }
    ast_manager& get_manager() const { return m; }
    app_ref gen_rnd_str_const() {
        app_ref ret(m_util_s.str.mk_string(gen_rnd_name()),m);
        std::cout << "gen_rnd_str_const:" << mk_pp(ret.get(),m) << std::endl;
        return ret;
    }
    app_ref gen_str_const(zstring name) {
        app_ref ret(m_util_s.str.mk_string(name),m);
        std::cout << "gen_str_const:" << mk_pp(ret.get(),m) << std::endl;
        return ret;
    }
    var_ref gen_str_var(unsigned idx) {
        var_ref ret(m.mk_var(idx,m_util_s.str.mk_string_sort()),m);
        return ret;
    }
    zstring get_const_zstring(app* n) {  // only for constant
        SASSERT(is_app(n));
        return n->get_decl()->get_parameter(0).get_symbol().bare_str();
    }
    void tst_elem() {
        std::cout << "str_fuzz::tst_elem()" << std::endl;
        app_ref const1_ref = gen_rnd_str_const();
        std::cout << "const1(" << get_const_zstring(const1_ref.get()) << "): " << mk_pp(const1_ref.get(),m) << std::endl;
        zstring zname2 = "abcde";
        zstring zname3 = "abcde";
        app_ref const2_ref = gen_str_const(zname2);
        app_ref const3_ref = gen_str_const(zname3);
        std::cout << "const2:" << mk_pp(const2_ref.get(),m) << std::endl;
        std::cout << "const3:" << mk_pp(const3_ref.get(),m) << std::endl;
        std::cout << "id of const1: " << const1_ref->get_id() << std::endl;
        std::cout << "id of const2: " << const2_ref->get_id() << std::endl;
        std::cout << "id of const3: " << const3_ref->get_id() << std::endl;
        ENSURE(const2_ref.get()==const3_ref.get())
        var_ref var1_ref = gen_str_var(0);
        std::cout << "var1(" << var1_ref.get()->get_idx() << "):" << mk_pp(var1_ref.get(),m) << std::endl;
    }
    void tst_word_term() {
        std::cout << "str_fuzz::tst_word_term()" << std::endl;
        unsigned idx = 0;
        zstring zstr1 = "abcde", zstr2 = "bbcde", zstr3 = "cde";
        word_term wt1 = word_term::from_string(zstr1);
        word_term wt1a = word_term::from_string(zstr1);
        word_term wt2 = word_term::from_string(zstr2);
        word_term wt3 = word_term::from_string(zstr3);
        ENSURE(wt1==wt1a)
        ENSURE(wt1.has_constant())
        ENSURE(!wt1.empty())
        ENSURE(wt1.length()==5)
        ENSURE(wt1.count_const()==5)
        ENSURE(wt1.head().value().encode()=="a")
        ENSURE(wt1.get(2).value().encode()=="c")
        ENSURE(wt1.get(wt1.length()-1).value().encode()=="e")
        ENSURE(wt1.check_head(element::t::CONST))

        var_ref var1_exprf = gen_str_var(idx++);
        word_term wt3a = word_term::from_variable(zstr1,var1_exprf.get());
        element var1_elm(element::t::VAR,zstr1,var1_exprf.get());
        ENSURE(wt3a.has_variable())
        ENSURE(wt3a.count_var(var1_elm)==1)
        wt3a.concat(wt3a);
        ENSURE(wt3a.count_var(var1_elm)==2)
        ENSURE(wt3a.head()==wt3a.get(wt3a.length()-1))
        wt3a.remove_head();
        ENSURE(wt3a.count_var(var1_elm)==1)

        ENSURE(wt2.get(3)==wt3.get(1))
        word_term wt4(wt3.content());
        ENSURE(wt4==wt3)
        word_term wt5({element(element::t::CONST,zstr3[0],gen_str_const(zstr3[0]).get()),
                       element(element::t::CONST,zstr3[1],gen_str_const(zstr3[1]).get()),
                       element(element::t::CONST,zstr3[2],gen_str_const(zstr3[2]).get())});
        ENSURE(wt5==wt3)

//        var_ref var2_exprf = gen_str_var(idx++);
//        word_term wt3b = word_term::from_variable(zstr2,var2_exprf.get());
//        element var2_elm(element::t::VAR,zstr2,var2_exprf.get());
        wt1.replace(wt1.get(2),wt3);
        word_term wt1r = word_term::from_string("abcdede");
        ENSURE(wt1==wt1r)
    }
    void tst_word_equation() {
        std::cout << "str_fuzz::tst_word_equation()" << std::endl;
        unsigned idx = 0;
        word_term wt1c = word_term::from_string("abcde");
        var_ref var1_exprf = gen_str_var(idx++);
        word_term wt1v = word_term::from_variable("A",var1_exprf.get());
        element var1_elm(element::t::VAR,"A",var1_exprf.get());
        word_equation we1(wt1v,wt1c);
        ENSURE(we1.heads().first==wt1v.get(0))
        ENSURE(we1.heads().second==wt1c.get(0))
        ENSURE(we1.count_var(var1_elm)==1)
        ENSURE(we1.variables().size()==1)
        ENSURE(*we1.variables().begin()==var1_elm)
        word_equation we2(wt1c,wt1v);
        ENSURE(we1==we2)
        word_term wt2c = word_term::from_string("abcde");
        var_ref var2_exprf = gen_str_var(idx++);
        word_term wt2v = word_term::from_variable("A",var2_exprf.get());
        ENSURE(we1.lhs()==wt2v)
        ENSURE(we1.rhs()==wt2c)
        ENSURE(!we1.empty())
        ENSURE(word_equation(word_term(),word_term()).empty())

        word_equation we3(wt2c,wt2v);
        ENSURE(we1==we3)

    }

};

static void fuzz_str()
{
    ast_manager m;
    reg_decl_plugins(m);
    str_fuzzer fuzzer(m);
    fuzzer.tst_elem();
    fuzzer.tst_word_term();
    fuzzer.tst_word_equation();

//    std::cout << "round 2" << std::endl;
//    app_ref const1_ref = fuzzer.gen_rnd_str_const();
//    std::cout << "const1:" << mk_pp(const1_ref.get(),m) << std::endl;
//    zstring zname = "abcdefg";
//    app_ref const2_ref = fuzzer.gen_str_const(zname);
//    app_ref const3_ref = fuzzer.gen_str_const(zname);
//    std::cout << "const2:" << mk_pp(const2_ref.get(),m) << std::endl;
//    std::cout << "const3:" << mk_pp(const3_ref.get(),m) << std::endl;
//    std::cout << "id of const1: " << const1_ref->get_id() << std::endl;
//    std::cout << "family id of const1: " << const1_ref->get_family_id() << std::endl;
//    std::cout << "id of const2: " << const2_ref->get_id() << std::endl;
//    std::cout << "family id of const2: " << const2_ref->get_family_id() << std::endl;
//    std::cout << "id of const3: " << const3_ref->get_id() << std::endl;
//    std::cout << "family id of const3: " << const3_ref->get_family_id() << std::endl;
//    ENSURE(const2_ref.get()==const3_ref.get())
//
//    int idx=0;
//    var_ref var1_ref = fuzzer.gen_str_var(idx++);
//    std::cout << "var1: " << mk_pp(var1_ref.get(),m) << std::endl;
//    std::cout << "id of var1: " << var1_ref->get_id() << std::endl;
}

static void tst_element() {

    // init z3 environment
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_model = true;
    smt::context ctx(m, params);
    seq_util m_util_s(m);
//    arith_util m_util_a(m);
//    smt::theory_str theo_str(m,params);

//    for (int i=0; i<1000; i++) {
//        std::cout << genRandName().encode() << std::endl;
//    }
    zstring zstr_a5 = "aaaaa";
    zstring zstr_b5 = "bbbbb";

    std::cout << "test element class..." << std::endl;
    app_ref expr_a5_const_ref(m_util_s.str.mk_string(zstr_a5),m);
    expr* expr_a5_const = expr_a5_const_ref.get();
    element elm_a5_const(element::t::CONST,zstr_a5,expr_a5_const);
    std::cout << "new string constant: " << elm_a5_const.value() << mk_pp(expr_a5_const,m) << ", id: " << expr_a5_const->get_id() << std::endl;
    ENSURE(elm_a5_const.type()==element::t::CONST)
    ENSURE(elm_a5_const.value()==zstr_a5)
    ENSURE(elm_a5_const.origin_expr().size()==1)
    ENSURE(elm_a5_const.origin_expr().front()==expr_a5_const)
    ENSURE(m_util_s.str.is_string(expr_a5_const))

    app_ref expr_a5_const_ref_2(m_util_s.str.mk_string(zstr_a5),m);
    expr* expr_a5_const_2 = expr_a5_const_ref.get();
    element elm_a5_const_2(element::t::CONST,zstr_a5,expr_a5_const);
    ENSURE(elm_a5_const==elm_a5_const_2)

    app_ref expr_b5_const_ref(m_util_s.str.mk_string(zstr_b5),m);
    expr* expr_b5_const = expr_b5_const_ref.get();
    element elm_b5_const(element::t::CONST,zstr_b5,expr_b5_const);
    ENSURE(elm_a5_const!=elm_b5_const)
    ENSURE(elm_a5_const<elm_b5_const)

    sort* string_sort = m_util_s.str.mk_string_sort();
    var_ref expr_b5_var_ref(m.mk_var(0,string_sort),m);
    var* expr_b5_var = expr_b5_var_ref.get();
    ENSURE(m.get_sort(expr_b5_var)==string_sort)
    element elm_b5_var(element::t::VAR,zstr_b5,expr_b5_var);
    std::cout << "new string variable: " << elm_b5_var.value() << mk_pp(expr_b5_var,m) << ", id: " << expr_b5_var->get_id() << std::endl;
    ENSURE(elm_b5_var.type()==element::t::VAR)
    ENSURE(elm_b5_var.value()==zstr_b5)
    ENSURE(elm_b5_var.origin_expr().size()==1)
    ENSURE(elm_b5_var.origin_expr().front()==expr_b5_var)
    std::cout << "shortname: " << elm_b5_var.shortname() << std::endl;
    ENSURE(elm_b5_var.shortname()=="V0")

    ENSURE(elm_a5_const<elm_b5_var)

//    std::cout << "-------1-------" << std::endl;
//    ctx.internalize(expr_b5_var,false);
//    ctx.get_enode(expr_b5_var);
//    smt::theory_var theory_var_b5_var = theo_str.mk_var(ctx.get_enode(expr_b5_var));
}


void tst_theory_str() {
    tst_element();
    fuzz_str();

//    tst_oaut_adaptor();
//    tst_zaut_adaptor();
//    tst_oaut();
//    tst_zaut_oaut_crosscheck();
}
