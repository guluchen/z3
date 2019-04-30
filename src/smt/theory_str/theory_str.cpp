#include <algorithm>
#include <numeric>
#include <sstream>
#include "ast/ast_pp.h"
#include "ast/rewriter/bool_rewriter.h"
#include "smt/theory_str/theory_str.h"
#include "smt/smt_context.h"
#include "smt/smt_model_generator.h"
#include "smt/theory_lra.h"
#include "smt/theory_arith.h"
#include "smt/smt_context.h"
#include "ast/seq_decl_plugin.h"
#include "ast/reg_decl_plugins.h"


namespace smt {
    bool theory_str::is_main_branch=true;
    bool theory_str::is_over_approximation=false;

    namespace {
        bool IN_CHECK_FINAL = false;
    }

    theory_str::theory_str(ast_manager& m, const theory_str_params& params)
            : theory{m.mk_family_id("seq")}, m_params{params}, m_rewrite{m}, m_util_a{m},
              m_util_s{m} {}

    void theory_str::display(std::ostream& os) const {
        os << "theory_str display" << std::endl;
    }

    void theory_str::init(context *ctx) {
        theory::init(ctx);
        STRACE("str", if (!IN_CHECK_FINAL) tout << "init\n";);
    }

    void theory_str::add_theory_assumptions(expr_ref_vector& assumptions) {
        STRACE("str", if (!IN_CHECK_FINAL) tout << "add_theory_assumptions\n";);
    }

    theory_var theory_str::mk_var(enode *const n) {
        STRACE("str", tout << "mk_var: " << mk_pp(n->get_owner(), get_manager()) << '\n';);
        if (!is_string_sort(n->get_owner()) && !is_regex_sort(n->get_owner())) {
            return null_theory_var;
        }
        if (is_attached_to_var(n)) {
            const theory_var v = n->get_th_var(get_id());
            STRACE("str", tout << "already attached to theory_var #" << v << '\n';);
            return v;
        }

        context& ctx = get_context();
        const theory_var v = theory::mk_var(n);
        ctx.attach_th_var(n, this, v);
        ctx.mark_as_relevant(n);
        STRACE("str", tout << "new theory_var #" << v << '\n';);
        return v;
    }


    bool theory_str::internalize_atom(app *const atom, const bool gate_ctx) {
        (void) gate_ctx;
        STRACE("str", tout << "internalize_atom: gate_ctx is " << gate_ctx << ", "
                           << mk_pp(atom, get_manager()) << '\n';);
        context& ctx = get_context();
        if (ctx.b_internalized(atom)) {
            STRACE("str", tout << "done before\n";);
            return true;
        }
        return internalize_term(atom);
    }

    bool theory_str::internalize_term(app *const term) {
        ast_manager& m = get_manager();
        context& ctx = get_context();
        SASSERT(is_of_this_theory(term));
        if (ctx.e_internalized(term)) {
            enode *e = ctx.get_enode(term);
            mk_var(e);
            return true;
        }
        for (auto e : *term) {
            if (!ctx.e_internalized(e)) {
                ctx.internalize(e, false);
            }
            enode *n = ctx.get_enode(e);
            ctx.mark_as_relevant(n);
            mk_var(n);
        }
        if (m.is_bool(term)) {
            bool_var bv = ctx.mk_bool_var(term);
            ctx.set_var_theory(bv, get_id());
            ctx.mark_as_relevant(bv);
        }

        enode *e = nullptr;
        if (ctx.e_internalized(term)) {
            e = ctx.get_enode(term);
        } else {
            e = ctx.mk_enode(term, false, m.is_bool(term), true);
        }
        mk_var(e);
        return true;
    }

    void theory_str::print_ctx(context& ctx) {  // test_hlin
        std::cout << "~~~~~ print ctx start ~~~~~~~\n";
//        context& ctx = get_context();
        unsigned nFormulas = ctx.get_num_asserted_formulas();
        expr_ref_vector Literals(get_manager()), Assigns(get_manager());
        ctx.get_guessed_literals(Literals);
        ctx.get_assignments(Assigns);
        std::cout << "~~~~~~ from get_asserted_formulas ~~~~~~\n";
        for (unsigned i = 0; i < nFormulas; ++i) {
            expr * ex = ctx.get_asserted_formula(i);
            std::cout << mk_pp(ex,get_manager()) << " relevant? "<<ctx.is_relevant(ex)<<std::endl;
        }
        std::cout << "~~~~~~ from get_guessed_literals ~~~~~~\n";
        for (auto & e : Literals){
            std::cout << mk_pp(e,get_manager()) << " relevant? "<<ctx.is_relevant(e)<< std::endl;
        }
        std::cout << "~~~~~~ from get_assignments ~~~~~~\n";
        for (auto & e : Assigns){
//            print_ast(e);
            std::cout << mk_pp(e,get_manager()) << " relevant? "<<ctx.is_relevant(e) << std::endl;
        }
        std::cout << "~~~~~ print ctx end ~~~~~~~~~\n";
    }

    void theory_str::print_ast(expr *e) {  // test_hlin
        ast_manager m = get_manager();
        unsigned int id = e->get_id();
        ast_kind ast = e->get_kind();
        sort *e_sort = m.get_sort(e);
        sort *bool_sort = m.mk_bool_sort();
        sort *str_sort = m_util_s.str.mk_string_sort();
        std::cout << "#e.id = " << id << std::endl;
        std::cout << "#e.kind = " << get_ast_kind_name(ast) << std::endl;
        std::cout << std::boolalpha << "#is bool sort? " << (e_sort == bool_sort) << std::endl;
        std::cout << std::boolalpha << "#is string sort? " << (e_sort == str_sort) << std::endl;
        std::cout << std::boolalpha << "#is string term? " << m_util_s.str.is_string(e) << std::endl;
        std::cout << std::boolalpha << "#is_numeral? " << m_util_a.is_numeral(e) << std::endl;
        std::cout << std::boolalpha << "#is_to_int? " << m_util_a.is_to_int(e) << std::endl;
        std::cout << std::boolalpha << "#is_int_expr? " << m_util_a.is_int_expr(e) << std::endl;
        std::cout << std::boolalpha << "#is_le? " << m_util_a.is_le(e) << std::endl;
        std::cout << std::boolalpha << "#is_ge? " << m_util_a.is_ge(e) << std::endl;
    }


    void theory_str::init_search_eh() {
        STRACE("str", tout << __LINE__ << " enter " << __FUNCTION__ << std::endl;);
        context& ctx = get_context();
        unsigned nFormulas = ctx.get_num_asserted_formulas();
        for (unsigned i = 0; i < nFormulas; ++i) {
            expr * ex = ctx.get_asserted_formula(i);
                string_theory_propagation(ex);
        }
        STRACE("str", tout << __LINE__ << " leave " << __FUNCTION__ << std::endl;);

    }

    void theory_str::string_theory_propagation(expr * expr) {
        STRACE("str", tout << __LINE__ << " enter " << __FUNCTION__ << std::endl;);

        if(!propgated_string_theory.contains(expr)||true) {
            propgated_string_theory.insert(expr);
            ast_manager &m = get_manager();
            context &ctx = get_context();

            if (!ctx.e_internalized(expr)) {
                ctx.internalize(expr, false);
            }
            enode* n = ctx.get_enode(expr);
            ctx.mark_as_relevant(n);

            sort *expr_sort = m.get_sort(expr);
            sort *str_sort = m_util_s.str.mk_string_sort();

            if (expr_sort == str_sort) {

                enode *n = ctx.get_enode(expr);
                propagate_basic_string_axioms(n);
                if (is_app(expr) && m_util_s.str.is_concat(to_app(expr))) {
                    propagate_concat_axiom(n);
                }
            }
            // if expr is an application, recursively inspect all arguments
            if (is_app(expr)&&!m_util_s.str.is_length(expr)) {
                app *term = to_app(expr);
                unsigned num_args = term->get_num_args();
                for (unsigned i = 0; i < num_args; i++) {
                    string_theory_propagation(term->get_arg(i));
                }
            }
        }
        STRACE("str", tout << __LINE__ << " leave " << __FUNCTION__ << std::endl;);

    }

    void theory_str::propagate_concat_axiom(enode * cat) {
        STRACE("str", tout << __LINE__ << " enter " << __FUNCTION__ << std::endl;);

        bool on_screen=false;


        app * a_cat = cat->get_owner();
        SASSERT(m_util_s.str.is_concat(a_cat));
        ast_manager & m = get_manager();

        // build LHS
        expr_ref len_xy(m);
        len_xy = m_util_s.str.mk_length(a_cat);
        SASSERT(len_xy);

        // build RHS: start by extracting x and y from Concat(x, y)
        SASSERT(a_cat->get_num_args() == 2);
        app * a_x = to_app(a_cat->get_arg(0));
        app * a_y = to_app(a_cat->get_arg(1));
        expr_ref len_x(m);
        len_x = m_util_s.str.mk_length(a_x);
        SASSERT(len_x);

        expr_ref len_y(m);
        len_y = m_util_s.str.mk_length(a_y);
        SASSERT(len_y);

        // now build len_x + len_y
        expr_ref len_x_plus_len_y(m);
        len_x_plus_len_y = m_util_a.mk_add(len_x, len_y);
        SASSERT(len_x_plus_len_y);

        if(on_screen) std::cout<<"[Concat Axiom] "<<mk_pp(len_xy,m)<<" = "<<mk_pp(len_x,m)<<" + "<<mk_pp(len_y,m)<<std::endl;

        // finally assert equality between the two subexpressions
        app * eq = m.mk_eq(len_xy, len_x_plus_len_y);
        SASSERT(eq);
        add_axiom(eq);
        STRACE("str", tout << __LINE__ << " leave " << __FUNCTION__ << std::endl;);

    }

    void theory_str::propagate_basic_string_axioms(enode * str) {
        bool on_screen=false;

        context & ctx = get_context();
        ast_manager & m = get_manager();

        {
            sort * a_sort = m.get_sort(str->get_owner());
            sort * str_sort = m_util_s.str.mk_string_sort();
            if (a_sort != str_sort) {
                STRACE("str", tout << "WARNING: not setting up string axioms on non-string term " << mk_pp(str->get_owner(), m) << std::endl;);
                return;
            }
        }

        // TESTING: attempt to avoid a crash here when a variable goes out of scope
        if (str->get_iscope_lvl() > ctx.get_scope_level()) {
            STRACE("str", tout << "WARNING: skipping axiom setup on out-of-scope string term" << std::endl;);
            return;
        }

        // generate a stronger axiom for constant strings
        app * a_str = str->get_owner();

        if (m_util_s.str.is_string(a_str)) {
            if(on_screen) std::cout<<"[ConstStr Axiom] "<<mk_pp(a_str,m)<<std::endl;

            expr_ref len_str(m);
            len_str = m_util_s.str.mk_length(a_str);
            SASSERT(len_str);

            zstring strconst;
            m_util_s.str.is_string(str->get_owner(), strconst);
            unsigned int l = strconst.length();
            expr_ref len(m_util_a.mk_numeral(rational(l), true), m);

            literal lit(mk_eq(len_str, len, false));
            ctx.mark_as_relevant(lit);
            ctx.mk_th_axiom(get_id(), 1, &lit);
        } else {
            // build axiom 1: Length(a_str) >= 0
            {
                if(on_screen) std::cout<<"[Non-Zero Axiom] "<<mk_pp(a_str,m)<<std::endl;

                // build LHS
                expr_ref len_str(m);
                len_str = m_util_s.str.mk_length(a_str);
                SASSERT(len_str);
                // build RHS
                expr_ref zero(m);
                zero = m_util_a.mk_numeral(rational(0), true);
                SASSERT(zero);
                // build LHS >= RHS and assert
                app * lhs_ge_rhs = m_util_a.mk_ge(len_str, zero);
                SASSERT(lhs_ge_rhs);
                STRACE("str", tout << "string axiom 1: " << mk_ismt2_pp(lhs_ge_rhs, m) << std::endl;);
                add_axiom(lhs_ge_rhs);
            }

            // build axiom 2: Length(a_str) == 0 <=> a_str == ""
            {
                if(on_screen) std::cout<<"[Zero iff Empty Axiom] "<<mk_pp(a_str,m)<<std::endl;

                // build LHS of iff
                expr_ref len_str(m);
                len_str = m_util_s.str.mk_length(a_str);
                SASSERT(len_str);
                expr_ref zero(m);
                zero = m_util_a.mk_numeral(rational(0), true);
                SASSERT(zero);
                expr_ref lhs(m);
                lhs = ctx.mk_eq_atom(len_str, zero);
                SASSERT(lhs);
                // build RHS of iff
                expr_ref empty_str(m);
                empty_str = m_util_s.str.mk_string(symbol(""));
                SASSERT(empty_str);
                expr_ref rhs(m);
                rhs = ctx.mk_eq_atom(a_str, empty_str);
                SASSERT(rhs);
                // build LHS <=> RHS and assert
                literal l(mk_eq(lhs, rhs, true));
                ctx.mark_as_relevant(l);
                ctx.mk_th_axiom(get_id(), 1, &l);
            }

        }
    }

    void theory_str::relevant_eh(app *const n) {
        STRACE("str", tout << "relevant: " << mk_pp(n, get_manager()) << '\n';);


        if (m_util_s.str.is_extract(n)) {
            handle_substr(n);
        } else if (m_util_s.str.is_itos(n)) {
            //handle_itos(n);
        } else if (m_util_s.str.is_stoi(n)) {
            //handle_stoi(n);
        } else if (m_util_s.str.is_at(n)) {
            handle_char_at(n);
        } else if (m_util_s.str.is_replace(n)) {
            //handle_replace(n);
        } else if (m_util_s.str.is_index(n)) {
            handle_index_of(n);
        }

    }

    void theory_str::assign_eh(bool_var v, const bool is_true) {
        ast_manager& m = get_manager();
        STRACE("str", tout << "assign: bool_var #" << v << " is " << is_true << ", "
                           << mk_pp(get_context().bool_var2expr(v), m) << '\n';);
        context& ctx = get_context();
        expr *e = ctx.bool_var2expr(v);
        expr *e1 = nullptr, *e2 = nullptr;
        if (m_util_s.str.is_prefix(e, e1, e2)) {
            if (is_true) {
                handle_prefix(e);
            } else {
                TRACE("str", tout << "TODO: not prefix\n";);
                is_over_approximation=true;
            }
        } else if (m_util_s.str.is_suffix(e, e1, e2)) {
            if (is_true) {
                handle_suffix(e);
            } else {
                TRACE("str", tout << "TODO: not suffix\n";);
                is_over_approximation=true;
            }
        } else if (m_util_s.str.is_contains(e, e1, e2)) {
            if (is_true) {
                handle_contains(e);
            } else {
                TRACE("str", tout << "TODO: not contains " << mk_pp(e, m) << "\n";);
                is_over_approximation=true;
            }
        } else if (m_util_s.str.is_in_re(e)) {
            handle_in_re(e, is_true);
        } else {
            TRACE("str", tout << "unhandled literal " << mk_pp(e, m) << "\n";);
            UNREACHABLE();
        }
    }

    void theory_str::new_eq_eh(theory_var x, theory_var y) {
        m_word_eq_var_todo.push_back({x,y});
        ast_manager& m = get_manager();
        const expr_ref l{get_enode(x)->get_owner(), m};
        const expr_ref r{get_enode(y)->get_owner(), m};
        m_word_eq_todo.push_back({l, r});
        STRACE("str", tout << "new_eq: " << l << " = " << r << '\n';);
    }

    template <class T>
    static T* get_th_arith(context& ctx, theory_id afid, expr* e) {
        theory* th = ctx.get_theory(afid);
        if (th && ctx.e_internalized(e)) {
            return dynamic_cast<T*>(th);
        }
        else {
            return nullptr;
        }
    }

    void theory_str::new_diseq_eh(theory_var x, theory_var y) {
        m_word_diseq_var_todo.push_back({x,y});

        ast_manager& m = get_manager();
        const expr_ref l{get_enode(x)->get_owner(), m};
        const expr_ref r{get_enode(y)->get_owner(), m};

//        //add lower bound from solvers
//
//        context& ctx = get_context();
//        expr_ref el(m_util_s.str.mk_length(l), m);
//        expr_ref er(m_util_s.str.mk_length(r), m);
//        expr_ref _lo(m);
//        family_id afid = m_util_a.get_family_id();
//        for(const expr_ref& e :{el,er}) {
//            theory_mi_arith* tha = get_th_arith<theory_mi_arith>(ctx, afid, e);
//            if (tha && tha->get_lower(ctx.get_enode(e), _lo)) { std::cout << "low of "<< mk_pp(e,m) <<" = " << _lo<<std::endl;}
//            theory_i_arith* thi = get_th_arith<theory_i_arith>(ctx, afid, e);
//            if (thi && thi->get_lower(ctx.get_enode(e), _lo)) { std::cout << "low of "<< mk_pp(e,m) <<" = " << _lo<<std::endl;}
//            theory_lra* thr = get_th_arith<theory_lra>(ctx, afid, e);
//            if (thr && thr->get_lower(ctx.get_enode(e), _lo)) { std::cout << "low of "<< mk_pp(e,m) <<" = " << _lo<<std::endl;}
//        }
//
        m_word_diseq_todo.push_back({l, r});
        STRACE("str", tout << "new_diseq: " << l << " != " << r << '\n';);
    }

    bool theory_str::can_propagate() {
        return false;
    }

    void theory_str::propagate() {
        STRACE("str", if (!IN_CHECK_FINAL) tout << "propagate" << '\n';);
    }

    void theory_str::push_scope_eh() {
        m_scope_level += 1;
        m_word_eq_todo.push_scope();
        m_word_diseq_todo.push_scope();
        m_word_eq_var_todo.push_scope();
        m_word_diseq_var_todo.push_scope();
        m_membership_todo.push_scope();
        STRACE("str", if (!IN_CHECK_FINAL) tout << "push_scope: " << m_scope_level << '\n';);
    }

    void theory_str::pop_scope_eh(const unsigned num_scopes) {
        m_scope_level -= num_scopes;
        m_word_eq_todo.pop_scope(num_scopes);
        m_word_diseq_todo.pop_scope(num_scopes);
        m_word_eq_var_todo.pop_scope(num_scopes);
        m_word_diseq_var_todo.pop_scope(num_scopes);
        m_membership_todo.pop_scope(num_scopes);
        m_rewrite.reset();
        STRACE("str", if (!IN_CHECK_FINAL)
            tout << "pop_scope: " << num_scopes << " (back to level " << m_scope_level << ")\n";);
    }

    void theory_str::reset_eh() {
        STRACE("str", tout << "reset" << '\n';);
    }


    bool theory_str::mini_check_sat(expr *e) {  // test_hlin
        ast_manager m;
        reg_decl_plugins(m);
        seq_util su(m);
        arith_util au(m);
        smt_params params;
        params.m_model = true;
        smt::context ctx(m, params);
        expr * exp = au.mk_ge(au.mk_int(0), au.mk_add(au.mk_int(1), au.mk_int(2)));
        std::cout << "expr made:\n" << mk_pp(exp, m) << std::endl;
//        std::cout << "print ctx ... \n";
//        print_ctx(ctx);
//        std::cout << "print ctx2 ... \n";
//        sort * intSort = au.mk_int();
//        m.mk_var(0, intSort);
//        mk_literal(expr);
        print_ctx(ctx);
        str::zaut::symbol_solver csolver(m, params);
        lbool mini_chk_res = csolver.check_sat(exp);
        std::cout << std::boolalpha << "mini_chk_res = " << mini_chk_res << std::endl;
        return mini_chk_res;
    }

    bool theory_str::lenc_check_sat(expr *e) {
        std::cout << "~~~~~ lenc_check_sat start ~~~~~~~~~\n";  // test_hlin
        str::zaut::symbol_solver csolver(get_manager(), get_context().get_fparams());
        lbool chk_res = csolver.check_sat(e);
        STRACE("str", tout << std::boolalpha << "lenc_check_sat result = " << chk_res << std::endl;);
        std::cout << std::boolalpha << "lenc_check_sat result = " << chk_res << std::endl;
        std::cout << "~~~~~ lenc_check_sat end ~~~~~~~~~~~\n";  // test_hlin
        return chk_res;
    }

    bool theory_str::check_counter_system_lenc(smt::str::solver &solver) {
        using namespace str;
        counter_system cs = counter_system(solver);
        cs.print_counter_system();  // STRACE output
        cs.print_var_expr(get_manager());  // STRACE output

        STRACE("str", tout << "[ABSTRACTION INTERPRETATION]\n";);
        apron_counter_system ap_cs = apron_counter_system(cs);
        STRACE("str", tout << "apron_counter_system constructed..." << std::endl;);
        // ap_cs.print_apron_counter_system();  // standard output only (because of apron library)
        STRACE("str", tout << "apron_counter_system abstraction starting..." << std::endl;);
        ap_cs.run_abstraction();
        STRACE("str", tout << "apron_counter_system abstraction finished..." << std::endl;);
        // make length constraints from the result of abstraction interpretation
        STRACE("str", tout << "generating length constraints..." << std::endl;);
        ap_length_constraint lenc = ap_length_constraint(ap_cs.get_ap_manager(), &ap_cs.get_final_node().get_abs(),
                                                   ap_cs.get_var_expr());
        lenc.pretty_print(get_manager());
        if (!lenc.empty()) {
            expr *lenc_res = lenc.export_z3exp(m_util_a, m_util_s);
            std::cout << "length constraint from counter system:\n" << mk_pp(lenc_res, get_manager()) << std::endl;  // keep stdout for test
            STRACE("str", tout << "length constraint from counter system:\n" << mk_pp(lenc_res, get_manager()) << std::endl;);
            return lenc_check_sat(lenc_res);
//            add_axiom(lenc_res);
//            return true;
        }
        else {  // if generated no length constraint, return true(sat)
            return true;
        }
    }

    final_check_status theory_str::final_check_eh() {
        if(is_main_branch){
            main_branch=true;
            is_main_branch=false;
        }


        if(!main_branch) return FC_DONE;
        using namespace str;
        if (m_word_eq_todo.empty()) {
            if (is_over_approximation)
                return FC_GIVEUP;
            else
                return FC_DONE;
        }

        TRACE("str", tout << "final_check: level " << get_context().get_scope_level() << '\n';);
        IN_CHECK_FINAL = true;

        if (!m_aut_imp) m_aut_imp = std::make_shared<zaut_adaptor>(get_manager(), get_context());
        state&& root = mk_state_from_todo();
        STRACE("strg", tout << "[Abbreviation <=> Fullname]\n"<<element::abbreviation_to_fullname(););

        STRACE("strg", tout << "root original:\n" << root <<std::endl;);
//        root.remove_single_variable_word_term();
//        STRACE("str", tout << "root removed single var:\n" << root <<std::endl;);
        root.merge_elements();
        STRACE("strg", tout << "root merged:\n" << root <<std::endl;);


        if(root.word_eqs().size()==0){
            if (!is_over_approximation)
                return FC_GIVEUP;
            else
                return FC_DONE;
        }
        if (root.unsolvable_by_inference() ) {
        STRACE("str", tout << "proved unsolvable by inference\n";);
            block_curr_assignment();
            IN_CHECK_FINAL = false;
            return FC_CONTINUE;
        }
        solver solver{std::move(root), m_aut_imp};
        while(solver.unfinished()){
            solver.resume(get_manager(),get_context(),*this);
            std::list<smt::str::state> to_check=solver.get_last_leaf_states();
            for(auto& s:to_check){
               bool reachable =  s.is_reachable(get_manager(),get_context(),*this);
               if(reachable){
                   STRACE("str", tout << "Leaf node reachable: \n"<<s<<std::endl;);
                   if (!is_over_approximation)
                       return FC_DONE;
               }
            }
        }

        if (solver.check() == result::SAT) {
            counter_system cs = counter_system(solver);
            STRACE("str", tout << "graph size: #state=" << solver.get_graph().access_map().size() << '\n';);
            STRACE("str", tout << "root state quadratic? " << solver.get_root().get().quadratic() << '\n';);
            // stdout for test: print graph size then exit
            std::cout << "graph construction summary:\n";
            std::cout << "#states total = " << solver.get_graph().access_map().size() << '\n';
            std::cout << "root state quadratic? " << solver.get_root().get().quadratic() << '\n';
            std::cout << "is the proof graph a DAG? " << cs.is_dag() << '\n';

            bool cs_lenc_check_res = true;
            //check_counter_system_lenc(solver);

            TRACE("str", tout << "final_check ends\n";);

            if (cs_lenc_check_res) {
                IN_CHECK_FINAL = false;
                return FC_GIVEUP;
            }  // will leave this if block if lenc_check_sat returns false
        }
        block_curr_assignment();
        TRACE("str", tout << "final_check ends\n";);
        IN_CHECK_FINAL = false;
        return FC_CONTINUE;
    }

    model_value_proc *theory_str::mk_value(enode *const n, model_generator& mg) {
        ast_manager& m = get_manager();
        app *const tgt = n->get_owner();
        (void) m;
        STRACE("str", tout << "mk_value: sort is " << mk_pp(m.get_sort(tgt), m) << ", "
                           << mk_pp(tgt, m) << '\n';);
        return alloc(expr_wrapper_proc, tgt);
    }

    void theory_str::init_model(model_generator& mg) {
        STRACE("str", if (!IN_CHECK_FINAL) tout << "init_model\n";);
    }

    void theory_str::finalize_model(model_generator& mg) {
        STRACE("str", if (!IN_CHECK_FINAL) tout << "finalize_model\n";);
    }

    lbool theory_str::validate_unsat_core(expr_ref_vector& unsat_core) {
        return l_undef;
    }

    bool theory_str::is_of_this_theory(expr *const e) const {
        return is_app(e) && to_app(e)->get_family_id() == get_family_id();
    }

    bool theory_str::is_string_sort(expr *const e) const {
        return m_util_s.str.is_string_term(e);
    }

    bool theory_str::is_regex_sort(expr *const e) const {
        return m_util_s.is_re(e);
    }

    bool theory_str::is_const_fun(expr *const e) const {
        return is_app(e) && to_app(e)->get_decl()->get_arity() == 0;
    }

    expr_ref theory_str::mk_sub(expr *a, expr *b) {
        ast_manager& m = get_manager();

        expr_ref result(m_util_a.mk_sub(a, b), m);
        m_rewrite(result);
        return result;
    }

    expr_ref
    theory_str::mk_skolem(symbol const& name, expr *e1, expr *e2, expr *e3, expr *e4, sort *sort) {
        ast_manager& m = get_manager();
        expr *es[4] = {e1, e2, e3, e4};
        unsigned len = e4 ? 4 : (e3 ? 3 : (e2 ? 2 : 1));

        if (!sort) {
            sort = m.get_sort(e1);
        }
        app * a = m_util_s.mk_skolem(name, len, es, sort);

//        ctx.internalize(a, false);
//        mk_var(ctx.get_enode(a));
//        propagate_basic_string_axioms(ctx.get_enode(a));
//
//        enode* n = ctx.get_enode(a);
//
//        if (!is_attached_to_var(n)) {
//            const theory_var v = theory::mk_var(n);
//            ctx.attach_th_var(n, this, v);
//            ctx.mark_as_relevant(n);
//            STRACE("str", tout << "new theory_var #" << v << '\n';);
//        }

        return expr_ref(a,m);

    }

    literal theory_str::mk_literal(expr *const e) {
        ast_manager& m = get_manager();
        context& ctx = get_context();
        expr_ref ex{e, m};
        m_rewrite(ex);
        if (!ctx.e_internalized(ex)) {
            ctx.internalize(ex, false);
        }
        enode *const n = ctx.get_enode(ex);
        ctx.mark_as_relevant(n);
        return ctx.get_literal(ex);
    }

    bool_var theory_str::mk_bool_var(expr *const e) {
        ast_manager& m = get_manager();
        STRACE("str", tout << "mk_bool_var: " << mk_pp(e, m) << '\n';);
        if (!m.is_bool(e)) {
            return null_bool_var;
        }
        context& ctx = get_context();
        SASSERT(!ctx.b_internalized(e));
        const bool_var& bv = ctx.mk_bool_var(e);
        ctx.set_var_theory(bv, get_id());
        ctx.set_enode_flag(bv, true);
        return bv;
    }

    str::word_term theory_str::mk_word_term(expr *const e) const {
        using namespace str;
        zstring s;
        if (m_util_s.str.is_string(e, s)) {
            return word_term::from_string(s);
        }
        if (m_util_s.str.is_concat(e)) {
            word_term result;
            for (unsigned i = 0; i < to_app(e)->get_num_args(); i++) {
                result.concat(mk_word_term(to_app(e)->get_arg(i)));
            }
            return result;
        }
        std::stringstream ss;
        ss << mk_pp(e, get_manager());
        return word_term::from_variable({ss.str().data()}, e);
    }

    str::state theory_str::mk_state_from_todo() {
        using namespace str;
        state result{std::make_shared<str::basic_memberships>(m_aut_imp)};
        STRACE("str", tout << "[Build State]\nmembership todo:\n";);
        STRACE("str", if (m_membership_todo.empty()) tout << "--\n";);
        for (const auto& m : m_membership_todo) {
            SASSERT(is_const_fun(m.first));
            zstring name{to_app(m.first)->get_decl()->get_name().bare_str()};
            result.add_membership({element::t::VAR, name, m.first}, m.second);
            STRACE("str", tout << m.first << " is in " << m.second << '\n';);
        }
        STRACE("str", tout << "word equation todo:\n";);
        STRACE("str", if (m_word_eq_todo.empty()) tout << "--\n";);
        for (const auto& eq : m_word_eq_todo) {
            result.add_word_eq({mk_word_term(eq.first), mk_word_term(eq.second)});
            STRACE("str", tout << eq.first << " = " << eq.second << '\n';);
        }
        STRACE("str", tout << "word disequality todo:\n";);
        STRACE("str", if (m_word_diseq_todo.empty()) tout << "--\n";);
        for (const auto& diseq : m_word_diseq_todo) {
            result.add_word_diseq({mk_word_term(diseq.first), mk_word_term(diseq.second)});
            STRACE("str", tout << diseq.first << " != " << diseq.second << '\n';);
        }

        result.initialize_length_constraint(result.variables());
        result.remove_useless_diseq();
        result.initialize_model_map(result.variables());
        return result;
    }

    void theory_str::add_axiom(expr *const e) {

        STRACE("str", tout << __LINE__ << " enter " << __FUNCTION__ << std::endl;);


        if(!axiomatized_terms.contains(e)||false) {
            axiomatized_terms.insert(e);
            if (e == nullptr || get_manager().is_true(e)) return;
//        string_theory_propagation(e);
            context &ctx = get_context();
//        SASSERT(!ctx.b_internalized(e));
            if (!ctx.b_internalized(e)) {
                ctx.internalize(e, false);
            }
            ctx.internalize(e, false);
            literal l{ctx.get_literal(e)};
            ctx.mark_as_relevant(l);
            ctx.mk_th_axiom(get_id(), 1, &l);
            STRACE("str", ctx.display_literal_verbose(tout << "[Assert_e]\n", l) << '\n';);
        }
        STRACE("str", tout << __LINE__ << " leave " << __FUNCTION__ << std::endl;);
    }

    void theory_str::add_clause(std::initializer_list<literal> ls) {
        STRACE("str", tout << __LINE__ << " enter " << __FUNCTION__ << std::endl;);
        context& ctx = get_context();
        literal_vector lv;
        for (const auto& l : ls) {
            if (l != null_literal && l != false_literal) {
                ctx.mark_as_relevant(l);
                lv.push_back(l);
            }
        }
        ctx.mk_th_axiom(get_id(), lv.size(), lv.c_ptr());
        STRACE("str", ctx.display_literals_verbose(tout << "[Assert_c]\n", lv) << '\n';);
        STRACE("str", tout << __LINE__ << " leave " << __FUNCTION__ << std::endl;);
    }

    /*
      Note: this is copied and modified from theory_seq.cpp
      Let e = at(s, i)
        0 <= i < len(s)  ->  s = xey /\ len(x) = i /\ len(e) = 1
        i < 0 \/ i >= len(s)  ->  e = empty
    */
    void theory_str::handle_char_at(expr *e) {
        ast_manager& m = get_manager();
        expr *s = nullptr, *i = nullptr;
        VERIFY(m_util_s.str.is_at(e, s, i));
        expr_ref len_e(m_util_s.str.mk_length(e), m);
        expr_ref len_s(m_util_s.str.mk_length(s), m);
        expr_ref zero(m_util_a.mk_int(0), m);
        expr_ref one(m_util_a.mk_int(1), m);
        expr_ref x = mk_skolem(symbol("m_char_at_left"), s, i);
        expr_ref y = mk_skolem(symbol("m_char_at_right"), s, i);
        expr_ref xey(m_util_s.str.mk_concat(x, m_util_s.str.mk_concat(e, y)), m);
        string_theory_propagation(xey);

        expr_ref len_x(m_util_s.str.mk_length(x), m);
        expr_ref emp(m_util_s.str.mk_empty(m.get_sort(e)), m);

        literal i_ge_0 = mk_literal(m_util_a.mk_ge(i, zero));
        literal i_ge_len_s = mk_literal(m_util_a.mk_ge(mk_sub(i, m_util_s.str.mk_length(s)), zero));

        add_clause({~i_ge_0, i_ge_len_s, mk_eq(s, xey, false)});
        add_clause({~i_ge_0, i_ge_len_s, mk_eq(one, len_e, false)});
        add_clause({~i_ge_0, i_ge_len_s, mk_eq(i, len_x, false)});

        add_clause({i_ge_0, mk_eq(e, emp, false)});
        add_clause({~i_ge_len_s, mk_eq(e, emp, false)});
    }

    /*
      Note: this is copied and modified from theory_seq.cpp
      TBD: check semantics of extract, a.k.a, substr(s, i ,l)

      let e = extract(s, i, l)

      i is start index, l is length of substring starting at index.

      i < 0 => e = ""
      i >= |s| => e = ""
      l <= 0 => e = ""
      0 <= i < |s| & l > 0 => s = xey, |x| = i, |e| = min(l, |s|-i)

    this translates to:

      0 <= i <= |s| -> s = xey
      0 <= i <= |s| -> len(x) = i
      0 <= i <= |s| & 0 <= l <= |s| - i -> |e| = l
      0 <= i <= |s| & |s| < l + i  -> |e| = |s| - i
      i >= |s| => |e| = 0
      i < 0 => |e| = 0
      l <= 0 => |e| = 0

      It follows that:
      |e| = min(l, |s| - i) for 0 <= i < |s| and 0 < |l|
    */
    void theory_str::handle_substr(expr *e) {
        if(!axiomatized_terms.contains(e)||false) {
            axiomatized_terms.insert(e);

            ast_manager &m = get_manager();
            expr *s = nullptr, *i = nullptr, *l = nullptr;
            VERIFY(m_util_s.str.is_extract(e, s, i, l));

            expr_ref x(mk_skolem(symbol("m_substr_left"), s, i), m);
            expr_ref ls(m_util_s.str.mk_length(s), m);
            expr_ref lx(m_util_s.str.mk_length(x), m);
            expr_ref le(m_util_s.str.mk_length(e), m);
            expr_ref ls_minus_i_l(mk_sub(mk_sub(ls, i), l), m);
            expr_ref y(mk_skolem(symbol("m_substr_right"), s, ls_minus_i_l), m);
            expr_ref xe(m_util_s.str.mk_concat(x, e), m);
            expr_ref xey(m_util_s.str.mk_concat(x, e, y), m);

            string_theory_propagation(xe);
            string_theory_propagation(xey);

            expr_ref zero(m_util_a.mk_int(0), m);

            literal i_ge_0 = mk_literal(m_util_a.mk_ge(i, zero));
            literal ls_le_i = mk_literal(m_util_a.mk_le(mk_sub(i, ls), zero));
            literal li_ge_ls = mk_literal(m_util_a.mk_ge(ls_minus_i_l, zero));
            literal l_ge_zero = mk_literal(m_util_a.mk_ge(l, zero));
            literal ls_le_0 = mk_literal(m_util_a.mk_le(ls, zero));

            add_clause({~i_ge_0, ~ls_le_i, mk_eq(xey, s, false)});
            add_clause({~i_ge_0, ~ls_le_i, mk_eq(lx, i, false)});
            add_clause({~i_ge_0, ~ls_le_i, ~l_ge_zero, ~li_ge_ls, mk_eq(le, l, false)});
            add_clause({~i_ge_0, ~ls_le_i, li_ge_ls, mk_eq(le, mk_sub(ls, i), false)});
            add_clause({~i_ge_0, ~ls_le_i, l_ge_zero, mk_eq(le, zero, false)});
            add_clause({i_ge_0, mk_eq(le, zero, false)});
            add_clause({ls_le_i, mk_eq(le, zero, false)});
            add_clause({~ls_le_0, mk_eq(le, zero, false)});
        }
    }

    void theory_str::handle_index_of(expr *i) {
        if(!axiomatized_terms.contains(i)||false) {
            axiomatized_terms.insert(i);
            ast_manager &m = get_manager();
            expr *s = nullptr, *t = nullptr, *offset = nullptr;
            rational r;
            VERIFY(m_util_s.str.is_index(i, t, s) || m_util_s.str.is_index(i, t, s, offset));

            expr_ref minus_one(m_util_a.mk_int(-1), m);
            expr_ref zero(m_util_a.mk_int(0), m);

            expr_ref emp(m_util_s.str.mk_empty(m.get_sort(t)), m);

            literal cnt = mk_literal(m_util_s.str.mk_contains(t, s));
            literal i_eq_m1 = mk_eq(i, minus_one, false);
            literal i_eq_0 = mk_eq(i, zero, false);
            literal s_eq_empty = mk_eq(s, emp, false);
            literal t_eq_empty = mk_eq(t, emp, false);

            add_clause({cnt, i_eq_m1});
            add_clause({~t_eq_empty, s_eq_empty, i_eq_m1});

            if (!offset || (m_util_a.is_numeral(offset, r) && r.is_zero())) {
                expr_ref x = mk_skolem(symbol("m_indexof_left"), t, s);
                expr_ref y = mk_skolem(symbol("m_indexof_right"), t, s);
                expr_ref xsy(m_util_s.str.mk_concat(x, s, y), m);
                string_theory_propagation(xsy);

                // |s| = 0 => indexof(t,s,0) = 0
                // contains(t,s) & |s| != 0 => t = xsy & indexof(t,s,0) = |x|
                expr_ref lenx(m_util_s.str.mk_length(x), m);
                add_clause({~s_eq_empty, i_eq_0});
                add_clause({~cnt, s_eq_empty, mk_eq(t, xsy, false)});
                add_clause({~cnt, s_eq_empty, mk_eq(i, lenx, false)});
                add_clause({~cnt, mk_literal(m_util_a.mk_ge(i, zero))});
                TRACE("str", tout << "TODO: ignore tightest_prefix\n";);
                is_over_approximation=true;

                tightest_prefix(s, x);
            } else {
                expr_ref len_t(m_util_s.str.mk_length(t), m);
                literal offset_ge_len = mk_literal(m_util_a.mk_ge(mk_sub(offset, len_t), zero));
                literal offset_le_len = mk_literal(m_util_a.mk_le(mk_sub(offset, len_t), zero));
                literal i_eq_offset = mk_eq(i, offset, false);
                add_clause({~offset_ge_len, s_eq_empty, i_eq_m1});
                add_clause({offset_le_len, i_eq_m1});
                add_clause({~offset_ge_len, ~offset_le_len, ~s_eq_empty, i_eq_offset});

                expr_ref x = mk_skolem(symbol("m_indexof_left"), t, s, offset);
                expr_ref y = mk_skolem(symbol("m_indexof_right"), t, s, offset);
                expr_ref xy(m_util_s.str.mk_concat(x, y), m);
                string_theory_propagation(xy);

                expr_ref indexof0(m_util_s.str.mk_index(y, s, zero), m);
                expr_ref offset_p_indexof0(m_util_a.mk_add(offset, indexof0), m);
                literal offset_ge_0 = mk_literal(m_util_a.mk_ge(offset, zero));
                add_clause(
                        {~offset_ge_0, offset_ge_len, mk_eq(t, xy, false)});
                add_clause(
                        {~offset_ge_0, offset_ge_len, mk_eq(m_util_s.str.mk_length(x), offset, false)});
                add_clause({~offset_ge_0, offset_ge_len, ~mk_eq(indexof0, minus_one, false), i_eq_m1});
                add_clause({~offset_ge_0, offset_ge_len, ~mk_literal(m_util_a.mk_ge(indexof0, zero)),
                            mk_eq(offset_p_indexof0, i, false)});

                // offset < 0 => -1 = i
                add_clause({offset_ge_0, i_eq_m1});
            }
        }
    }

    void theory_str::tightest_prefix(expr* s, expr* x) {
//        ast_manager &m = get_manager();
//
//        expr_ref s1 = mk_first(s);
//        expr_ref c  = mk_last(s);
//        expr_ref s1c = m_util_s.str.mk_concat(s1, m_util_s.str.mk_unit(c));
//        expr_ref emp(m_util_s.str.mk_empty(m.get_sort(s)), m);
//        literal s_eq_emp = mk_eq_empty(s);
//        add_axiom(s_eq_emp, mk_eq(s, s1c, false));
//        add_axiom(s_eq_emp, ~mk_literal(m_util_s.str.mk_contains(m_util_s.str.mk_concat(x, s1), s)));
    }

    // e = prefix(x, y), check if x is a prefix of y
    void theory_str::handle_prefix(expr *e) {
        if(!axiomatized_terms.contains(e)||false) {
            axiomatized_terms.insert(e);

            ast_manager &m = get_manager();
            expr *x = nullptr, *y = nullptr;
            VERIFY(m_util_s.str.is_prefix(e, x, y));

            expr_ref s = mk_skolem(symbol("m_prefix_right"), x, y);
            expr_ref xs(m_util_s.str.mk_concat(x, s), m);
            string_theory_propagation(xs);
            literal not_e = mk_literal(mk_not({e, m}));
            add_clause({not_e, mk_eq(y, xs, false)});
        }
    }

    // e = suffix(x, y), check if x is a suffix of y
    void theory_str::handle_suffix(expr *e) {
        if(!axiomatized_terms.contains(e)||false) {
            axiomatized_terms.insert(e);
            ast_manager &m = get_manager();
            expr *x = nullptr, *y = nullptr;
            VERIFY(m_util_s.str.is_suffix(e, x, y));

            expr_ref p = mk_skolem(symbol("m_suffix_left"), x, y);
            expr_ref px(m_util_s.str.mk_concat(p, x), m);
            string_theory_propagation(px);
            literal not_e = mk_literal(mk_not({e, m}));
            add_clause({not_e, mk_eq(y, px, false)});
        }
    }
    // e = contains(x, y)
    void theory_str::handle_contains(expr *e) {
        if(!axiomatized_terms.contains(e)||false) {
            axiomatized_terms.insert(e);
            ast_manager &m = get_manager();
            expr *x = nullptr, *y = nullptr;
            VERIFY(m_util_s.str.is_contains(e, x, y));
            expr_ref p = mk_skolem(symbol("m_contains_left"), x, y);
            expr_ref s = mk_skolem(symbol("m_contains_right"), x, y);
            expr_ref pys(m_util_s.str.mk_concat(m_util_s.str.mk_concat(p, y), s), m);

            string_theory_propagation(pys);
//            expr_ref not_e(m.mk_not(e),m);
//            add_axiom(m.mk_or(not_e, m.mk_eq(y, pys)));
            literal not_e = mk_literal(mk_not({e, m}));
            add_clause({not_e, mk_eq(x, pys, false)});
        }

    }

    void theory_str::handle_in_re(expr *const e, const bool is_true) {
        expr *s = nullptr, *re = nullptr;
        VERIFY(m_util_s.str.is_in_re(e, s, re));
        ast_manager& m = get_manager();

        expr_ref tmp{e, m};
        m_rewrite(tmp);
        if ((m.is_false(tmp) && is_true) || (m.is_true(tmp) && !is_true)) {
            literal_vector lv;
            lv.push_back(is_true ? mk_literal(e) : ~mk_literal(e));
            set_conflict(lv);
            return;
        }
        expr_ref r{re, m};
        context& ctx = get_context();
        literal l = ctx.get_literal(e);
        if (!is_true) {
            r = m_util_s.re.mk_complement(re);
            l.neg();
        }
        m_membership_todo.push_back({{s, m}, r});
    }

    void theory_str::set_conflict(const literal_vector& lv) {
        context& ctx = get_context();
        const auto& js = ext_theory_conflict_justification{
                get_id(), ctx.get_region(), lv.size(), lv.c_ptr(), 0, nullptr, 0, nullptr};
        ctx.set_conflict(ctx.mk_justification(js));
        STRACE("str", ctx.display_literals_verbose(tout << "[Conflict]\n", lv) << '\n';);
    }

    void theory_str::block_curr_assignment() {
        STRACE("str", tout << __LINE__ << " enter " << __FUNCTION__ << std::endl;);

        bool on_screen=false;

        if(on_screen) std::cout<<"[block] ";
        for (const auto& we : m_word_eq_var_todo) {
            if(on_screen) std::cout<<"("<<we.first<<"="<<we.second<<")";
        }
        for (const auto& we : m_word_diseq_var_todo) {
            if(on_screen) std::cout<<"("<<we.first<<"!="<<we.second<<")";
        }
        if(on_screen) std::cout<<std::endl;

        ast_manager& m = get_manager();
        expr *refinement = nullptr;
        STRACE("str", tout << "[Refinement]\nformulas:\n";);
        for (const auto& we : m_word_eq_todo) {
//            expr *const e = m.mk_not(mk_eq_atom(we.first, we.second));
            expr *const e = m.mk_not(m.mk_eq(we.first, we.second));
            refinement = refinement == nullptr ? e : m.mk_or(refinement, e);
            STRACE("str", tout << we.first << " = " << we.second << '\n';);
        }
        for (const auto& wi : m_word_diseq_todo) {
//            expr *const e = mk_eq_atom(wi.first, wi.second);
            expr *const e = m.mk_eq(wi.first, wi.second);
            refinement = refinement == nullptr ? e : m.mk_or(refinement, e);
            STRACE("str", tout << wi.first << " != " << wi.second << '\n';);
        }
        if (refinement != nullptr) {
            add_axiom(refinement);
        }
        STRACE("str", tout << __LINE__ << " leave " << __FUNCTION__ << std::endl;);

    }

    void theory_str::dump_assignments() const {
        STRACE("str", \
                ast_manager& m = get_manager();
                context& ctx = get_context();
                std::cout << "dump all assignments:\n";
                expr_ref_vector assignments{m};
                ctx.get_assignments(assignments);
                for (expr *const e : assignments) {
                   // ctx.mark_as_relevant(e);
                    std::cout <<"**"<< mk_pp(e, m) << (ctx.is_relevant(e) ? "\n" : " (not relevant)\n");
                }
        );
    }

}
