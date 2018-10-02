/*++
  Module Name:

  theory_str.cpp

  Abstract:

  String Theory Plugin

  Author:

  Murphy Berzish and Yunhui Zheng

  Revision History:

  --*/
#include "ast/ast_smt2_pp.h"
#include "smt/smt_context.h"
#include "smt/theory_str.h"
#include "smt/smt_model_generator.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include<list>
#include<algorithm>
#include "smt/theory_seq_empty.h"
#include "smt/theory_arith.h"
#include "ast/ast_util.h"
#include "ast/rewriter/seq_rewriter.h"
#include "smt_kernel.h"

namespace smt {
    theory_str::theory_str(ast_manager & m, theory_str_params const & params):
    theory(m.mk_family_id("seq")),
    sLevel(0),
    m_params(params)
    {
    }

    theory_str::~theory_str() {

    }





    void theory_str::init(context * ctx) {
        theory::init(ctx);
    }

    bool theory_str::internalize_atom(app * atom, bool gate_ctx) {
        return internalize_term(atom);
    }

    bool theory_str::internalize_term(app * term) {
        context & ctx = get_context();
        ast_manager & m = get_manager();
        SASSERT(term->get_family_id() == get_family_id());

        TRACE("str", tout << "internalizing term: " << mk_ismt2_pp(term, get_manager()) << std::endl;);

        unsigned num_args = term->get_num_args();
        for (unsigned i = 0; i < num_args; ++i) {
            ctx.internalize(term->get_arg(i), false);
        }
        if (ctx.e_internalized(term)) {
            enode * e = ctx.get_enode(term);
            mk_var(e);
            return true;
        }
//        std::cout << "the term: " << mk_ismt2_pp(term, get_manager()) << " is bool? "<< m.is_bool(term) << std::endl;
        enode * e = ctx.mk_enode(term, false, m.is_bool(term), true);
        if (m.is_bool(term)) {
            bool_var bv = ctx.mk_bool_var(term);
            ctx.set_var_theory(bv, get_id());
            ctx.set_enode_flag(bv, true);
        }
        // make sure every argument is attached to a theory variable
        for (unsigned i = 0; i < num_args; ++i) {
            enode * arg = e->get_arg(i);
            theory_var v_arg = mk_var(arg);
            TRACE("str", tout << "arg has theory var #" << v_arg << std::endl;); (void)v_arg;
        }

        theory_var v = mk_var(e);
        TRACE("str", tout << "term has theory var #" << v << std::endl;);
        return true;
    }

    theory_var theory_str::mk_var(enode* n) {
        TRACE("str", tout << "mk_var for " << mk_pp(n->get_owner(), get_manager()) << std::endl;);
        ast_manager & m = get_manager();
        if (!(is_string_theory_term(n->get_owner()))) {
            return null_theory_var;
        }
        if (is_attached_to_var(n)) {
            TRACE("str", tout << "already attached to theory var v#" << n->get_th_var(get_id()) << std::endl;);
            return n->get_th_var(get_id());
        } else {
            theory_var v = theory::mk_var(n);
            TRACE("str", tout << "new theory var v#" << v << " find " << get_enode(v) << std::endl;);
            get_context().attach_th_var(n, this, v);
            get_context().mark_as_relevant(n);
            return v;
        }
    }

    bool theory_str::can_propagate() {
        return false;
    }

    void theory_str::propagate() {
        TRACE("str", tout << "propagating..." << std::endl;);
    }

    void theory_str::reset_eh() {
        TRACE("str", tout << "resetting" << std::endl;);
    }

    void theory_str::add_theory_assumptions(expr_ref_vector & assumptions) {
        TRACE("str", tout << "add overlap assumption for theory_str" << std::endl;);
    }

    lbool theory_str::validate_unsat_core(expr_ref_vector & unsat_core) {
        return l_undef;
    }

    void theory_str::init_search_eh() {

    }

    void theory_str::new_eq_eh(theory_var x, theory_var y) {


        ast_manager & m = get_manager();
        enode* n1 = get_enode(x);
        enode* n2 = get_enode(y);
        expr_ref e1(n1->get_owner(), m);
        expr_ref e2(n2->get_owner(), m);
        weq weq1(e1, e2);
//        std::cout << "new equality " << get_context().get_scope_level() << ": "<<
//        mk_ismt2_pp(get_enode(x)->get_owner(), get_manager()) << " = " <<
//        mk_ismt2_pp(get_enode(y)->get_owner(), get_manager()) << std::endl;

        m_eqs.push_back(weq1);
        TRACE("str", tout << "new eq: " << mk_ismt2_pp(get_enode(x)->get_owner(), get_manager()) << " = " <<
              mk_ismt2_pp(get_enode(y)->get_owner(), get_manager()) << std::endl;);
    }

    void theory_str::new_diseq_eh(theory_var x, theory_var y) {
        ast_manager & m = get_manager();
        enode* n1 = get_enode(x);
        enode* n2 = get_enode(y);
        expr_ref e1(n1->get_owner(), m);
        expr_ref e2(n2->get_owner(), m);
        weq weq1(e1, e2);
//        std::cout << "new disequality " << get_context().get_scope_level() << ": "<<
//                  mk_ismt2_pp(get_enode(x)->get_owner(), get_manager()) << " = " <<
//                  mk_ismt2_pp(get_enode(y)->get_owner(), get_manager()) << std::endl;

        m_nqs.push_back(weq1);
        TRACE("str", tout << "new diseq: " << mk_ismt2_pp(get_enode(x)->get_owner(), get_manager()) << " = " <<
                          mk_ismt2_pp(get_enode(y)->get_owner(), get_manager()) << std::endl;);
    }

    void theory_str::relevant_eh(app * n) {
        TRACE("str", tout << "relevant: " << mk_ismt2_pp(n, get_manager()) << std::endl;);
    }

    void theory_str::assign_eh(bool_var v, bool is_true) {
        std::cout << "assert: v" << v << " #" << get_context().bool_var2expr(v)->get_id() << " is_true: " << is_true << std::endl;

        TRACE("str", tout << "assert: v" << v << " #" << get_context().bool_var2expr(v)->get_id() << " is_true: " << is_true << std::endl;);
    }

    void theory_str::push_scope_eh() {
        sLevel += 1;
        m_eqs.push_scope();
        m_nqs.push_scope();
     //   std::cout<< "push to " << sLevel << std::endl;
        TRACE("str", tout << "push to " << sLevel << std::endl;);
    }

    void theory_str::pop_scope_eh(unsigned num_scopes) {
        sLevel -= num_scopes;
        m_eqs.pop_scope(num_scopes);
        m_nqs.pop_scope(num_scopes);

     //   std::cout<< "pop " << num_scopes << " to " << sLevel << std::endl;
        TRACE("str", tout << "pop " << num_scopes << " to " << sLevel << std::endl;);

    }

    final_check_status theory_str::final_check_eh() {
        context & ctx = get_context();
        ast_manager & m = get_manager();
        std::cout<< "level: " << get_context().get_scope_level() << "\n"<<std::endl;

        expr* toAssert=NULL;
        for (auto const& e : m_eqs) {
            expr* exp=m.mk_not(mk_eq_atom( e.ls(),e.rs()));
            if(toAssert==NULL){
                toAssert=exp;
            }else{
                toAssert = m.mk_or(toAssert, exp);
            }
            std::cout << e.ls() << " = " << e.rs() << " \n";
        }

        for (auto const& e : m_nqs) {
            expr* exp=mk_eq_atom( e.ls(),e.rs());
            if(toAssert==NULL){
                toAssert=exp;
            }else{
                toAssert = m.mk_or(toAssert, exp);
            }
            std::cout << e.ls() << " != " << e.rs() << " \n";
        }

        //std::cout<< "asserting " << mk_pp(toAssert, m) << std::endl;
        assert_axiom(toAssert);

        TRACE("str", tout << "final check" << std::endl;);
        TRACE_CODE(dump_assignments(););

        return FC_CONTINUE;
    }
    void theory_str::init_model(model_generator & mg) {
        TRACE("str", tout << "initializing model" << std::endl;);

    }

    model_value_proc * theory_str::mk_value(enode * n, model_generator & mg) {
        TRACE("str", tout << "mk_value for: " << mk_ismt2_pp(n->get_owner(), get_manager()) <<
                          " (sort " << mk_ismt2_pp(get_manager().get_sort(n->get_owner()), get_manager()) << ")" << std::endl;);
        ast_manager & m = get_manager();
        app_ref owner(m);
        owner = n->get_owner();

        // If the owner is not internalized, it doesn't have an enode associated.
        SASSERT(get_context().e_internalized(owner));

        return alloc(expr_wrapper_proc, owner);

    }

    void theory_str::finalize_model(model_generator & mg) {}
    void theory_str::display(std::ostream & out) const {
        out << "TODO: theory_str display" << std::endl;
    }






    /*=====================================
     *
     * Helper functions
     *
     *=====================================*/


    void theory_str::dump_assignments() {
        TRACE_CODE(
                ast_manager & m = get_manager();
                context & ctx = get_context();
                tout << "dumping all assignments:" << std::endl;
                expr_ref_vector assignments(m);
                ctx.get_assignments(assignments);
                for (expr_ref_vector::iterator i = assignments.begin(); i != assignments.end(); ++i) {
                    expr * ex = *i;
                    tout << mk_ismt2_pp(ex, m) << (ctx.is_relevant(ex) ? "" : " (NOT REL)") << std::endl;
                }
        );
    }

    void theory_str::assert_axiom(expr * _e) {
        if (_e == nullptr)
            return;

        if (get_manager().is_true(_e)) return;
        context & ctx = get_context();
        ast_manager& m = get_manager();
        TRACE("str", tout << "asserting " << mk_ismt2_pp(_e, m) << std::endl;);


        expr_ref e(_e, m);
        if (!ctx.b_internalized(e)) {
            ctx.internalize(e, false);
        }
        literal lit(ctx.get_literal(e));
        ctx.mark_as_relevant(lit);
        ctx.mk_th_axiom(get_id(), 1, &lit);


//        TRACE("str", tout << "done asserting " << mk_ismt2_pp(e, get_manager()) << std::endl;);

    }

    bool theory_str::is_string_theory_term(expr *e){
        ast_manager & m = get_manager();

        return (m.get_sort(e) == m.mk_sort(m.mk_family_id("seq"), _STRING_SORT, 0, nullptr));
    }

}; /* namespace smt */
