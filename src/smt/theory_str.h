/*++
  Module Name:

  theory_str.h

  Abstract:

  String Theory Plugin

  Author:

  Murphy Berzish and Yunhui Zheng

  Revision History:

  --*/
#ifndef _THEORY_STR_H_
#define _THEORY_STR_H_

#include "util/trail.h"
#include "util/union_find.h"
#include "util/scoped_vector.h"
#include "util/scoped_ptr_vector.h"
#include "util/hashtable.h"
#include "ast/ast_pp.h"
#include "ast/arith_decl_plugin.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/seq_decl_plugin.h"
#include "smt/smt_theory.h"
#include "smt/params/theory_str_params.h"
#include "smt/proto_model/value_factory.h"
#include "smt/smt_model_generator.h"
#include<set>
#include<stack>
#include<vector>
#include<map>

namespace smt {

// Asserted or derived equality
class weq {
    expr_ref  m_lhs;
    expr_ref  m_rhs;
public:

    weq(expr_ref& l, expr_ref& r):
            m_lhs(l), m_rhs(r){}
    weq(weq const& other): m_lhs(other.m_lhs), m_rhs(other.m_rhs) {}
    expr_ref const& ls() const { return m_lhs; }
    expr_ref const& rs() const { return m_rhs; }
};


class theory_str : public theory {
public:
    theory_str(ast_manager & m, theory_str_params const & params);
    ~theory_str() override;
    void display(std::ostream & out) const override;

    //used in union_find<theory_str>
//    trail_stack<theory_str> m_trail_stack;
//    trail_stack<theory_str>& get_trail_stack() { return m_trail_stack; }


protected:
//    union_find<theory_str> m_find;
    int sLevel;
    theory_str_params const & m_params;
    scoped_vector<weq>          m_eqs;        // set of current equations.
    scoped_vector<weq>          m_nqs;        // set of current disequalities.
    void assert_axiom(expr * e);



    bool internalize_atom(app * atom, bool gate_ctx) override;
    bool internalize_term(app * term) override;
    theory_var mk_var(enode * n) override;
    void new_eq_eh(theory_var, theory_var) override;
    void new_diseq_eh(theory_var, theory_var) override;

    theory* mk_fresh(context*) override { return alloc(theory_str, get_manager(), m_params);}
    void init(context * ctx) override;
    void init_search_eh() override;
    void add_theory_assumptions(expr_ref_vector & assumptions) override;
    lbool validate_unsat_core(expr_ref_vector & unsat_core) override;
    void relevant_eh(app * n) override;
    void assign_eh(bool_var v, bool is_true) override;
    void push_scope_eh() override;
    void pop_scope_eh(unsigned num_scopes) override;
    void reset_eh() override;

    bool can_propagate() override;
    void propagate() override;
    final_check_status final_check_eh() override;

    void init_model(model_generator & m) override;
    model_value_proc * mk_value(enode * n, model_generator & mg) override;
    void finalize_model(model_generator & mg) override;
    void dump_assignments();
private:
    bool is_string_theory_term(expr *);
    expr* mk_not_and_remove_double_negation(expr *);

};


};

#endif /* _THEORY_STR_H_ */
