#ifndef _THEORY_STR_H_
#define _THEORY_STR_H_

#include <list>
#include <set>
#include <stack>
#include <map>
#include <vector>
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

namespace smt {

    enum class element_t {
        CONST, VAR, NONE
    };

    class element {
        element_t m_type;
        std::string m_value;
    public:
        static const element& null();
        element(const element_t& t, std::string v) : m_type{t}, m_value{std::move(v)} {}
        const element_t& type() const { return m_type; }
        const std::string& value() const { return m_value; }
        const bool operator==(const element& other) const;
        const bool operator<(const element& other) const;
        friend std::ostream& operator<<(std::ostream& os, const element& e);
    };

    class word_term {
        std::list<element> m_elements;
    public:
        static const word_term& null();
        static word_term of_string(const std::string& literal);
        static word_term of_variable(const std::string& name);
        static const bool prefix_mismatch_in_consts(const word_term& w1, const word_term& w2);
        static const bool suffix_mismatch_in_consts(const word_term& w1, const word_term& w2);
        static const bool unequalable_no_empty_var(const word_term& w1, const word_term& w2);
        static const bool unequalable(const word_term& w1, const word_term& w2);
        word_term() = default;
        word_term(const word_term& other);
        explicit word_term(std::list<element> v) : m_elements{std::move(v)} {}
        const std::size_t length() const { return m_elements.size(); };
        const std::list<element>& elements() const { return m_elements; };
        const std::set<element> variables() const;
        const bool has_constant() const;
        const bool check_front(const element_t& t) const;
        const element& peek_front() const;
        void remove_front();
        void concat(const word_term& other);
        void replace(const element& tgt, const word_term& subst);
        const bool operator==(const word_term& other) const;
        const bool operator<(const word_term& other) const;
        friend std::ostream& operator<<(std::ostream& os, const word_term& w);
    };

    class word_equation {
        word_term m_lhs;
        word_term m_rhs;
    public:
        word_equation(const word_term& lhs, const word_term& rhs);
        word_equation(const word_equation& other) = default;
        const word_term& lhs() const { return m_lhs; }
        const word_term& rhs() const { return m_rhs; }
        const std::set<element> variables() const;
        const element& definition_var() const;
        const word_term& definition_body() const;
        const bool is_simply_unsat(bool allow_empty_var = false) const;
        const bool is_in_definition_form() const;
        const bool check_heads(const element_t& lht, const element_t& rht) const;
        void trim_prefix();
        void replace(const element& tgt, const word_term& subst);
        const bool operator<(const word_equation& other) const;
        friend std::ostream& operator<<(std::ostream& os, const word_equation& we);
    };

    using def_node = element;
    using def_nodes = std::set<def_node>;
    using def_graph = std::map<element, def_nodes>;

    class state {
        std::set<word_equation> m_word_equations;
    public:
        state() = default;
        const std::set<element> variables() const;
        const std::vector<std::vector<word_term>> equivalence_classes() const;
        const bool is_simply_unsat() const;
        const bool is_in_definition_form() const;
        const bool is_in_solved_form() const;
        const bool detect_unsat_in_equivalence_classes() const;
        void add_word_equation(word_equation we);
        state replace(const element& tgt, const word_term& subst) const;
        const std::list<state> transform() const;
        const bool operator<(const state& other) const;
        friend std::ostream& operator<<(std::ostream& os, const state& s);
    private:
        static const bool dag_def_check_node(const def_graph& graph, const def_node& node,
                                             def_nodes& marked, def_nodes& checked);
        const bool definition_acyclic() const;
    };

    class neilson_based_solver {
        std::set<state> m_processed;
        std::stack<state> m_pending;
        bool m_solution_found;
    public:
        explicit neilson_based_solver(const state& root);
        const bool solution_found() const { return m_solution_found; }
        void consider_var_empty_cases();
        void check_sat();
    };

    using expr_pair = std::pair<expr_ref, expr_ref>;

    class theory_str : public theory {
        int m_scope_level;
        const theory_str_params& m_params;
        scoped_vector<expr_pair> m_we_expr_memo;
        scoped_vector<expr_pair> m_wine_expr_memo;
    public:
        theory_str(ast_manager& m, const theory_str_params& params);
        void display(std::ostream& os) const override;
    protected:
        void init(context *ctx) override;
        bool internalize_atom(app *atom, bool gate_ctx) override;
        bool internalize_term(app *term) override;
        theory_var mk_var(enode *n) override;
        theory *mk_fresh(context *) override { return alloc(theory_str, get_manager(), m_params); }
        model_value_proc *mk_value(enode *n, model_generator& mg) override;
        void add_theory_assumptions(expr_ref_vector& assumptions) override;
        lbool validate_unsat_core(expr_ref_vector& unsat_core) override;
        void new_eq_eh(theory_var, theory_var) override;
        void new_diseq_eh(theory_var, theory_var) override;
        void init_search_eh() override;
        void relevant_eh(app *n) override;
        void assign_eh(bool_var v, bool is_true) override;
        void push_scope_eh() override;
        void pop_scope_eh(unsigned num_scopes) override;
        void reset_eh() override;
        final_check_status final_check_eh() override;
        bool can_propagate() override;
        void propagate() override;
        void init_model(model_generator& m) override;
        void finalize_model(model_generator& mg) override;
    private:
        void assert_axiom(expr *e);
        void dump_assignments();
        const bool is_theory_str_term(expr *e) const;
        decl_kind get_decl_kind(expr *e) const;
        word_term get_word_term(expr *e) const;
        state build_state_from_memo() const;
        const bool block_dpllt_assignment_from_memo();
    };

};

#endif /* _THEORY_STR_H_ */
