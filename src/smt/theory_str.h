#ifndef _THEORY_STR_H_
#define _THEORY_STR_H_

#include <list>
#include <set>
#include <stack>
#include <map>
#include <vector>
#include "ast/arith_decl_plugin.h"
#include "ast/seq_decl_plugin.h"
#include "smt/params/theory_str_params.h"
#include "smt/smt_theory.h"
#include "util/scoped_vector.h"

namespace smt {

    namespace str {

        class element {
        public:
            enum class t {
                CONST, VAR, NONE
            };
            static const element& null();
        private:
            element::t m_type;
            zstring m_value;
        public:
            element(const element::t& t, const zstring& v) : m_type{t}, m_value{v} {}
            const element::t& type() const { return m_type; }
            const zstring& value() const { return m_value; }
            const bool typed(const element::t& t) const { return m_type == t; }
            explicit operator bool() const { return *this != null(); }
            const bool operator==(const element& other) const;
            const bool operator!=(const element& other) const { return !(*this == other); }
            const bool operator<(const element& other) const;
            friend std::ostream& operator<<(std::ostream& os, const element& e);
        };

        class word_term {
        public:
            static const word_term& null();
            static word_term from_string(const zstring& str);
            static word_term from_variable(const zstring& name);
            static const bool prefix_const_mismatched(const word_term& w1, const word_term& w2);
            static const bool suffix_const_mismatched(const word_term& w1, const word_term& w2);
            static const bool unequalable_no_empty_var(const word_term& w1, const word_term& w2);
            static const bool unequalable(const word_term& w1, const word_term& w2);
        private:
            std::list<element> m_elements;
        public:
            word_term() = default;
            word_term(std::initializer_list<element> list);
            const std::size_t length() const { return m_elements.size(); }
            const std::size_t constant_count() const;
            const element& head() const;
            const std::set<element> variables() const;
            const bool empty() const { return m_elements.empty(); }
            const bool has_constant() const;
            const bool has_variable() const;
            const bool check_head(const element::t& t) const;
            void remove_head();
            void concat(const word_term& other);
            void replace(const element& tgt, const word_term& subst);
            explicit operator bool() const { return *this != null(); }
            const bool operator==(const word_term& other) const;
            const bool operator!=(const word_term& other) const { return !(*this == other); }
            const bool operator<(const word_term& other) const;
            friend std::ostream& operator<<(std::ostream& os, const word_term& w);
        };

        using head_pair = std::pair<const element&, const element&>;

        class word_equation {
        public:
            static const word_equation& null();
        private:
            word_term m_lhs;
            word_term m_rhs;
        public:
            word_equation(const word_term& lhs, const word_term& rhs);
            const word_term& lhs() const { return m_lhs; }
            const word_term& rhs() const { return m_rhs; }
            const head_pair heads() const { return {m_lhs.head(), m_rhs.head()}; }
            const std::set<element> variables() const;
            const element& definition_var() const;
            const word_term& definition_body() const;
            const bool empty() const { return m_lhs.empty() && m_rhs.empty(); }
            const bool unsolvable(bool allow_empty_var = true) const;
            const bool in_definition_form() const;
            const bool check_heads(const element::t& lht, const element::t& rht) const;
            word_equation trim_prefix() const;
            word_equation replace(const element& tgt, const word_term& subst) const;
            word_equation remove(const element& tgt) const;
            word_equation remove_all(const std::set<element>& tgt) const;
            explicit operator bool() const { return *this != null(); }
            const bool operator==(const word_equation& other) const;
            const bool operator!=(const word_equation& other) const { return !(*this == other); }
            const bool operator<(const word_equation& other) const;
            friend std::ostream& operator<<(std::ostream& os, const word_equation& we);
        private:
            void sort();
        };

        class state {
            using def_node = element;
            using def_nodes = std::set<def_node>;
            using def_graph = std::map<def_node, def_nodes>;
            using trans_source = std::pair<const word_equation&, const word_equation&>;
            bool m_allow_empty_var = true;
            std::set<word_equation> m_wes_to_satisfy;
            std::set<word_equation> m_wes_to_fail;
        public:
            state() = default;
            explicit state(const bool allow_empty_var) : m_allow_empty_var{allow_empty_var} {}
            const std::set<element> variables() const;
            const word_equation& only_one_eq_left() const;
            const std::vector<std::vector<word_term>> eq_classes() const;
            const bool eq_classes_inconsistent() const;
            const bool diseq_inconsistent() const;
            const bool unsolvable_by_check() const;
            const bool unsolvable_by_inference() const;
            const bool in_definition_form() const;
            const bool in_solved_form() const;
            void allow_empty_var(const bool enable) { m_allow_empty_var = enable; }
            void should_satisfy(const word_equation& we);
            void should_fail(const word_equation& we);
            state replace(const element& tgt, const word_term& subst) const;
            state remove(const element& tgt) const;
            state remove_all(const std::set<element>& tgt) const;
            const std::list<state> transform() const;
            const bool operator<(const state& other) const;
            friend std::ostream& operator<<(std::ostream& os, const state& s);
        private:
            static const bool dag_def_check_node(const def_graph& graph, const def_node& node,
                                                 def_nodes& marked, def_nodes& checked);
            const bool definition_acyclic() const;
            const trans_source transformation_source() const;
            void transform_one_var(const head_pair& hh, std::list<state>& result) const;
            void transform_two_var(const head_pair& hh, std::list<state>& result) const;
        };

        class neilson_based_solver {
            std::set<state> m_processed;
            std::stack<state> m_pending;
            bool m_solution_found;
        public:
            explicit neilson_based_solver(const state& root);
            const bool solution_found() const { return m_solution_found; }
            void explore_var_empty_cases();
            void check_sat();
        };

        using expr_pair = std::pair<expr_ref, expr_ref>;

    }

    class theory_str : public theory {
        int m_scope_level = 0;
        const theory_str_params& m_params;
        const arith_util m_util_a;
        const seq_util m_util_s;
        scoped_vector<str::expr_pair> m_word_eq_todo;
        scoped_vector<str::expr_pair> m_word_diseq_todo;
    public:
        theory_str(ast_manager& m, const theory_str_params& params);
        void display(std::ostream& os) const override;
    protected:
        theory *mk_fresh(context *) override { return alloc(theory_str, get_manager(), m_params); }
        void init(context *ctx) override;
        void add_theory_assumptions(expr_ref_vector& assumptions) override;
        theory_var mk_var(enode *n) override;
        bool internalize_atom(app *atom, bool gate_ctx) override;
        bool internalize_term(app *term) override;
        void init_search_eh() override;
        void relevant_eh(app *n) override;
        void assign_eh(bool_var v, bool is_true) override;
        void new_eq_eh(theory_var, theory_var) override;
        void new_diseq_eh(theory_var, theory_var) override;
        bool can_propagate() override;
        void propagate() override;
        void push_scope_eh() override;
        void pop_scope_eh(unsigned num_scopes) override;
        void reset_eh() override;
        final_check_status final_check_eh() override;
        model_value_proc *mk_value(enode *n, model_generator& mg) override;
        void init_model(model_generator& m) override;
        void finalize_model(model_generator& mg) override;
        lbool validate_unsat_core(expr_ref_vector& unsat_core) override;
    private:
        void assert_axiom(expr *e);
        void dump_assignments();
        const bool is_theory_str_term(expr *e) const;
        str::word_term mk_word_term(expr *e) const;
        str::state mk_state_from_todo() const;
        const bool block_curr_assignment();
    };

}

#endif /* _THEORY_STR_H_ */
