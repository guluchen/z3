#ifndef _THEORY_STR_H_
#define _THEORY_STR_H_

#include <functional>
#include <list>
#include <set>
#include <stack>
#include <map>
#include <queue>
#include <unordered_map>
#include <vector>
#include "ast/arith_decl_plugin.h"
#include "ast/seq_decl_plugin.h"
#include "smt/params/theory_str_params.h"
#include "smt/smt_theory.h"
#include "util/scoped_vector.h"
#include "ast/rewriter/th_rewriter.h"

namespace smt {

    namespace str {

        class element {
        public:
            enum class t {
                CONST, VAR, NONE
            };
            struct hash {
                std::size_t operator()(const element& e) const;
            };
            static const element& null();
        private:
            element::t m_type;
            zstring m_value;
        public:
            element(const element::t& t, const zstring& v) : m_type{t}, m_value{v} {}
            const element::t& type() const { return m_type; }
            const zstring& value() const { return m_value; }
            bool typed(const element::t& t) const { return m_type == t; }
            bool operator==(const element& other) const;
            bool operator!=(const element& other) const { return !(*this == other); }
            bool operator<(const element& other) const;
            explicit operator bool() const { return *this != null(); }
            friend std::ostream& operator<<(std::ostream& os, const element& e);
        };

        class word_term {
        public:
            struct hash {
                std::size_t operator()(const word_term& w) const;
            };
            static const word_term& null();
            static word_term from_string(const zstring& str);
            static word_term from_variable(const zstring& name);
            static bool prefix_const_mismatched(const word_term& w1, const word_term& w2);
            static bool suffix_const_mismatched(const word_term& w1, const word_term& w2);
            static bool unequalable_no_empty_var(const word_term& w1, const word_term& w2);
            static bool unequalable(const word_term& w1, const word_term& w2);
        private:
            std::list<element> m_elements;
        public:
            word_term() = default;
            word_term(std::initializer_list<element> list);
            std::size_t length() const { return m_elements.size(); }
            std::size_t constant_num() const;
            std::set<element> variables() const;
            const std::list<element>& content() const { return m_elements; }
            const element& head() const;
            bool empty() const { return m_elements.empty(); }
            bool has_constant() const;
            bool has_variable() const;
            bool check_head(const element::t& t) const;
            void remove_head();
            void concat(const word_term& other);
            void replace(const element& tgt, const word_term& subst);
            bool operator==(const word_term& other) const;
            bool operator!=(const word_term& other) const { return !(*this == other); }
            bool operator<(const word_term& other) const;
            explicit operator bool() const { return *this != null(); }
            friend std::ostream& operator<<(std::ostream& os, const word_term& w);
        };

        using head_pair = std::pair<element, element>;

        class word_equation {
        public:
            struct hash {
                std::size_t operator()(const word_equation& we) const;
            };
            static const word_equation& null();
        private:
            word_term m_lhs;
            word_term m_rhs;
        public:
            word_equation(const word_term& lhs, const word_term& rhs);
            head_pair heads() const { return {m_lhs.head(), m_rhs.head()}; }
            std::set<element> variables() const;
            const word_term& lhs() const { return m_lhs; }
            const word_term& rhs() const { return m_rhs; }
            const element& definition_var() const;
            const word_term& definition_body() const;
            bool empty() const { return m_lhs.empty() && m_rhs.empty(); }
            bool unsolvable(bool allow_empty_var = true) const;
            bool in_definition_form() const;
            bool check_heads(const element::t& lht, const element::t& rht) const;
            word_equation trim_prefix() const;
            word_equation replace(const element& tgt, const word_term& subst) const;
            word_equation remove(const element& tgt) const;
            word_equation remove_all(const std::set<element>& tgt) const;
            bool operator==(const word_equation& other) const;
            bool operator!=(const word_equation& other) const { return !(*this == other); }
            bool operator<(const word_equation& other) const;
            explicit operator bool() const { return *this != null(); }
            friend std::ostream& operator<<(std::ostream& os, const word_equation& we);
        private:
            void sort();
        };

        class regex {
        };

        class automaton {
        };

        class language {
        public:
            using pair = std::pair<language, language>;
            enum class t {
                RE, AUT
            };
            union v {
                regex re;
                automaton aut;
            };
            struct hash {
                std::size_t operator()(const language& l) const { return 0; };
            };
        private:
            language::t m_type;
            language::v m_value;
        public:
            language(const language::t& t, language::v&& v) : m_type{t}, m_value{std::move(v)} {}
            const language::t& type() const { return m_type; }
            const language::v& value() const { return m_value; }
            bool typed(const language::t& t) const { return m_type == t; }
            language complement() const { return {t::AUT, {}}; }
            language concat(const language& other) const { return {t::AUT, {}}; }
            language intersect(const language& other) const { return {t::AUT, {}}; }
            language remove_prefix(const element& e) const { return {t::AUT, {}}; }
            std::list<language::pair> split() const { return {}; }
            bool operator==(const language& other) const { return true; }
            bool operator!=(const language& other) const { return !(*this == other); }
        };

        class state {
        public:
            struct hash {
                std::size_t operator()(const state& s) const;
            };
        private:
            using def_node = element;
            using def_nodes = std::set<def_node>;
            using def_graph = std::map<def_node, def_nodes>;
            bool m_allow_empty_var = true;
            std::set<word_equation> m_wes_to_satisfy;
            std::set<word_equation> m_wes_to_fail;
            std::unordered_map<element, language, element::hash> m_lang_to_satisfy;
        public:
            state() = default;
            explicit state(const bool allow_empty_var) : m_allow_empty_var{allow_empty_var} {}
            std::size_t word_eq_num() const { return m_wes_to_satisfy.size(); }
            std::set<element> variables() const;
            std::vector<std::vector<word_term>> eq_classes() const;
            const word_equation& smallest_eq() const;
            const word_equation& only_one_eq_left() const;
            bool allows_empty_var() const { return m_allow_empty_var; }
            bool in_definition_form() const;
            bool in_solved_form() const;
            bool eq_classes_inconsistent() const;
            bool diseq_inconsistent() const;
            bool unsolvable_by_check() const;
            bool unsolvable_by_inference() const;
            void allow_empty_var(const bool enable) { m_allow_empty_var = enable; }
            void add_word_eq(const word_equation& we);
            void add_word_diseq(const word_equation& we);
            state replace(const element& tgt, const word_term& subst) const;
            state remove(const element& tgt) const;
            state remove_all(const std::set<element>& tgt) const;
            bool operator==(const state& other) const;
            bool operator!=(const state& other) const { return !(*this == other); }
            bool operator<(const state& other) const;
            friend std::ostream& operator<<(std::ostream& os, const state& s);
        private:
            static bool dag_def_check_node(const def_graph& graph, const def_node& node,
                                           def_nodes& marked, def_nodes& checked);
            bool definition_acyclic() const;
        };

        using state_cref = std::reference_wrapper<const state>;

        enum class result {
            SAT, UNSAT, UNKNOWN
        };

        class neilsen_transforms {
        public:
            struct move {
                enum class t {
                    TO_EMPTY,
                    TO_CONST,
                    TO_VAR,
                    TO_VAR_VAR,
                    TO_CHAR_VAR,
                };
                const state_cref m_from;
                const move::t m_type;
                const std::vector<element> m_record;
                move add_record(const element& e) const;
            };
            using action = std::pair<move, state>;
            class mk_move {
                const state& m_state;
                const word_equation& m_src;
            public:
                mk_move(const state& s, const word_equation& src);
                std::list<action> operator()();
            private:
                bool src_vars_empty();
                bool src_var_is_const();
                action prop_empty();
                action prop_const();
                std::list<action> handle_two_var();
                std::list<action> handle_one_var();
            };
            class record_graph {
                std::unordered_map<state, std::list<move>, state::hash> m_backward_def;
            public:
                bool contains(const state& s) const;
                const std::list<move>& incoming_moves(const state& s) const;
                void add_move(move&& m, const state& s);
                const state& add_state(state&& s);
            };
        private:
            result m_status = result::UNKNOWN;
            record_graph m_records;
            std::stack<state_cref> m_pending;
        public:
            explicit neilsen_transforms(state&& root);
            bool in_status(const result& t) const { return m_status == t; };
            bool should_explore_all() const;
            result check(bool split_var_empty_ahead = false);
        private:
            result split_var_empty_cases();
            std::queue<state_cref> split_first_level_var_empty();
            std::list<action> transform(const state& s) const;
        };

        using expr_pair = std::pair<expr_ref, expr_ref>;

    }

    class theory_str : public theory {
        int m_scope_level = 0;
        const theory_str_params& m_params;
        arith_util m_util_a;
        seq_util m_util_s;
        int m_fresh_id;
        th_rewriter m_rewrite;

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
        void assert_axiom(literal l1, literal l2 = null_literal, literal l3 = null_literal,
                          literal l4 = null_literal, literal l5 = null_literal);
        void add_extract_axiom(expr *e);
        void add_contains_axiom(expr *e);
        void dump_assignments() const;
        bool is_theory_str_term(expr *e) const;
        bool is_word_term(expr *e) const;
        app *mk_str_var(std::string name);
        literal mk_literal(expr *e);
        str::word_term mk_word_term(expr *e) const;
        str::state mk_state_from_todo() const;
        bool block_curr_assignment();
    };

}

#endif /* _THEORY_STR_H_ */
