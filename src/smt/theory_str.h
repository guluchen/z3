#ifndef _THEORY_STR_H_
#define _THEORY_STR_H_

#include <functional>
#include <list>
#include <set>
#include <stack>
#include <map>
#include <memory>
#include <queue>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include "ast/arith_decl_plugin.h"
#include "ast/seq_decl_plugin.h"
#include "smt/params/theory_str_params.h"
#include "smt/smt_kernel.h"
#include "smt/smt_theory.h"
#include "util/scoped_vector.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/th_rewriter.h"
#include <gmp.h>
extern "C" {
#include "ap_global0.h"
#include "ap_global1.h"
#include "box.h"
#include "oct.h"
#include "pk.h"
#include "pkeq.h"
#include "ap_ppl.h"
};
namespace smt {

    namespace str {

        class element {
        public:
            using pair = std::pair<element, element>;
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
            element::pair heads() const { return {m_lhs.head(), m_rhs.head()}; }
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
        public:
            using ptr = std::unique_ptr<automaton>;
            using sptr = std::shared_ptr<automaton>;
            using sptr_pair = std::pair<sptr, sptr>;
            using state = unsigned;
            using len_offset = unsigned;
            using len_period = unsigned;
            using len_constraint = std::pair<len_offset, len_period>;
        public:
            virtual ~automaton() = 0;
            virtual bool is_empty() = 0;
            virtual bool is_deterministic() = 0;
            virtual bool is_final(state s) { return get_finals().find(s) != get_finals().end(); };
            virtual state get_init() = 0;
            virtual std::set<state> get_finals() = 0;
            virtual ptr clone() = 0;
            virtual sptr simplify() = 0;
            virtual sptr determinize() = 0;
            virtual ptr intersect_with(sptr other) = 0;
            virtual ptr union_with(sptr other) = 0;
            virtual std::list<ptr> remove_prefix(const zstring& prefix);
            virtual std::list<sptr_pair> split();
            virtual sptr set_init(state s) = 0;
            virtual sptr add_final(state s) = 0;
            virtual sptr remove_final(state s) = 0;
            virtual std::set<state> reachable_states() { return reachable_states(get_init()); };
            virtual std::set<state> reachable_states(state s) = 0;
            virtual std::set<state> successors(state s) = 0;
            virtual std::set<state> successors(state s, const zstring& str) = 0;
            virtual std::set<len_constraint> length_constraints() = 0;
            virtual std::ostream& display(std::ostream& os) = 0;
            virtual bool operator==(sptr other) = 0;
            virtual bool operator!=(sptr other) { return !(*this == std::move(other)); }
        };

        class zaut : public automaton {
        public:
            using internal = ::automaton<sym_expr, sym_expr_manager>;
            using symbol = sym_expr;
            using symbol_ref = obj_ref<sym_expr, sym_expr_manager>;
            using symbol_manager = sym_expr_manager;
            class symbol_boolean_algebra : public boolean_algebra<sym_expr *> {
            public:
                using expr = sym_expr *;
                struct displayer {
                    std::ostream& display(std::ostream& os, expr e) const { return e->display(os); }
                };
            private:
                ast_manager& m_ast_man;
                expr_solver& m_solver;
            public:
                symbol_boolean_algebra(ast_manager& m, expr_solver& s);
                expr mk_true() override;
                expr mk_false() override;
                expr mk_and(expr e1, expr e2) override;
                expr mk_and(unsigned size, const expr *es) override;
                expr mk_or(expr e1, expr e2) override;
                expr mk_or(unsigned size, const expr *es) override;
                expr mk_not(expr e) override;
                lbool is_sat(expr e) override;
            };
            class symbol_solver : public expr_solver {
                kernel m_kernel;
            public:
                symbol_solver(ast_manager& m, smt_params& p) : m_kernel{m, p} {}
                lbool check_sat(expr *e) override;
            };
            using moves = internal::moves;
            using maker = re2automaton;
            using handler = symbolic_automata<sym_expr, sym_expr_manager>;
        private:
            internal *m_imp;
            symbol_manager& m_sym_man;
            symbol_boolean_algebra& m_sym_ba;
            handler& m_handler;
        public:
            zaut(internal *a, symbol_manager& s, symbol_boolean_algebra& ba, handler& h);
            ~zaut() override { dealloc(m_imp); };
            bool is_empty() override { return m_imp->is_empty(); }
            bool is_deterministic() override;
            state get_init() override { return m_imp->init(); }
            std::set<state> get_finals() override;
            ptr clone() override;
            sptr simplify() override { return std::shared_ptr<zaut>(this); }
            sptr determinize() override;
            ptr intersect_with(sptr other) override;
            ptr union_with(sptr other) override;
            std::list<ptr> remove_prefix(const zstring& prefix) override;
            std::list<sptr_pair> split() override;
            sptr set_init(state s) override;
            sptr add_final(state s) override;
            sptr remove_final(state s) override;
            std::set<state> reachable_states(state s) override;
            std::set<state> successors(state s) override;
            std::set<state> successors(state s, const zstring& str) override;
            std::set<len_constraint> length_constraints() override;
            std::ostream& display(std::ostream& out) override;
            bool operator==(sptr other) override;
        private:
            bool contains(const zaut& other) const;
            ptr mk_ptr(internal *&& a) const;
            moves transitions_skeleton();
        };

        class zaut_adaptor {
            zaut::symbol_manager m_sym_man;
            zaut::symbol_solver *m_sym_solver;
            zaut::symbol_boolean_algebra *m_sym_ba;
            zaut::handler *m_aut_man;
            zaut::maker m_aut_make;
            std::map<expr *, zaut::sptr> m_re_aut_cache;
        public:
            zaut_adaptor(ast_manager& m, context& ctx);
            ~zaut_adaptor();
            automaton::sptr mk_from_re_expr(expr *re);
        };

        class language {
        public:
            using pair = std::pair<language, language>;
            enum class t {
                RE, AUT
            };
            union v {
                regex re;
                automaton::sptr aut;
                v() : aut{} {}
                ~v() {}
            };
            struct hash {
                std::size_t operator()(const language& l) const { return 0; };
            };
        private:
            language::t m_type;
            language::v m_value;
        public:
            explicit language(automaton::sptr a) : m_type{t::AUT} { m_value.aut = std::move(a); }
            language(const language& other);
            language(language&& other) noexcept;
            ~language();
            const language::t& type() const { return m_type; }
            const language::v& value() const { return m_value; }
            bool typed(const language::t& t) const { return m_type == t; }
            language intersect(const language& other) const;
            language remove_prefix(const element& e) const;
            bool operator==(const language& other) const { return true; };
            bool operator!=(const language& other) const { return !(*this == other); }
        };

        class state {
        public:
            using cref = std::reference_wrapper<const state>;
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
                const state::cref m_from;
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
                const std::unordered_map<state,std::list<move>,state::hash>& access_map() const {return m_backward_def;}
            };
        private:
            result m_status = result::UNKNOWN;
            record_graph m_records;
            state::cref m_rec_root;
            std::list<state::cref> m_rec_success_leaves;
            std::stack<state::cref> m_pending;
        public:
            explicit neilsen_transforms(state&& root);
            bool in_status(const result& t) const { return m_status == t; };
            bool should_explore_all() const;
            result check(bool split_var_empty_ahead = false);
            const record_graph& get_graph() const { return m_records; };
            const std::list<state::cref>& get_success_leaves() const { return m_rec_success_leaves; };
            const state::cref get_root() const { return m_rec_root; };
        private:
            bool finish_after_found(const state& s);
            result split_var_empty_cases();
            std::queue<state::cref> split_first_level_var_empty();
            std::list<action> transform(const state& s) const;
        };

        using expr_pair = std::pair<expr_ref, expr_ref>;

        class counter_system {
        public:
            // constructor
            counter_system(const neilsen_transforms& solver);
            // type defines
            enum class assign_type {
                CONST=0,  // x := constant
                VAR=1,    // x := y
                PLUS_ONE=2,  // x := x + 1
                PLUS_VAR=3   // x := x + y
            };
            struct cs_assign {
                assign_type type = assign_type::CONST;
                std::list<std::string> vars = std::list<std::string>();
                unsigned long num = -1;
                const std::string type2str() const;
                bool operator<(const cs_assign& other) const;
            };
            using cs_state = unsigned int;
            using cs_transition = std::pair<cs_assign, cs_state>;
            using cs_relation = std::map<cs_state, std::set<cs_transition>>;
            // public methods
            const std::set<cs_state>& init_states() const { return init; };  // return a copied reference
            const cs_state final_state() const { return final; };
            bool is_init(cs_state const& s) const { return init.count(s) > 0;  };
            bool is_final(cs_state const& s) const { return s == final; };
            void add_init_state(const cs_state s) { init.insert(s); };
            void set_final_state(const cs_state s) { final = s; }  // Note: no check of number of states
            bool add_transition(const cs_state s, const cs_assign& assign, const cs_state s_to);  // add one transition
            void add_var_name(const std::string& str) { var_names.insert(str); };
            const std::set<std::string>& get_var_names() const { return var_names; };
            const unsigned long get_num_states() const { return num_states; };
            const cs_relation& get_relations() const { return relation; };
            void print_counter_system() const;  // printout
        private:
            // private attributes
            std::set<std::string> var_names;  // all var names appeared
            unsigned long num_states;
            std::set<cs_state> init;  // initial (success) states
            cs_state final;           // final state (root of word equation)
            cs_relation relation;     // adjacency format
//            std::map<cs_sate, std::set<cs_cond>> init_cond;  // ToDo, plan: record polynomial coefficients
            // private methods
            void print_transition(const cs_state s, const cs_assign& assign, const cs_state s_to) const;
        };

        class apron_counter_system {
        public: // types
            class node {
            public:
                using ref = std::reference_wrapper<node>;
                node()=default;
                node(ap_manager_t* man, ap_abstract1_t& base_abs);  // initialize base attributes
                node(ap_manager_t* man, ap_environment_t* env, bool top_flag);  // initialize with apron defaults
                bool equal_to_pre(ap_manager_t* man) { return ap_abstract1_is_eq(man,&abs_pre,&abs); };
                ap_abstract1_t& get_abs() { return abs; };
                bool join_and_update_abs(ap_manager_t* man, ap_abstract1_t& from_abs);
                void widening(ap_manager_t* man);
                void print_abs(ap_manager_t* man) { ap_abstract1_fprint(stdout,man,&abs); };
                void print_abs_silent(ap_manager_t* man);
                void print_abs_pre(ap_manager_t* man) { ap_abstract1_fprint(stdout,man,&abs_pre); };
//                bool operator<(const node& other) { return abs<other.get_abs()? true:false; };
            private:
                ap_abstract1_t abs;
                ap_abstract1_t abs_pre;
            };
            class ap_assign {
            public:
                ap_assign(ap_environment_t* env, const counter_system::cs_assign& assign);
                const std::list<std::pair<char*,ap_linexpr1_t>>& get_var_exp_pairs() const { return var_exp_pairs; };
                void abstraction_propagate(ap_manager_t* man, node& s, node& s_to);
            private:
                std::list<std::pair<char*,ap_linexpr1_t>> var_exp_pairs;
            };
            using ap_state = counter_system::cs_state;
            using cs_transition = counter_system::cs_transition;
            using ap_transition = std::pair<ap_assign,ap_state>;
            using ap_relation = std::map<ap_state,std::list<ap_transition>>;
        private: // private attributes
            ap_manager_t* man;
            ap_var_t* variables;
            ap_environment_t* env;
            unsigned long num_states;
            unsigned long num_vars;
            unsigned int widening_threshold = 10;
            std::set<ap_state> init;
            ap_state final;
            std::map<ap_state,node> nodes;
            ap_relation relations;
        public: // public methods
            apron_counter_system(const counter_system& cs);
            void abstraction();
            void run_abstraction();
            bool fixpoint_check(bool widen_flag);
            void print_apron_counter_system();
            long int coeff2int(ap_coeff_t* c);
            void export_final_lincons(arith_util& ap_util_a, seq_util& ap_util_s);
//            node& get_final_node() { return nodes.find(final)->second; };  // note: should be used with const
        };
    }

    std::ostream& operator<<(std::ostream& os, str::automaton::sptr a);

    class theory_str : public theory {
        int m_scope_level = 0;
        const theory_str_params& m_params;
        th_rewriter m_rewrite;
        arith_util m_util_a;
        seq_util m_util_s;
        std::unique_ptr<str::zaut_adaptor> m_aut_imp;

        scoped_vector<str::expr_pair> m_word_eq_todo;
        scoped_vector<str::expr_pair> m_word_diseq_todo;
        scoped_vector<str::expr_pair> m_membership_todo;
    public:
        theory_str(ast_manager& m, const theory_str_params& params);
        void display(std::ostream& os) const override;
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
        bool is_of_this_theory(expr *e) const;
        bool is_string_sort(expr *e) const;
        bool is_regex_sort(expr *e) const;
        expr_ref mk_sub(expr *a, expr *b);
        expr_ref mk_skolem(symbol const& s, expr *e1, expr *e2 = nullptr, expr *e3 = nullptr,
                           expr *e4 = nullptr, sort *range = nullptr);
        literal mk_literal(expr *e);
        bool_var mk_bool_var(expr *e);
        str::language mk_language(expr *e);
        str::word_term mk_word_term(expr *e) const;
        str::state mk_state_from_todo();
        void add_axiom(expr *e);
        void add_clause(std::initializer_list<literal> ls);
        void handle_char_at(expr *e);
        void handle_substr(expr *e);
        void handle_index_of(expr *e);
        void handle_prefix(expr *e);
        void handle_suffix(expr *e);
        void handle_contains(expr *e);
        void handle_in_re(expr *e, bool is_true);
        void set_conflict(const literal_vector& ls);
        void block_curr_assignment();
        void dump_assignments() const;
    };

}

#endif /* _THEORY_STR_H_ */
