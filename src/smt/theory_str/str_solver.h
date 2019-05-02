#ifndef _STR_SOLVER_H_
#define _STR_SOLVER_H_

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
#include "smt/theory_str/automata.h"
#include "smt/theory_str/affine_program.h"


namespace smt {
    class theory_str;
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
            static const element& multiple();

        private:
            static size_t var_num;
            static std::set<element> variables;
            element::t m_type;
            zstring m_value;
            std::list<expr*> m_expr;
            string m_shortname;
        public:
            element(const element::t& t, const zstring& v, expr* e) : m_type{t}, m_value{v} {
                m_expr.push_back(e);
                if(m_type==t::VAR){
                    if(variables.find(*this)==variables.end()){
                        m_shortname = "V"+std::to_string(var_num);
                        var_num++;
                        variables.insert(*this);
                    }else{
                        m_shortname=variables.find(*this)->m_shortname;
                    }
                }
            }
            element(const std::list<element>&);
            const element::t& type() const { return m_type; }
            const zstring& value() const { return m_value; }
            const string& shortname() const { return m_shortname; }
            const std::list<expr*>& origin_expr() const { return m_expr; }
            bool typed(const element::t& t) const { return m_type == t; }
            bool operator==(const element& other) const;
            bool operator!=(const element& other) const { return !(*this == other); }
            bool operator<(const element& other) const;
            explicit operator bool() const { return *this != null(); }
            friend std::ostream& operator<<(std::ostream& os, const element& e);
            static string abbreviation_to_fullname();
        };

        class word_term {
        public:
            struct hash {
                std::size_t operator()(const word_term& w) const;
            };
            static const word_term& null();
            static word_term from_string(const zstring& str);
            static word_term from_variable(const zstring& name, expr* e);
            static bool prefix_const_mismatched(const word_term& w1, const word_term& w2);
            static bool suffix_const_mismatched(const word_term& w1, const word_term& w2);
            static bool unequalable(const word_term& w1, const word_term& w2, const std::map<element, size_t>& lb ) ;
            static void update_next_and_previous_element_maps(const word_term& , std::map<element,element>&, std::map<element,element>& ) ;
        private:
            std::list<element> m_elements;
        public:
            word_term() = default;
            word_term(std::initializer_list<element> list);
            word_term(const std::list<element>& list);
            std::size_t length() const { return m_elements.size(); }
            std::size_t count_const() const;
            word_term merge_list_of_elements(const std::list<element>&) const;
            std::size_t minimal_model_length(const std::map<element, size_t>& lb) const {
                size_t length=0;

                for(auto& e:m_elements) {
                    if (e.typed(element::t::CONST)) length++;
                    else if (e.typed(element::t::VAR) && lb.find(e) != lb.end())
                        length += lb.find(e)->second;
                }
                return length;
            }
            std::size_t count_var(const element& e) const;
            std::set<element> variables() const;
            const std::list<element>& content() const { return m_elements; }
            const element& head() const;
            element get(size_t index ) const ;
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
           ;
            word_equation(const word_term& lhs, const word_term& rhs);
            element::pair heads() const { return {m_lhs.head(), m_rhs.head()}; }
            std::size_t count_var(const element& e) const;
            std::set<element> variables() const;
            const word_term& lhs() const { return m_lhs; }
            const word_term& rhs() const { return m_rhs; }
            const element& definition_var() const;
            const word_term& definition_body() const;
            word_equation merge_list_of_elements(const std::list<element>&) const;
            bool empty() const { return m_lhs.empty() && m_rhs.empty(); }
            bool unsolvable(const std::map<element, size_t>& lb = std::map<element, size_t>()) const;
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

        class var_relation {
            using node = element;
            using nodes = std::set<node>;
            bool m_valid = true;
            nodes m_heads;
            nodes m_visited;
            nodes m_straight_line;
            std::map<node, nodes> m_record;
            std::map<node, word_term> m_definition;
        public:
            explicit var_relation(const state& s);
            bool is_valid() const { return m_valid; }
            bool check_straight_line(const node& n);
            bool is_straight_line();
            const nodes& heads() const { return m_heads; }
            const std::map<node, word_term>& definition_table() const { return m_definition; }
        };

        class memberships {
        public:
            using ptr = std::unique_ptr<memberships>;
            using sptr = std::shared_ptr<memberships>;
            using len_constraints = std::list<std::pair<element, automaton::len_constraint>>;
        public:
            virtual ~memberships() = 0;
            virtual bool empty() = 0;
            virtual bool inconsistent() = 0;
            virtual std::size_t hash() = 0;
            virtual std::set<element> variables() = 0;
            virtual void set(const element& var, expr * re) = 0;
            virtual automaton::sptr get(const element& var) = 0;
            virtual ptr assign_empty(const element& var) = 0;
            virtual ptr assign_empty_all(const std::set<element>& vars) = 0;
            virtual ptr assign_const(const element& var, const word_term& tgt) = 0;
            virtual ptr assign_as(const element& var, const element& as_var) = 0;
            virtual std::list<ptr> assign_prefix(const element& var, const element& ch) = 0;
            virtual std::list<ptr> assign_prefix_var(const element& var, const element& prefix) = 0;
            virtual len_constraints length_constraints() = 0;
            virtual len_constraints length_constraints(const element& l, const word_term& r) = 0;
            virtual std::ostream& display(std::ostream& os) = 0;
            virtual bool operator==(const memberships& other) = 0;
            virtual bool operator!=(const memberships& other) { return !(*this == other); }
            friend std::ostream& operator<<(std::ostream& os, memberships::sptr m);
        };

        using expr_pair = std::pair<expr_ref, expr_ref>;
        using tvar_pair = std::pair<theory_var , theory_var >;


        class basic_memberships : public memberships {
            struct automaton_ref {
                automaton::sptr ref;
                automaton_ref() = default;
                explicit automaton_ref(automaton::sptr ref) : ref{std::move(ref)} {}
                bool operator==(const automaton_ref& other) const { return *ref == *other.ref; }
            };
            using record = std::unordered_map<element, automaton_ref, element::hash>;
            bool m_inconsistent = false;
            automaton_factory::sptr m_aut_maker;
            record m_record;
        public:
            explicit basic_memberships(automaton_factory::sptr af) : m_aut_maker{std::move(af)} {}
            ~basic_memberships() override = default;
            bool empty() override { return m_record.empty(); }
            bool inconsistent() override { return m_inconsistent; }
            std::size_t hash() override;
            std::set<element> variables() override;
            void set(const element& var, expr * re) override;
            automaton::sptr get(const element& var) override;
            ptr assign_empty(const element& var) override;
            ptr assign_empty_all(const std::set<element>& vars) override;
            ptr assign_const(const element& var, const word_term& tgt) override;
            ptr assign_as(const element& var, const element& as_var) override;
            std::list<ptr> assign_prefix(const element& var, const element& ch) override;
            std::list<ptr> assign_prefix_var(const element& var, const element& prefix) override;
            len_constraints length_constraints() override { return {}; }
            len_constraints length_constraints(const element& l, const word_term& r) override { return {}; }
            std::ostream& display(std::ostream& os) override;
            bool operator==(const memberships& other) override;
        private:
            basic_memberships* shallow_copy() const;
            ptr mk_ptr(basic_memberships* m) const;
            automaton::sptr remove_prefix(automaton::sptr a, const zstring& prefix) const;
        };
        class length_constraints {
        private:

            class constraint {
            public:
                //maintains a map m_coeffs that represents the inequality SUM_{A in Dom(m_coeffs)} m_coeffs[A]*A >= 0
                enum class t {
                    EXPR, GT, EQ
                };
                static const element& constant(){
                    return element::null();
                }
                constraint(const constraint & other) { m_coeffs = other.m_coeffs; type=other.type;}
                constraint(const element& var) {
                    if(var.typed(element::t::VAR)){
                        m_coeffs.insert({var,1}); type=t::EXPR;
                    }else if(var.typed(element::t::CONST)){
                        m_coeffs.insert({constraint::constant(),1}); type=t::EXPR;
                    }
                }
                constraint() { m_coeffs.insert({constant(),0}); type=t::GT;}//for initial path constraint

                constraint& operator=(const constraint & other) { m_coeffs = other.m_coeffs; type=other.type; return *this; }
                expr_ref get_expr(ast_manager& m) const;
                void neg() {for (auto e : m_coeffs) { m_coeffs[e.first] = -e.second;} }
                void add(const constraint& tgt) {  for (const auto& e : tgt.m_coeffs) { add(e.first, e.second); } }
                void minus(const constraint& tgt) { for (const auto& e : tgt.m_coeffs) { add(e.first, -e.second); } }
                constraint& set_type(t type){this->type=type;return *this;}
                bool operator<(const constraint& other) const {
                    if (type < other.type) return true;
                    if (type > other.type) return false;
                    return m_coeffs < other.m_coeffs;
                }
                std::ostream& print(std::ostream& os) const{
                    bool is_zero=true;
                    for(auto e_it = m_coeffs.begin();e_it != m_coeffs.end();++e_it){
                        if(e_it->second!=0) {
                            if (e_it->first == element::null()) {
                                os << e_it->second;
                            } else if (e_it->second==1){
                                os << e_it->first;
                            }else{
                                os<<e_it->second<<"*"<<e_it->first;
                            }
                            is_zero=false;
                            if(std::next(e_it) != m_coeffs.end() &&
                            (std::next(e_it)->first !=element::null() || std::next(e_it)->second !=0)){
                                os<<" + ";
                            }
                        }
                    }
                    if(is_zero) os<<0;
                    if(type==t::GT){
                        os<<" > 0";
                    }else if(type==t::EQ){
                        os<<" = 0";
                    }
                    return os;
                };
                void add(element name, int num) { m_coeffs[name] = get_coeff(name) + num; }

            private:
                t type;
                std::map<element,int> m_coeffs;
                int get_coeff(element name) { if (m_coeffs.count(name)>0) return m_coeffs[name]; else return 0; }
                void update(element name, int num) { m_coeffs[name] = num; }
            };

            std::set<constraint> m_path_cond;
            std::map<element,constraint> m_len_cons;
        public:

            length_constraints() = default;
            length_constraints(const std::set<element>& vars);  // constructor for root state
            length_constraints(const length_constraints& other){
                m_path_cond=other.m_path_cond;
                m_len_cons=other.m_len_cons;
            };  // copy constructor

            expr_ref get_path_cond(ast_manager& m) const;
            expr_ref get_len_cons(const element& e, ast_manager& m) const;
            length_constraints assign_prefix(const element& var, const element& ch) const;
            length_constraints assign_as(const element& var, const element& as_var) const;
            length_constraints assign_const(const element& var, const word_term& tgt) const;
            length_constraints assign_empty(const element& var, const element& non_zero_var) const;
            length_constraints assign_empty_all(const std::set<element>& vars) const;
            length_constraints assign_prefix_var(const element& var, const element& prefix) const;
            length_constraints add_equality(const element& lhs, const word_term& rhs) const;

            void merge_list_of_elements(const std::list<element>&);

            std::ostream& print_path_cond(std::ostream& os) const {
                for(auto& p:m_path_cond){
                    p.print(os)<<std::endl;
                }
                return os;
            }
            std::ostream& print_len_cons(std::ostream& os) const {
                for(auto& lc:m_len_cons){
                    os<<lc.first<<"_cur = ";
                    lc.second.print(os)<<std::endl;
                }
                return os;
            }
            friend std::ostream& operator<<(std::ostream& os, const length_constraints& s);

        };

        class state {
        public:
            using cref = std::reference_wrapper<const state>;
            struct hash {
                std::size_t operator()(const state& s) const;
            };
            std::map<element, size_t> m_lower_bound;
            enum class transform_strategy {
                allow_empty_var, not_allow_empty_var, dynamic_empty_var_detection
            };

        private:
            state::transform_strategy m_strategy;

            std::set<word_equation> m_eq_wes;
            std::set<word_equation> m_diseq_wes;
            memberships::sptr m_memberships;
            length_constraints m_length;
            std::map<element, word_term> m_model;
            std::map<element, unsigned> var_occurrence;
            std::map<word_term, std::set<word_term>> eq_class_map;
            void initialize_eq_class_map();
            void count_variable_occurrences();
            bool quadratic_after_add_this_term(const word_term&);
            bool has_non_quadratic_var(const word_term& wt);
            word_term find_alternative_term(const word_term&,const word_term&);
            static void merge_list_of_elements(std::set<word_equation>&, const std::list<element>&);
        public:
            explicit state(memberships::sptr m) : m_strategy{state::transform_strategy::dynamic_empty_var_detection},m_memberships{std::move(m)} {}
            std::size_t word_eq_num() const { return m_eq_wes.size(); }
            std::set<element> variables() const;
            std::vector<std::vector<word_term>> eq_classes() const;

            memberships::sptr get_memberships() const { return m_memberships; }
            const std::set<word_equation>& word_eqs() const { return m_eq_wes; }
            const word_equation& smallest_eq() const;
            const word_equation& only_one_eq_left() const;
            var_relation var_rel_graph() const;
            const transform_strategy get_strategy() const { return m_strategy; }
            void initialize_length_constraint(const std::set<element>& var) { m_length={var}; }
            void initialize_model_map(const std::set<element>& var) {
                for(const auto &v:var){
                    std::list<element> wt_content;
                    wt_content.push_back(v);
                    word_term wt(wt_content);
                    m_model[v]=wt;
                }
            }

            void set_strategy(transform_strategy st) { m_strategy=st; }
            bool is_non_empty_var(const element& v) const {return m_lower_bound.find(v)!=m_lower_bound.end() && m_lower_bound.find(v)->second > 0;}
            void merge_elements();
            bool in_definition_form() const;
            bool eq_classes_inconsistent() const;
            bool diseq_inconsistent() const;
            bool unsolvable_by_check() const;
            bool unsolvable_by_inference() const;
            bool quadratic() const;
            void quadratify();
            void remove_single_variable_word_term();
            void remove_useless_diseq();
            void add_word_eq(const word_equation& we);
            void add_word_diseq(const word_equation& we);
            void add_membership(const element& var, expr * re);
            state assign_empty(const element& var, const element& non_zero_var=element::null()) const;
            state assign_empty_all(const std::set<element>& vars) const;
            state assign_const(const element& var, const word_term& tgt) const;
            state assign_as(const element& var, const element& as_var) const;
            std::list<state> assign_prefix(const element& var, const element& ch) const;
            std::list<state> assign_prefix_var(const element& var, const element& prefix) const;
            void set_length(const length_constraints& lc);
            bool operator==(const state& other) const;
            bool operator!=(const state& other) const { return !(*this == other); }
            friend std::ostream& operator<<(std::ostream& os, const state& s);
            bool is_reachable(ast_manager& m, context& ctx, theory_str& th) const;
        };

        enum class result {
            SAT, UNSAT, UNKNOWN
        };

        class solver {
        public:
            struct move {
                enum class t {
                    TO_EMPTY = 0,
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
            std::list<state> m_unchecked_leaves;
            result m_status = result::UNKNOWN;
            record_graph m_records;
            state::cref m_rec_root;
            std::list<state::cref> m_rec_success_leaves;
            std::stack<state::cref> m_pending;
            automaton_factory::sptr m_aut_maker;
        public:
            explicit solver(state&& root, automaton_factory::sptr af);
            bool in_status(const result& t) const { return m_status == t; }
            bool should_explore_all() const;

            bool unfinished();
            void resume(ast_manager& m, context& ctx, theory_str& th);
            std::list<state> get_last_leaf_states();
            result check();

            const record_graph& get_graph() const { return m_records; };
            const std::list<state::cref>& get_success_leaves() const { return m_rec_success_leaves; };
            const state::cref get_root() const { return m_rec_root; };
        private:
            automaton::sptr derive_var_membership(const var_relation& g, memberships::sptr m, const element& var);
            bool check_straight_line_membership(const var_relation& g, memberships::sptr m);
            automaton::sptr concat_simple_membership(memberships::sptr m, const word_term& w);
            bool check_linear_membership(const state& s);
            bool finish_after_found(const state& s);
            const state& add_sibling_ext_record(const state& s, state&& sib, const element& v);
            const state& add_child_var_removed(const state& s, state&& c, const element& v);
            result split_var_empty_cases();
            std::queue<state::cref> split_first_level_var_empty();
            std::list<action> transform(const state& s) const;

        };

    }
    class seq_expr_solver : public expr_solver {
        kernel m_kernel;
        ast_manager& m;
    public:
        seq_expr_solver(ast_manager& m, smt_params& fp, context& ctx):
                m_kernel(m, fp), m(m){}

        lbool check_sat(expr* e) override {
            m_kernel.push();
            m_kernel.assert_expr(e);
            lbool r = m_kernel.check();
            m_kernel.pop(1);
            return r;
        }

        void assert_expr(expr * e){
            m_kernel.assert_expr(e);
        }
    };

}

#endif /* _STR_SOLVER__H_ */
