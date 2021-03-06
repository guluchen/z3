#ifndef _AFFINE_PRG_H_
#define _AFFINE_PRG_H_

#include <functional>
#include <list>
#include <set>
//#include <stack>
#include <map>
//#include <memory>
#include <queue>
#include <unordered_map>
#include <unordered_set>
//#include <vector>
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

        class state;
        class solver;

        class counter_system {
        public:
            // constructor
            counter_system(const solver &solv);

            // type defines
            enum class assign_type {
                CONST = 0,  // x := constant
                VAR = 1,    // x := y
                PLUS_ONE = 2,  // x := x + 1
                PLUS_VAR = 3   // x := x + y
            };

            struct cs_assign {
                assign_type type = assign_type::CONST;
                std::list<std::string> vars = std::list<std::string>();
                unsigned long num = -1;
                const std::string type2str() const;
                bool operator<(const cs_assign &other) const;
            };

            using cs_state = unsigned int;
            using cs_transition = std::pair<cs_assign, cs_state>;
            using cs_relation = std::map<cs_state, std::set<cs_transition>>;

            // public methods
            const std::set<cs_state> &init_states() const { return init; };  // return a copied reference
            const cs_state final_state() const { return final; };
            bool is_init(cs_state const &s) const { return init.count(s) > 0; };
            bool is_final(cs_state const &s) const { return s == final; };
            void add_init_state(const cs_state s) { init.insert(s); };
            void set_final_state(const cs_state s) { final = s; }  // Note: no check of number of states
            bool add_transition(const cs_state s, const cs_assign &assign, const cs_state s_to);  // add one transition
            bool add_var_expr(const std::string &str, const std::list<expr*> exprs, const std::string& str_short);
            const std::map<std::string,std::pair<std::list<expr*>,std::string>> &get_var_expr() const { return var_expr; };
            const unsigned long get_num_states() const { return num_states; };
            const cs_relation &get_relations() const { return relation; };
            expr_ref get_length_constraint_for_dag_counter_system(ast_manager&);
            void print_counter_system() const;  // printout
            void print_var_expr(ast_manager & m);
            bool is_dag();
        private:
            // private attributes
            std::map<std::string,std::pair<std::list<expr*>,std::string>> var_expr;  // var names appeared mapped to their internal expressions in z3 together with their short names
            unsigned long num_states;
            std::set<cs_state> init;  // initial (success) states
            cs_state final;           // final state (root of word equation)
            cs_relation relation;     // adjacency format
//            std::map<cs_sate, std::set<cs_cond>> init_cond;  // ToDo, plan: record polynomial coefficients
            // private methods
            void print_transition(const cs_state s, const cs_assign &assign, const cs_state s_to) const;
        };

        long int coeff2int(ap_coeff_t *c);

        class apron_counter_system {
        public: // types
            class node {
            public:
                using ref = std::reference_wrapper<node>;

                node() = default;
                node(ap_manager_t *man, ap_abstract1_t &base_abs);  // initialize base attributes
                node(ap_manager_t *man, ap_environment_t *env, bool top_flag);  // initialize with apron defaults
                bool equal_to_pre(ap_manager_t *man) { return ap_abstract1_is_eq(man, &abs_pre, &abs); };
                ap_abstract1_t &get_abs() { return abs; };
                void join_and_update_abs(ap_manager_t *man, ap_abstract1_t &from_abs);
                void widening(ap_manager_t *man);
                void print_abs(ap_manager_t *man) { ap_abstract1_fprint(stdout, man, &abs); };
                void print_abs_silent(ap_manager_t *man);
                void print_abs_pre(ap_manager_t *man) { ap_abstract1_fprint(stdout, man, &abs_pre); };
//                bool operator<(const node& other) { return abs<other.get_abs()? true:false; };
            private:
                ap_abstract1_t abs;
                ap_abstract1_t abs_pre;
            };

            class ap_assign {
            public:
                ap_assign(ap_environment_t *env, const counter_system::cs_assign &assign);
                const std::list<std::pair<char *, ap_linexpr1_t>> &get_var_exp_pairs() const { return var_exp_pairs; };
                void abstraction_propagate(ap_manager_t *man, node &s, node &s_to);

            private:
                std::list<std::pair<char *, ap_linexpr1_t>> var_exp_pairs;
            };

            using ap_state = counter_system::cs_state;
            using cs_transition = counter_system::cs_transition;
            using ap_transition = std::pair<ap_assign, ap_state>;
            using ap_relation = std::map<ap_state, std::list<ap_transition>>;
        private: // private attributes
            ap_manager_t *man;
            ap_var_t *variables;
            std::map<std::string,std::pair<std::list<expr*>,std::string>> var_expr;  // var names appeared mapped to their internal expressions in z3
            ap_environment_t *env;
            unsigned long num_states;
            unsigned long num_vars;
            unsigned int widening_threshold = 10;
            std::set<ap_state> init;
            ap_state final;
            std::map<ap_state, node> nodes;
            ap_relation relations;
        public: // public methods
            apron_counter_system(const counter_system &cs);
            void abstraction();
            void run_abstraction();
            bool fixpoint_check(bool widen_flag);
            ap_manager_t* get_ap_manager() { return man; };
            void print_apron_counter_system();
            node& get_final_node() { return nodes[final]; };  // use it like a const method.
            const std::map<std::string,std::pair<std::list<expr*>,std::string>>& get_var_expr() { return var_expr; };  // use it like a const method.
        };

        class ap_length_constraint {
        public:
            enum class lcons_type {
                EQ = 0,    // =0
                SUPEQ = 1  // >=0
            };
            class len_cons {
                lcons_type m_type;
                std::map<std::string,std::pair<std::list<expr*>,long int>> m_var_expr_coeff;
                long int m_cst;
            public:
                len_cons(ap_manager_t *ap_man, ap_lincons1_t* ap_cons_ptr,
                        const std::map<std::string,std::pair<std::list<expr*>,std::string>>& var_expr);
                void pretty_print(ast_manager& ast_man, bool on_screen);
                expr_ref export_z3exp(ast_manager&);
            };
        private:
            std::list<len_cons> m_cons;
        public:
            ap_length_constraint(ap_manager_t *ap_man, ap_abstract1_t* ap_abs_ptr,
                   const std::map<std::string,std::pair<std::list<expr*>,std::string>>& var_expr);
            void pretty_print(ast_manager& ast_man);
            expr_ref export_z3exp(ast_manager& m);
            bool empty() { return m_cons.empty(); };
        };

    }
}

#endif /* _AFFINE_PRG_H_ */
