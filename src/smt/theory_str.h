#ifndef _THEORY_STR_H_
#define _THEORY_STR_H_

#include <list>
#include <set>
#include <stack>
#include <map>
#include <vector>
#include "ast/arith_decl_plugin.h"
#include "ast/ast_pp.h"
#include "smt/params/theory_str_params.h"
#include "smt/proto_model/value_factory.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/seq_decl_plugin.h"
#include "smt/smt_model_generator.h"
#include "smt/smt_theory.h"
#include "util/hashtable.h"
#include "util/scoped_vector.h"
#include "util/scoped_ptr_vector.h"
#include "util/trail.h"
#include "util/union_find.h"
#include "smt/smt_arith_value.h"

#define LOCALSPLITMAX 20
#define SUMFLAT 100000000
#define EMPTYFLAT 9999999

#define REGEX_CODE -10000
#define MINUSZERO 999

#define LENPREFIX "len_"
#define ARRPREFIX "arr_"
#define ITERSUFFIX "__iter"

namespace smt {



    enum {
        NONE = 0,
        LEFT_EMPTY = 1,
        LEFT_EQUAL = 2,
        LEFT_SUM = 3,
        RIGHT_EMPTY = 4,
        RIGHT_EQUAL = 5,
        RIGHT_SUM = 6
    };

    enum {
        SIMPLE_CASE = 0,
        CONST_ONLY = 1,
        CONNECTED_ONLY = 2,
        CONST_CONNECTED = 3
    };


    class theory_str_contain_pair_bool_map_t : public obj_pair_map<expr, expr, expr*> {};

    class theory_str : public theory {
        int m_scope_level;
        const theory_str_params& m_params;

        typedef union_find<theory_str> th_union_find;
        typedef trail_stack<theory_str> th_trail_stack;
        struct zstring_hash_proc {
            unsigned operator()(zstring const & s) const {
                return string_hash(s.encode().c_str(), static_cast<unsigned>(s.length()), 17);
            }
        };
        typedef map<zstring, expr*, zstring_hash_proc, default_eq<zstring> > string_map;

        class Arrangment{
        public:
            std::vector<int> left_arr;
            std::vector<int> right_arr;

            Arrangment(std::vector<int> _left_arr,
                       std::vector<int> _right_arr){
                left_arr.insert(left_arr.end(), _left_arr.begin(), _left_arr.end());
                right_arr.insert(right_arr.end(), _right_arr.begin(), _right_arr.end());
            }

            void addLeft(int number) {
                left_arr.emplace_back(number);
            }

            void addRight(int number) {
                right_arr.emplace_back(number);
            }

            bool canSplit(int boundedFlat, int boundSize, int pos, std::string frame, std::vector<std::string> &flats) {
                if ((int)flats.size() == boundedFlat)
                    return false;

                for (int size = 1; size <= boundSize; ++size) { /* size of a flat */
                    std::string flat = frame.substr(pos, size);
                    flats.emplace_back(flat); /* add to stack */
                    int tmpPos = pos + size;

                    while (true) {
                        std::string nextIteration = frame.substr(tmpPos, size);
                        if (nextIteration.compare(flat) != 0)
                            break;
                        else if (tmpPos < (int)frame.length() && tmpPos + size <= (int)frame.length()){
                            tmpPos += size;
                        }
                        else
                            break;
                    }
                    if (tmpPos < (int)frame.length()){
                        if (canSplit(boundedFlat, boundSize, tmpPos, frame, flats))
                            return true;
                        else {
                            /* de-stack */
                            flats.pop_back();
                        }
                    }
                    else {
                        return true;
                    }
                }
                return false;
            }



            bool isUnionStr(std::string str){
                return str.find("|") != std::string::npos;
            }

            /*
            * Pre-Condition: x_i == 0 --> x_i+1 == 0
            */
            bool isPossibleArrangement(
                    std::vector<std::pair<expr*, int>> lhs_elements,
                    std::vector<std::pair<expr*, int>> rhs_elements){
                /* bla bla */
                for (unsigned i = 0; i < left_arr.size(); ++i)
                    if (left_arr[i] != -1){
                        for (int j = i - 1; j >= 0; --j){
                            if (lhs_elements[j].second < lhs_elements[i].second) { /* same var */
                                if (left_arr[j] == -1)
                                    return false;
                            }
                            else
                                break;
                        }
                    }
                for (unsigned i = 0; i < right_arr.size(); ++i)
                    if (right_arr[i] != -1){
                        for (int j = i - 1; j >= 0; --j){
                            if (rhs_elements[j].second < rhs_elements[i].second) { /* same var */
                                if (right_arr[j] == -1)
                                    return false;
                            }
                            else
                                break;
                        }
                    }
                return true;
            }


            void printArrangement(std::string msg = ""){
                if (msg.length() > 0)
                STRACE("str", tout << msg << std::endl;);

                for (unsigned int i = 0; i < left_arr.size(); ++i)
                STRACE("str", tout << left_arr[i] << " ";);

                STRACE("str", tout << std::endl;);
                for (unsigned int i = 0; i < right_arr.size(); ++i)
                STRACE("str", tout << right_arr[i] << " ";);
                STRACE("str", tout <<  std::endl;);
            }
        };


    public:
        theory_str(ast_manager& m, const theory_str_params& params);
        void display(std::ostream& os) const override;
        th_trail_stack& get_trail_stack() { return m_trail_stack; }
        void merge_eh(theory_var, theory_var, theory_var v1, theory_var v2) {}
        void after_merge_eh(theory_var r1, theory_var r2, theory_var v1, theory_var v2) { }
        void unmerge_eh(theory_var v1, theory_var v2) {}

    protected:
        void init(context *ctx) override;
        bool internalize_atom(app *atom, bool gate_ctx) override;
        bool internalize_term(app *term) override;
        theory_var mk_var(enode *n) override;
        theory *mk_fresh(context *) override { return alloc(theory_str, get_manager(), m_params); }

        /*
         * Helper function for mk_value().
         * Attempts to resolve the expression 'n' to a string constant.
         * Stronger than get_eqc_value() in that it will perform recursive descent
         * through every subexpression and attempt to resolve those to concrete values as well.
         * Returns the concrete value obtained from this process,
         * guaranteed to satisfy m_strutil.is_string(),
         * if one could be obtained,
         * or else returns NULL if no concrete value was derived.
         */
        app * mk_value_helper(app * n);
        model_value_proc *mk_value(enode *n, model_generator& mg) override;
        void add_theory_assumptions(expr_ref_vector& assumptions) override;
        lbool validate_unsat_core(expr_ref_vector& unsat_core) override;
        void new_eq_eh(theory_var, theory_var) override;
        void new_diseq_eh(theory_var, theory_var) override;
        /*
         * Add an axiom of the form:
         * len lhs != len rhs -> lhs != rhs
         * len lhs == 0 == len rhs --> lhs == rhs
         */
        void init_search_eh() override;
        void relevant_eh(app *n) override;
        void assign_eh(bool_var v, bool is_true) override;
        void push_scope_eh() override;
        void pop_scope_eh(unsigned num_scopes) override;
        void reset_eh() override;
        final_check_status final_check_eh() override;



        void get_unique_non_concat_nodes(expr * node, std::set<expr*> & argSet);

            app* createSelectOperator(expr* x, expr* y);




        bool can_propagate() override;
        void propagate() override;
        void init_model(model_generator& m) override;
        void handle_equality(expr * lhs, expr * rhs);
        /*
         * strArgmt::solve_concat_eq_str()
         * Solve concatenations of the form:
         *   const == Concat(const, X)
         *   const == Concat(X, const)
         */
        void solve_concat_eq_str(expr * concat, expr * str);
        // previously Concat() in strTheory.cpp
        // Evaluates the concatenation (n1 . n2) with respect to
        // the current equivalence classes of n1 and n2.
        // Returns a constant string expression representing this concatenation
        // if one can be determined, or NULL if this is not possible.
        expr * eval_concat(expr * n1, expr * n2);
        void group_terms_by_eqc(expr * n, std::set<expr*> & concats, std::set<expr*> & vars, std::set<expr*> & consts);
        expr * simplify_concat(expr * node);

        /*
         * Add an axiom of the form:
         * (lhs == rhs) -> ( Length(lhs) == Length(rhs) )
         */
        void instantiate_str_eq_length_axiom(enode * lhs, enode * rhs);

        // Check that a string's length can be 0 iff it is the empty string.
        void check_eqc_empty_string(expr * lhs, expr * rhs);

        /*
         * Check whether n1 and n2 could be equal.
         * Returns true if n1 could equal n2 (maybe),
         * and false if n1 is definitely not equal to n2 (no).
         */
        bool can_two_nodes_eq(expr * n1, expr * n2);
        bool can_concat_eq_str(expr * concat, zstring& str);
        bool can_concat_eq_concat(expr * concat1, expr * concat2);
        expr * getMostLeftNodeInConcat(expr * node);
        expr * getMostRightNodeInConcat(expr * node);

        /*
         * Check equality among equivalence class members of LHS and RHS
         * to discover an incorrect LHS == RHS.
         * For example, if we have y2 == "str3"
         * and the equivalence classes are
         * { y2, (Concat ce m2) }
         * { "str3", (Concat abc x2) }
         * then y2 can't be equal to "str3".
         * Then add an assertion: (y2 == (Concat ce m2)) AND ("str3" == (Concat abc x2)) -> (y2 != "str3")
         */
        bool new_eq_check(expr * lhs, expr * rhs);
        void propagate_const_str(expr * lhs, expr * rhs, zstring value);
        void propagate_non_const(expr_ref_vector litems, expr * concat, expr * new_concat);
        expr* construct_concat_overapprox(expr* nn, expr_ref_vector & litems);

        /*
        * Decide whether n1 and n2 are already in the same equivalence class.
        * This only checks whether the core considers them to be equal;
        * they may not actually be equal.
        */
        bool in_same_eqc(expr * n1, expr * n2);

        expr * collect_eq_nodes(expr * n, expr_ref_vector & eqcSet);

        /*
        * Add axioms that are true for any string variable:
        * 1. Length(x) >= 0
        * 2. Length(x) == 0 <=> x == ""
        * If the term is a string constant, we can assert something stronger:
        *    Length(x) == strlen(x)
        */
        void instantiate_basic_string_axioms(enode * str);
        /*
        * Instantiate an axiom of the following form:
        * Length(Concat(x, y)) = Length(x) + Length(y)
        */
        void instantiate_concat_axiom(enode * cat);

        app * mk_fresh_const(char const* name, sort* s);
        app * mk_strlen(expr * e);
        expr * mk_string(zstring const& str);
        expr * mk_string(const char * str);
        app * mk_str_var(std::string name);
        expr * mk_concat(expr * n1, expr * n2);
        expr * mk_concat_const_str(expr * n1, expr * n2);
        app * mk_int(int n);
        app * mk_int(rational & q);


        void get_nodes_in_concat(expr * node, ptr_vector<expr> & nodeList);
        expr * get_eqc_value(expr * n, bool & hasEqcValue);
        expr * get_eqc_next(expr * n);

        theory_var get_var(expr * n) const;
        app * get_ast(theory_var v);
        bool get_len_value(expr* e, rational& val);
        bool get_arith_value(expr* e, rational& val) const;
        bool upper_num_bound(expr* e, rational& hi) const;
        bool lower_num_bound(expr* e, rational& hi) const;
        /*
         * Collect constant strings (from left to right) in an AST node.
         */
        void get_const_str_asts_in_node(expr * node, expr_ref_vector & astList);
        /*
        * Collect constant strings (from left to right) in an AST node.
        */
        /*
         * Collect important vars in AST node
         */
        eautomaton* get_automaton(expr* re);

        void track_variable_scope(expr * var);
        void assert_implication(expr * premise, expr * conclusion);

        enode* ensure_enode(expr* e);
        bool search_started;
        th_rewriter      m_rewrite;
        seq_rewriter m_seq_rewrite;
        arith_util m_autil;
        array_util m_arrayUtil;
        seq_util u;
        expr_ref_vector m_trail; // trail for generated terms
        th_union_find m_find;
        th_trail_stack m_trail_stack;

        std::map<int, obj_hashtable<expr> > internal_variable_scope_levels;
        obj_pair_map<expr, expr, expr*> concat_astNode_map;

        std::map<std::pair<expr*, zstring>, expr*> regex_in_bool_map;
        obj_map<expr, std::set<zstring> > regex_in_var_reg_str_map;

        scoped_ptr_vector<eautomaton> m_automata;
        ptr_vector<eautomaton> regex_automata;
        obj_hashtable<expr> regex_terms;
        obj_map<expr, ptr_vector<expr> > regex_terms_by_string; // S --> [ (str.in.re S *) ]

        // hashtable of all exprs for which we've already set up term-specific axioms --
        // this prevents infinite recursive descent with respect to axioms that
        // include an occurrence of the term for which axioms are being generated
        obj_hashtable<expr> axiomatized_terms;
        obj_hashtable<expr> variable_set;
        obj_hashtable<expr> internal_variable_set;
        obj_hashtable<expr> regex_variable_set;

        expr_ref_vector m_delayed_axiom_setup_terms;

        ptr_vector<enode> m_basicstr_axiom_todo;
        svector<std::pair<enode*,enode*> > m_str_eq_todo;
        ptr_vector<enode> m_concat_axiom_todo;
        ptr_vector<enode> m_string_constant_length_todo;
        ptr_vector<enode> m_concat_eval_todo;
        expr_ref_vector m_delayed_assertions_todo;

        // enode lists for library-aware/high-level string terms (e.g. substr, contains)
        ptr_vector<enode> m_library_aware_axiom_todo;
        obj_hashtable<expr> input_var_in_len;
        expr_ref_vector string_int_conversion_terms;
        obj_hashtable<expr> string_int_axioms;

        expr_ref_vector m_persisted_axiom_todo;

        expr_ref_vector contains_map;

        theory_str_contain_pair_bool_map_t contain_pair_bool_map;
        obj_map<expr, std::set<std::pair<expr*, expr*> > > contain_pair_idx_map;
        obj_map<enode, std::pair<enode*,enode*>> contain_split_map;
        unsigned m_fresh_id;
        string_map stringConstantCache;
        unsigned long totalCacheAccessCount;

        obj_map<expr, eautomaton*>     m_re2aut;
        re2automaton                   m_mk_aut;
        expr_ref_vector                m_res;

        /*
         * If DisableIntegerTheoryIntegration is set to true,
         * ALL calls to the integer theory integration methods
         * (get_arith_value, get_len_value, lower_bound, upper_bound)
         * will ignore what the arithmetic solver believes about length terms,
         * and will return no information.
         *
         * This reduces performance significantly, but can be useful to enable
         * if it is suspected that string-integer integration, or the arithmetic solver itself,
         * might have a bug.
         *
         * The default behaviour of Z3str2 is to set this to 'false'.
         */
        bool opt_DisableIntegerTheoryIntegration;

        /*
         * If ConcatOverlapAvoid is set to true,
         * the check to simplify Concat = Concat in handle_equality() will
         * avoid simplifying wrt. pairs of Concat terms that will immediately
         * result in an overlap. (false = Z3str2 behaviour)
         */
        bool opt_ConcatOverlapAvoid;


        // under approximation vars
        const int CONNECTINGSIZE = 300;
        static const int QCONSTMAX = 2;
        static const int QMAX = 2;
        static const int PMAX = 2;
        const std::string FLATPREFIX = "__flat_";
        int noFlatVariables = 0;
        bool trivialUnsat = false;


        std::map<expr*, int> varPieces;
        std::map<expr*, int> currVarPieces;
        std::set<std::string> generatedEqualities;

        std::map<std::pair<int, int>, std::vector<Arrangment>> arrangements;
        std::set<zstring> constSet;

        std::map<expr*, std::vector<expr*>> lenMap;
        std::map<expr*, std::vector<expr*>> iterMap;
        std::map<expr*, std::set<expr*>> appearanceMap;
        std::map<expr*, std::set<expr*>> notContainMap;
        std::map<expr*, expr*> arrMap;
        int connectingSize;

    private:
        void assert_axiom(expr *e);
        decl_kind get_decl_kind(expr *e) const;
        void set_up_axioms(expr * ex);
    };

}

#endif /* _THEORY_STR_H_ */
