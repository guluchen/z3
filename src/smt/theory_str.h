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

#define ROUNDCHECK 1
#define LOCALSPLITMAX 20
#define SUMFLAT 100000000
#define EMPTYFLAT 9999999

#define REGEX_CODE -10000
#define MINUSZERO 999

#define LENPREFIX "len_"
#define ARRPREFIX "arr_"
#define ITERSUFFIX "__iter"
#define ZERO "0"
#define REGEXSUFFIX "_10000"

namespace smt {

    namespace str {

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
            const bool typed(const element_t& t) const { return m_type == t; }
            explicit operator bool() const { return *this != null(); }
            const bool operator==(const element& other) const;
            const bool operator!=(const element& other) const { return !(*this == other); }
            const bool operator<(const element& other) const;
            friend std::ostream& operator<<(std::ostream& os, const element& e);
        };

        class word_term {
            std::list<element> m_elements;
        public:
            static const word_term& null();
            static word_term of_string(const std::string& literal);
            static word_term of_variable(const std::string& name);
            static const bool prefix_mismatched_in_consts(const word_term& w1, const word_term& w2);
            static const bool suffix_mismatched_in_consts(const word_term& w1, const word_term& w2);
            static const bool unequalable_no_empty_var(const word_term& w1, const word_term& w2);
            static const bool unequalable(const word_term& w1, const word_term& w2);
            word_term() = default;
            word_term(std::initializer_list<element> list);
            const std::size_t length() const { return m_elements.size(); }
            const std::size_t constant_count() const;
            const element& head() const;
            const std::set<element> variables() const;
            const bool empty() const { return m_elements.empty(); }
            const bool has_constant() const;
            const bool has_variable() const;
            const bool check_head(const element_t& t) const;
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
            word_term m_lhs;
            word_term m_rhs;
        public:
            static const word_equation& null();
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
            const bool check_heads(const element_t& lht, const element_t& rht) const;
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

            class transform {
                const state& m_state;
                const word_equation& m_src;
                const bool m_src_should_fail;
                std::list<state> m_result;

                transform(const state& s, const word_equation& src, bool by_wi = false);
                const bool src_vars_empty() const;
                const bool src_var_well_defined() const;
                const bool src_two_var_unequal() const;
                void transform_one_var();
                void transform_two_var();
                std::list<state> compute();
            };

            bool m_allow_empty_var = true;
            std::set<word_equation> m_wes_to_satisfy;
            std::set<word_equation> m_wes_to_fail;
        public:
            state() = default;
            explicit state(const bool allow_empty_var) : m_allow_empty_var{allow_empty_var} {}
            const std::set<element> variables() const;
            const word_equation& only_one_equation_left() const;
            const std::vector<std::vector<word_term>> equivalence_classes() const;
            const bool equivalence_classes_inconsistent() const;
            const bool disequalities_inconsistent() const;
            const bool unsolvable_by_check() const;
            const bool unsolvable_by_inference() const;
            const bool in_definition_form() const;
            const bool in_solved_form() const;
            void allow_empty_variable(const bool enable) { m_allow_empty_var = enable; }
            void satisfy_constraint(const word_equation& we);
            void fail_constraint(const word_equation& we);
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
        scoped_vector<str::expr_pair> m_we_expr_memo;
        scoped_vector<str::expr_pair> m_wi_expr_memo;
        scoped_vector<str::expr_pair> membership_memo;
        scoped_vector<str::expr_pair> non_membership_memo;

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

            int connectingSize; // extra info for all Arrangement

            Arrangment(std::vector<int> _left_arr,
                       std::vector<int> _right_arr,
                       std::map<std::string, std::string> _constMap,
                       int _connectingSize){
                left_arr.insert(left_arr.end(), _left_arr.begin(), _left_arr.end());
                right_arr.insert(right_arr.end(), _right_arr.begin(), _right_arr.end());
            }

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

            /*
             * Input: string that we are going to split, and number of flats
             * Ouput: able to split or not
             */
            int splitWithMinFlats(int boundedFlat, int boundSize, std::string frame){
                for (int i = 1; i <= boundedFlat; ++i) { /* number of flats */
                    std::vector<std::string> flats;
                    if (canSplit(i, PMAX, 0, frame, flats)){
                        return i;
                    }
                    flats.clear();
                }
                return -1;
            }

            void splitPrintTest(std::vector<int> currentSplit, std::string msg = ""){
                STRACE("str", tout << msg << std::endl;);
                for (unsigned int i = 0; i < currentSplit.size(); ++i)
                STRACE("str", tout << currentSplit[i] << " - " << std::endl;);
                STRACE("str", tout << std::endl << "------------" << std::endl;);
            }

            /**
             * Print a list
             */
            template<typename T>
            void printList(T list, std::string msg = "") {
                if (msg.length() > 0 )
                    printf("%s\n", msg.c_str());
                for (std::vector<int>::iterator it = list.begin(); it != list.end(); ++it) {
                    printf("%d ", *it);
                }
                printf("\n");
            }

            bool isUnionStr(std::string str){
                return str.find("|") != std::string::npos;
            }

            bool feasibleSplit_const(
                    std::string str,
                    std::vector<std::pair<std::string, int> > elementNames,
                    std::vector<int> currentSplit){
                /* check feasible const split */
                int pos = 0;
                for (unsigned i = 0; i < currentSplit.size(); ++i) {
                    if (elementNames[i].second == REGEX_CODE || isUnionStr(elementNames[i].first)) {
                    }

                        /* TODO: bound P */
                    else if (elementNames[i].second < 0) { /* const */
                        if (currentSplit[i] > (int)elementNames[i].first.length()) {
                        }
                        SASSERT ((int)elementNames[i].first.length() >= currentSplit[i]);

                        std::string lhs = str.substr(pos, currentSplit[i]);
                        std::string rhs = "";
                        if (elementNames[i].second % QCONSTMAX == -1) /* head */ {
                            rhs = elementNames[i].first.substr(0, currentSplit[i]);

                            if (i + 1 < elementNames.size()) {
                                if (QCONSTMAX == 1 || elementNames[i].first.length() == 1) {
                                    SASSERT (currentSplit[i] == (int)elementNames[i].first.length()); /* const length must be equal to length of const */
                                }
                                else {
                                    SASSERT (elementNames[i + 1].second % QCONSTMAX == 0);
                                    SASSERT ((currentSplit[i] + currentSplit[i + 1] == (int)elementNames[i].first.length())); /* sum of all const parts must be equal to length of const */
                                }
                            }
                        }
                        else { /* tail */
                            rhs = elementNames[i].first.substr(elementNames[i].first.length() - currentSplit[i], currentSplit[i]);
                        }

                        if (lhs.compare(rhs) != 0){
                            SASSERT(false);
                            STRACE("str", tout << __LINE__ << " " << lhs << " - " << rhs << std::endl;);
                            return false;
                        }
                    }
                    pos += currentSplit[i];
                }
                return true;
            }

            /*
             * we do not allow empty flats in the middle
             */
            bool isPossibleArrangement(){
                if (left_arr[left_arr.size() -1] == EMPTYFLAT &&
                    right_arr[right_arr.size() -1] == EMPTYFLAT)
                    return false;
                /* not allow empty flats in the middle */
                int startPos = 0;
                int endPos = left_arr.size() - 1;
                /* check lhs */
                for (startPos = 0; startPos < (int)left_arr.size(); ++startPos)
                    if (left_arr[startPos] != EMPTYFLAT)
                        break;
                for (endPos = (int)left_arr.size() - 1; endPos >= 0; --endPos)
                    if (left_arr[endPos] != EMPTYFLAT)
                        break;
                for (int i = startPos; i < endPos; ++i)
                    if (left_arr[i] == EMPTYFLAT) {
                        // printArrangement("ERRORR");
                        return false;
                    }

                /* check rhs */
                for (startPos = 0; startPos < (int)right_arr.size(); ++startPos)
                    if (right_arr[startPos] != EMPTYFLAT)
                        break;
                for (endPos = (int)right_arr.size() - 1; endPos >= 0; --endPos)
                    if (right_arr[endPos] != EMPTYFLAT)
                        break;
                for (int i = startPos; i < endPos; ++i)
                    if (right_arr[i] == EMPTYFLAT) {
                        // printArrangement("ERRORR");
                        return false;
                    }
                return true;
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
                    STRACE("str", tout << left_arr[i] << " " << std::endl;);

                STRACE("str", tout << std::endl;);
                for (unsigned int i = 0; i < right_arr.size(); ++i)
                    STRACE("str", tout << right_arr[i] << " " << std::endl;);
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
            void instantiate_str_diseq_length_axiom(expr * lhs, expr * rhs);
        void init_search_eh() override;
        void relevant_eh(app *n) override;
        void assign_eh(bool_var v, bool is_true) override;
        void push_scope_eh() override;
        void pop_scope_eh(unsigned num_scopes) override;
        void reset_eh() override;
        final_check_status final_check_eh() override;
            void underapproximation(
                std::map<expr*, std::set<expr*>> eq_combination,
                std::set<std::pair<expr*, int>> importantVars,
                str::state root);
            void initUnderapprox(std::map<expr*, std::set<expr*>> eq_combination);

            void convertEqualities(std::map<expr*, std::vector<expr*>> eq_combination,
                                           std::map<expr*, int> importantVars);

            /*
             * convert lhs == rhs to SMT formula
             */
            std::vector<expr*> equalityToSMT(
                std::string lhs, std::string rhs,
                std::vector<std::pair<expr*, int>> lhs_elements,
                std::vector<std::pair<expr*, int>> rhs_elements,
                std::map<expr*, int> connectedVariables,
                int p = PMAX);

            /*
             * lhs: size of the lhs
             * rhs: size of the rhs
             * lhs_elements: elements of lhs
             * rhs_elements: elements of rhs
             *
             * Pre-Condition: x_i == 0 --> x_i+1 == 0
             *
             */
            std::vector<expr*> collectAllPossibleArrangements(
                std::string lhs_str, std::string rhs_str,
                std::vector<std::pair<expr*, int>> lhs_elements,
                std::vector<std::pair<expr*, int>> rhs_elements,
                std::map<expr*, int> connectedVariables,
                int p = PMAX);

            void updatePossibleArrangements(
                std::vector<std::pair<expr*, int>> lhs_elements,
                std::vector<std::pair<expr*, int>> rhs_elements,
                std::vector<Arrangment> tmp,
                std::vector<Arrangment> &possibleCases);

            /*
             *
             */
            Arrangment manuallyCreate_arrangment(
                std::vector<std::pair<expr*, int>> lhs_elements,
                std::vector<std::pair<expr*, int>> rhs_elements);

            bool passNotContainMapReview(
                Arrangment a,
                std::vector<std::pair<expr*, int>> lhs_elements,
                std::vector<std::pair<expr*, int>> rhs_elements);

            /*
             * a_1 + a_2 + b_1 + b_2 = c_1 + c_2 + d_1 + d_2 ---> SMT
             */
            expr* generateSMT(int p,
                                            std::vector<int> left_arr,
                                            std::vector<int> right_arr,
                                            std::string lhs_str, std::string rhs_str,
                                            std::vector<std::pair<expr*, int>> lhs_elements,
                                            std::vector<std::pair<expr*, int>> rhs_elements,
                                            std::map<expr*, int> connectedVariables);
            /*
             * Flat = sum (flats)
             */
            expr* generateConstraint02(
                std::pair<expr*, int> a,
                std::vector<std::pair<expr*, int>> elementNames,
                std::string lhs_str, std::string rhs_str,
                int pMax,
                std::map<expr*, int> connectedVariables,
                bool optimizing);
            /*
             * Given a flat,
             * generate its size constraint
             */
            std::string generateVarSize(std::pair<expr*, int> a, std::string l_r_hs = "");
            /*
             *
             */
            std::string generateFlatIter(std::pair<expr*, int> a);
            /*
             * Given a flat,
             * generate its size constraint
             */
            std::string generateFlatSize(std::pair<expr*, int> a, std::string l_r_hs = "");

            int canBeOptimized_LHS(
                    int i, int startPos, int j,
                    std::vector<int> left_arr,
                    std::vector<int> right_arr,
                    std::vector<std::pair<std::string, int>> lhs_elements,
                    std::vector<std::pair<std::string, int>> rhs_elements);

            int canBeOptimized_RHS(
                    int i, int startPos, int j,
                    std::vector<int> left_arr,
                    std::vector<int> right_arr,
                    std::vector<std::pair<std::string, int>> lhs_elements,
                    std::vector<std::pair<std::string, int>> rhs_elements);
            /*
             * Given a flat,
             * generate its array name
             */
            std::string generateFlatArray(std::pair<expr*, int> a, std::string l_r_hs = "");
            /*
            * First base case
            */
            void handleCase_0_0_general();
            /*
             * 2nd base case [0] = (sum rhs...)
             */
            void handleCase_0_n_general(int lhs, int rhs);
            /*
             * 2nd base case (sum lhs...) = [0]
             */
            void handleCase_n_0_general(int lhs, int rhs);
            /*
             * general case
             */
            void handleCase_n_n_general(int lhs, int rhs);
            std::vector<std::pair<std::string, int>> vectorExpr2vectorStr(std::vector<std::pair<expr*, int>> v);
            std::string expr2str(expr* node);
            /*
             * Create a general value that the component belongs to
             */
            std::string sumStringVector(expr* node);
            std::string sumStringVector(ptr_vector<expr> list);
            std::string sumStringVector(std::vector<expr*> list);
            /*
             * extra variables
             */
            std::vector<expr*> createSetOfFlatVariables(int flatP, std::map<expr*, int> &importantVars);
            /*
             * Input: x . y
             * Output: flat . flat . flat . flat . flat . flat
             */
            std::vector<std::pair<expr*, int>> createEquality(expr* node);
            std::vector<std::pair<expr*, int>> createEquality(ptr_vector<expr> list);
            std::vector<std::pair<expr*, int>> createEquality(std::vector<expr*> list);
            std::vector<expr*> set2vector(std::set<expr*> s);
            unsigned findMaxP(std::vector<expr*> v);
            /*
             * cut the same prefix and suffix
             */
            void optimizeEquality(
                    expr* lhs,
                    expr* rhs,
                    ptr_vector<expr> &new_lhs,
                    ptr_vector<expr> &new_rhs);
            std::set<std::pair<expr*, int>> collect_important_vars(std::set<expr*> eqc_roots);
                bool is_importantVar(
                    expr* nn,
                    std::set<expr*> eqc_roots,
                    int &len);
            void print_all_assignments();
            std::map<expr*, std::set<expr*>> collect_inequalities_nonmembership(); // should be removed
            std::map<expr*, std::set<expr*>> construct_eq_combination(std::set<std::pair<expr*, int>> importantVars);
                std::set<expr*> extend_object(
                    expr* object,
                    std::map<expr*, std::set<expr*>> &combinations,
                    std::set<expr*> parents,
                    std::set<std::pair<expr*, int>> importantVars);
        bool can_propagate() override;
        void propagate() override;
        void init_model(model_generator& m) override;
        void finalize_model(model_generator& mg) override;

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
        void check_regex_in(expr * nn1, expr * nn2);
            void check_regex_in_lhs_rhs(expr * nn1, expr * nn2);
                expr* construct_concat_overapprox(expr* nn, expr_ref_vector & litems);
        void propagate_contain_in_new_eq(expr * n1, expr * n2);
        void check_contain_by_eqc_val(expr * varNode, expr * constNode);
        void check_contain_by_substr(expr * varNode, expr_ref_vector & willEqClass);
        bool in_contain_idx_map(expr * n);
        void check_contain_by_eq_nodes(expr * n1, expr * n2);
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
        void instantiate_axiom_prefixof(enode * e);
        void instantiate_axiom_suffixof(enode * e);
        void instantiate_axiom_contains(enode * e);
        void instantiate_axiom_charAt(enode * e);
        void instantiate_axiom_indexof(enode * e);
        void instantiate_axiom_indexof_extended(enode * _e);
        void instantiate_axiom_substr(enode * e);
        void instantiate_axiom_replace(enode * e);
        void instantiate_axiom_regexIn(enode * e);

        app * mk_fresh_const(char const* name, sort* s);
        app * mk_strlen(expr * e);
        expr * mk_string(zstring const& str);
        expr * mk_string(const char * str);
        app * mk_str_var(std::string name);
        expr * mk_concat(expr * n1, expr * n2);
        expr * mk_concat_const_str(expr * n1, expr * n2);
        app * mk_int(int n);
        app * mk_int(rational & q);
        app * mk_contains(expr * haystack, expr * needle);
        app * mk_indexof(expr * haystack, expr * needle);
        app * mk_int_var(std::string name);
        app * mk_regex_rep_var();
        expr * mk_regexIn(expr * str, expr * regexp);
        app * mk_unroll(expr * n, expr * bound);
        app * mk_unroll_bound_var();
        app * mk_str_to_re(expr *);
        app * mk_arr_var(std::string name);

        void get_nodes_in_concat(expr * node, ptr_vector<expr> & nodeList);
        expr * get_eqc_value(expr * n, bool & hasEqcValue);
        expr * z3str2_get_eqc_value(expr * n , bool & hasEqcValue);
        expr * get_eqc_next(expr * n);

        theory_var get_var(expr * n) const;
        app * get_ast(theory_var v);
        zstring get_std_regex_str(expr * regex);
        bool get_len_value(expr* e, rational& val);
        bool get_arith_value(expr* e, rational& val) const;
        void get_concats_in_eqc(expr * n, std::set<expr*> & concats);
        /*
         * Collect constant strings (from left to right) in an AST node.
         */
        void get_const_str_asts_in_node(expr * node, expr_ref_vector & astList);
        /*
        * Collect constant strings (from left to right) in an AST node.
        */
        void get_const_regex_str_asts_in_node(expr * node, expr_ref_vector & astList);

        /*
         * Collect important vars in AST node
         */
        void get_important_asts_in_node(expr * node, std::set<std::pair<expr*, int>> importantVars, expr_ref_vector & astList);
        eautomaton* get_automaton(expr* re);

        void track_variable_scope(expr * var);
        expr * rewrite_implication(expr * premise, expr * conclusion);
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
        static const int QCONSTMAX = 2;
        static const int QMAX = 2;
        static const int PMAX = 2;
        const std::string FLATPREFIX = "__flat_";
        int noFlatVariables = 0;
        bool trivialUnsat = false;


        std::map<expr*, int> varPieces;
        std::set<std::string> generatedEqualities;

        std::map<std::pair<int, int>, std::vector<Arrangment>> arrangements;
        std::map<expr*, std::string> constMap;

        std::map<expr*, std::vector<expr*>> lenMap;
        std::map<expr*, std::vector<expr*>> iterMap;
        std::map<expr*, expr*> arrMap;

    private:
        void assert_axiom(expr *e);
        void dump_assignments();
        const bool is_theory_str_term(expr *e) const;
        decl_kind get_decl_kind(expr *e) const;
        str::word_term get_word_term(expr *e) const;
        str::state build_state_from_memo() const;
        const bool block_dpllt_assignment_from_memo();
        void set_up_axioms(expr * ex);
    };

}

#endif /* _THEORY_STR_H_ */
