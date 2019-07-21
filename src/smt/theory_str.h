#ifndef _THEORY_STR_H_
#define _THEORY_STR_H_

#include <list>
#include <set>
#include <stack>
#include <map>
#include <vector>
#include "ast/arith_decl_plugin.h"
#include "ast/array_decl_plugin.h"
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

            std::set<word_equation> m_wes_to_satisfy;
            std::set<word_equation> m_wes_to_fail;
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
        scoped_vector<expr_ref> mful_scope_levels;
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
                    STRACE("str", tout << left_arr[i] << " ";);

                STRACE("str", tout << std::endl;);
                for (unsigned int i = 0; i < right_arr.size(); ++i)
                    STRACE("str", tout << right_arr[i] << " ";);
                STRACE("str", tout <<  std::endl;);
            }
        };

        class UnderApproxState{
        public:
            std::map<expr*, std::set<expr*>> eq_combination;
            std::set<std::pair<expr*, int>> importantVars;
            expr_ref_vector equalities;
            expr_ref_vector disequalities;
            str::state currState;
            bool reassertEQ = false;
            bool reassertDisEQ = false;
            int eqLevel = -1;
            int diseqLevel = -1;
            expr_ref_vector assertingConstraints;
            rational str_int_bound;

            UnderApproxState(ast_manager &m) : equalities(m), assertingConstraints(m), disequalities(m){

            }

            UnderApproxState(ast_manager &m, int _eqLevel, int _diseqLevel,
                            std::map<expr*, std::set<expr*>> _eq_combination,
                            std::set<std::pair<expr*, int>> _importantVars,
                            expr_ref_vector _equalities,
                            expr_ref_vector _disequalities,
                            str::state _currState,
                            rational _str_int_bound):

                            eqLevel(_eqLevel),
                            eq_combination(_eq_combination),
                            diseqLevel(_diseqLevel),
                            importantVars(_importantVars),
                            equalities(m),
                            disequalities(m),
                            assertingConstraints(m),
                            currState(_currState),
                            str_int_bound(_str_int_bound){
                assertingConstraints.reset();
                equalities.reset();
                equalities.append(_equalities);
                disequalities.reset();
                disequalities.append(_disequalities);
                reassertEQ = true;
                reassertDisEQ = true;
            }

            UnderApproxState clone(ast_manager &m){
                UnderApproxState tmp(m, eqLevel, diseqLevel, eq_combination, importantVars, equalities, disequalities, currState, str_int_bound);
                tmp.addAssertingConstraints(assertingConstraints);
                reassertEQ = true;
                reassertDisEQ = true;
                return tmp;
            }

            void reset_eq(){
                STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ <<  ": eqLevel = " << eqLevel << "; diseqLevel = " << diseqLevel << std::endl;);
                eqLevel = -1;
                reassertEQ = false;
            }

            void reset_diseq(){
                STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ <<  ": eqLevel = " << eqLevel << "; diseqLevel = " << diseqLevel << std::endl;);
                diseqLevel = -1;
                reassertDisEQ = false;
            }

            UnderApproxState&  operator=(const UnderApproxState& other){
                eqLevel = other.eqLevel;
                diseqLevel = other.diseqLevel;
                eq_combination = other.eq_combination;
                importantVars = other.importantVars;

                equalities.reset();
                equalities.append(other.equalities);

                disequalities.reset();
                disequalities.append(other.disequalities);

                currState = other.currState;
                assertingConstraints.reset();
                reassertEQ = true;
                reassertDisEQ = true;
                for (int i = 0; i < other.assertingConstraints.size(); ++i)
                    assertingConstraints.push_back(other.assertingConstraints[i]);

                STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << ":  eq_combination: " << other.eq_combination.size() << " --> " << eq_combination.size() << std::endl;);
                return *this;
            }

            void addAssertingConstraints(expr_ref_vector _assertingConstraints){
                for (int i = 0; i < _assertingConstraints.size(); ++i)
                    assertingConstraints.push_back(_assertingConstraints.get(i));
            }

            void addAssertingConstraints(expr_ref assertingConstraint){
                assertingConstraints.push_back(assertingConstraint);
            }

            bool operator==(const UnderApproxState state){
                std::map<expr*, std::set<expr*>> _eq_combination = state.eq_combination;
                STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << std::endl;);
                if (_eq_combination.size() != eq_combination.size()) {
                    STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << ": " << _eq_combination.size() << " vs " << eq_combination.size() <<  std::endl;);
                    return false;
                }

//                if (state.importantVars.size() != importantVars.size()) {
//                    STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << ": " << state.importantVars.size() << " vs " << importantVars.size() <<  std::endl;);
//                    return false;
//                }

                for (const auto& v : importantVars)
                    if (state.importantVars.find(v) == state.importantVars.end()) {
                        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << std::endl;);
                        return false;
                    }

                for (const auto& n : eq_combination) {
                    if (_eq_combination.find(n.first) == _eq_combination.end()) {
                        STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << std::endl;);
                        return false;
                    }
                    std::set<expr*> tmp = _eq_combination[n.first];
                    for (const auto &e : n.second) {

                        if (tmp.find(e) == tmp.end()) {
                            STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << std::endl;);
                            return false;
                        }
                        else {
                            // it is ok if some elements missing because if its size = 0
                        }
                    }
                }
                STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << ": Equal. " << std::endl;);
                return true;
            }
        };

        class string_value_proc : public model_value_proc {
            theory_str&                     th;
            sort*                           m_sort;
            svector<model_value_dependency> m_dependencies;
            app*                            node;
            enode*                          arr_node;
            bool                            importantVar;
            expr*                           regex;
            int                             len;
        public:

            string_value_proc(theory_str& th, sort * s, app* node, bool importantVar, enode* arr_node, expr* regex, int len = -1):
                    th(th),
                    m_sort(s),
                    node(node),
                    arr_node(arr_node),
                    importantVar(importantVar),
                    regex(regex),
                    len(len){
            }

            string_value_proc(theory_str& th, sort * s, app* node, bool importantVar, expr* regex, int len = -1):
                    th(th),
                    m_sort(s),
                    node(node),
                    importantVar(importantVar),
                    regex(regex),
                    len(len){
            }

            ~string_value_proc() override {}

            void add_entry(unsigned num_args, enode * const * args, enode * value) {
                SASSERT(num_args > 0);
                for (unsigned i = 0; i < num_args; i++)
                    m_dependencies.push_back(model_value_dependency(args[i]));
                m_dependencies.push_back(model_value_dependency(value));
            }

            void add_entry(enode * value){
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ":"  << mk_pp(node, th.get_manager()) << " --> " << mk_pp(value->get_owner(), th.get_manager()) << std::endl;);
                m_dependencies.push_back(model_value_dependency(value));
            }

            void get_dependencies(buffer<model_value_dependency> & result) override {
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__  << " " << mk_pp(node, th.get_manager()) << std::endl;);
                result.append(m_dependencies.size(), m_dependencies.c_ptr());
            }

            app * mk_value(model_generator & mg, ptr_vector<expr> & values) override {
                // values must have size = m_num_entries * (m_dim + 1) + ((m_else || m_unspecified_else) ? 0 : 1)
                // an array value is a lookup table + else_value
                // each entry has m_dim indexes that map to a value.
                ast_manager & m = mg.get_manager();
                obj_map<enode, app *> m_root2value = mg.get_root2value();
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ":"  << mk_pp(node, m) << std::endl;);

                for (int i = 0; i < m_dependencies.size(); ++i){
                    app* val = nullptr;
                    if (m_root2value.find(m_dependencies[i].get_enode(), val)) {
                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ":"  << mk_pp(m_dependencies[i].get_enode()->get_owner(), m) << " " << mk_pp(val, m) << std::endl;);
                    }
                    else
                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ":"  << mk_pp(m_dependencies[i].get_enode()->get_owner(), m) << " no value " << std::endl;);
                }


                sort * int_sort = m.mk_sort(th.m_autil.get_family_id(), INT_SORT);
                sort * str_sort = th.u.str.mk_string_sort();
                sort * arr_sort = th.m_arrayUtil.mk_array_sort(int_sort, int_sort);
                bool is_string = str_sort == m_sort;



                if (is_string) {
                    int len_int = len;
                    if (len_int != -1) {
                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": len : " << len_int << std::endl;);
                        if (importantVar) {
                            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": important" << std::endl;);
                            if (len_int != -1) {
                                zstring strValue;
                                if (constructStrFromArray(mg, m_root2value, arr_node, len_int, strValue)) {

                                }
                                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": value = \"" << strValue << "\""
                                                   << std::endl;);
                                return to_app(th.mk_string(strValue));
                            }
                        }

                        if (regex != nullptr) {
                            zstring strValue;
                            if (fetchValueFromDepGraph(mg, m_root2value, len_int, strValue))
                                return to_app(th.mk_string(strValue));
                            if (constructFromRegex(mg, len_int, m_root2value, strValue)) {
                                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": regex value = \"" << strValue << "\""
                                                   << std::endl;);
                                return to_app(th.mk_string(strValue));
                            }
                        }

                        zstring strValue;
                        constructAsNormal(mg, len_int, m_root2value, strValue);
                        return to_app(th.mk_string(strValue));
                    }
                    else {
                        STRACE("str",
                               tout << __LINE__ << " " << __FUNCTION__
                                    << mk_pp(node, m)
                                    << std::endl;);
                        SASSERT(false);
                    }
                }

                else {
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": not string: "  << mk_pp(node, m) << std::endl;);
                }

                return node;
            }

            bool constructFromRegex(model_generator & mg, int len_int, obj_map<enode, app *> m_root2value, zstring& strValue){
                ast_manager & m = mg.get_manager();
                std::vector<zstring> elements = collectAlternativeComponents(regex);
                if (th.u.re.is_union(regex)) {
                    SASSERT(elements.size() > 0);
                    for (int i = 0; i < elements.size(); ++i) {
                        if (elements[i].length() == len_int){
                            strValue = elements[i];
                            return true;
                        }
                    }

                    return false;
                }
                else if (th.u.re.is_to_re(regex)) {
                    SASSERT(elements.size() == 1);
                    SASSERT(elements[0].length() == len_int);
                    strValue = elements[0];
                    return true;
                }
                else if (th.u.re.is_star(regex) || th.u.re.is_plus(regex)) {
                    zstring valueStr("");
                    for (int i = 0; i < elements.size(); ++i) {
                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " "  << elements[i] << std::endl;);
                    }
                    if (createStringWithLength(elements, valueStr, len_int)) {
                        strValue = valueStr;
                        return true;
                    }
                    else
                        return false;
                }
                return false;
            }

            bool createStringWithLength(std::vector<zstring> elements, zstring &currentStr, int remainLength){
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": currentStr: "  << currentStr << std::endl;);
                if (remainLength == 0)
                    return true;

                for (const auto& s : elements) {
                    if (s.length() <= remainLength) {
                        int x = remainLength / s.length();
                        int bak_len = currentStr.length();
                        for (int j = 0; j < x; ++j)
                            currentStr  = currentStr + s;

                        if (remainLength % s.length() == 0) {
                            return true;
                        }
                        else {
                            int tmpRemainLength = remainLength % s.length();
                            while (currentStr.length() > bak_len) {
                                if (createStringWithLength(elements, currentStr, tmpRemainLength)) {
                                    return true;
                                } else {
                                    currentStr = currentStr.extract(0, currentStr.length() - s.length());
                                    tmpRemainLength += s.length();
                                }
                            }
                        }
                    }
                }

                return false;
            }

            std::vector<zstring> collectAlternativeComponents(expr* v){
                std::vector<zstring> result;
                collectAlternativeComponents(v, result);
                return result;
            }


            void collectAlternativeComponents(expr* v, std::vector<zstring>& ret){
                if (th.u.re.is_to_re(v)){
                    expr* arg0 = to_app(v)->get_arg(0);
                    zstring tmpStr;
                    th.u.str.is_string(arg0, tmpStr);
                    ret.push_back(tmpStr);
                }
                else if (th.u.re.is_union(v)){
                    expr* arg0 = to_app(v)->get_arg(0);
                    collectAlternativeComponents(arg0, ret);
                    expr* arg1 = to_app(v)->get_arg(1);
                    collectAlternativeComponents(arg1, ret);
                }
                else if (th.u.re.is_star(v) || th.u.re.is_plus(v)) {
                    expr* arg0 = to_app(v)->get_arg(0);
                    collectAlternativeComponents(arg0, ret);
                }
                else
                    SASSERT(false);
            }

            bool constructAsNormal(model_generator & mg, int len_int, obj_map<enode, app *> m_root2value, zstring& strValue){
                ast_manager & m = mg.get_manager();
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(node, m)  << ": NOT important" << std::endl;);
                if (len_int != -1) {
                    // non root var
                    bool constraint01 =
                            th.uState.eq_combination.find(node) == th.uState.eq_combination.end();
                    bool constraint02 = (th.backwardDep.find(node) != th.backwardDep.end() && th.backwardDep[node].size() > 0);
                    if (constraint01 || constraint02) {
                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": case non root" << (constraint01 ? " true " : "false ") << (constraint02 ? " true " : "false ") << std::endl;);
                        if (!constraint02) {
                            // free var
                            for (int i = 0; i < len_int; ++i)
                                strValue = strValue + th.defaultChar;
                            STRACE("str",
                                   tout << __LINE__ << " " << __FUNCTION__ << ": value = " << strValue
                                        << std::endl;);
                            return to_app(th.mk_string(strValue));
                        } else {
                            if (fetchValueFromDepGraph(mg, m_root2value, len_int, strValue))
                                return to_app(th.mk_string(strValue));
                        }
                    } else {
                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": case root" << std::endl;);
                        // root var
                        std::vector<int> val;
                        for (int i = 0; i < len_int; ++i)
                            val.push_back(-1);

                        if (th.u.str.is_concat(node))
                            constructStr(mg, node, m_root2value, val);

                        for (const auto &eq : th.uState.eq_combination[node]) {
                            constructStr(mg, eq, m_root2value, val);
                        }

                        for (int i = 0; i < len_int; ++i)
                            if (val[i] == -1) {
                                strValue = strValue + th.defaultChar;
                            } else
                                strValue = strValue + val[i];

                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": value = " << strValue
                                           << std::endl;);
                        return to_app(th.mk_string(strValue));
                    }
                }
                else {
                    STRACE("str",
                           tout << __LINE__ << " " << __FUNCTION__
                                << mk_pp(node, m)
                                << std::endl;);
                    SASSERT(false);
                }

                return false;
            }

            bool constructStrFromArray(model_generator mg, obj_map<enode, app *> m_root2value, enode* arr, int len_int, zstring &val){
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << std::endl;);

                app* arr_val = nullptr;
                if (m_root2value.find(arr, arr_val)) {
                    std::vector<int> vValue (len_int, -1);

                    func_decl * fd = to_func_decl(arr_val->get_parameter(0).get_ast());
                    func_interp* fi = mg.get_model().get_func_interp(fd);

                    unsigned num_entries = fi->num_entries();
                    for(unsigned i = 0; i < num_entries; i++)
                    {
                        func_entry const* fe = fi->get_entry(i);
                        expr* k =  fe->get_arg(0);
                        rational key;
                        if (th.m_autil.is_numeral(k, key)) {
                            expr* v =  fe->get_result();

                            rational value;
                            if (th.m_autil.is_numeral(v, value)) {
                                if (key.get_int32() < vValue.size())
                                    vValue[key.get_int32()] = value.get_int32();
                            }
                        }
                    }

                    bool completed = true;
                    zstring value;
                    for (int i = 0; i < vValue.size(); ++i) {
                        if (vValue[i] <= 0 || vValue[i] >= 128) {
                            value = value + th.defaultChar;
                            completed = false;
                        }
                        else
                            value = value + (char) vValue[i];
                    }

                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " value: "  << mk_pp(node, th.get_manager()) << " " << value << std::endl;);
                    val = value;
                    if (completed == false) {
                        return false;
                    }


                    return true;
                }



                return false;
            }

            void constructStr(model_generator & mg, expr* eq, obj_map<enode, app *> m_root2value, std::vector<int> &val){
                if (th.u.str.is_concat(eq)){
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": sync"  << mk_pp(eq, th.get_manager()) << std::endl;);
                    ptr_vector<expr> leafNodes;
                    th.get_nodes_in_concat(eq, leafNodes);

                    int sum = 0;
                    for (int i = 0; i < leafNodes.size(); ++i){
                        if (th.is_important(leafNodes[i]) || th.u.str.is_string(leafNodes[i]) || th.is_regex_var(leafNodes[i])){
                            zstring leafVal;

                            if (getStrValue(th.get_context().get_enode(leafNodes[i]), m_root2value, leafVal)){
                                int len_int = leafVal.length();
                                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": updating by: "  << mk_pp(leafNodes[i], th.get_manager())  << " = " << leafVal << std::endl;);
                                for (int j = sum; j < sum + len_int; ++j) {
                                    if (val[j] == -1) {
                                        val[j] = leafVal[j - sum];
                                    } else {
                                        if (val[j] != (int) leafVal[j - sum]) {
                                            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": val: " << val[j]
                                                               << std::endl;);
                                            STRACE("str",
                                                   tout << __LINE__ << " " << __FUNCTION__ << ": inconsistent @" << j
                                                        << " \"" << leafVal << "\" "
                                                        << mk_pp(leafNodes[i], th.get_manager()) << std::endl;);
                                        }
                                    }
                                }
                                sum = sum + len_int;
                            }
                            else {
                                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": cannot get string: "  << mk_pp(leafNodes[i], th.get_manager()) << std::endl;);
                                SASSERT(false);
                            }
                        }
                        else {
                            int len_int = -1;
                            if (getIntValue(mg, th.get_context().get_enode(th.mk_strlen(leafNodes[i])), m_root2value, len_int)){
                                sum += len_int;
                                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": sum = "  << sum << std::endl;);
                            }
                            else {
                                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": cannot get len: "  << mk_pp(leafNodes[i], th.get_manager()) << std::endl;);
                                SASSERT(false);
                            }
                        }
                    }
                }
            }

            bool fetchValueFromDepGraph(model_generator & mg, obj_map<enode, app *> m_root2value, int len, zstring& value){
                // component var
                ast_manager & m = mg.get_manager();
                for (const auto &ancestor : th.backwardDep[node]) {
                    STRACE("str",
                           tout << __LINE__ << " " << __FUNCTION__
                                << mk_pp(ancestor, m)
                                << std::endl;);
                    zstring ancestorValue;
                    if (getStrValue(th.get_context().get_enode(ancestor), m_root2value,
                                    ancestorValue)) {
                        if (th.u.str.is_concat(ancestor)) {
                            if (fetchValueBelongToConcat(mg, ancestor, ancestorValue, m_root2value,
                                                         len, value)) {
                                return true;
                            }
                        }

                        // find in its eq
                        if (th.uState.eq_combination.find(ancestor) !=
                            th.uState.eq_combination.end()) {
                            for (const auto &ancestor_i : th.uState.eq_combination[ancestor]) {
                                if (th.u.str.is_concat(ancestor_i)) {
                                    if (fetchValueBelongToConcat(mg, ancestor_i, ancestorValue,
                                                                 m_root2value, len,
                                                                 value)) {
                                        STRACE("str",
                                               tout << __LINE__ << " " << __FUNCTION__
                                                    << ": value = " << value
                                                    << std::endl;);
                                        return true;
                                    }
                                }
                            }
                        }

                    }
                }
                return false;
            }

            bool fetchValueBelongToConcat(model_generator & mg, expr* concat, zstring concatValue,obj_map<enode, app *> m_root2value, int len, zstring& value){
                if (th.u.str.is_concat(concat)){

                    ptr_vector<expr> leafNodes;
                    th.get_all_nodes_in_concat(concat, leafNodes);

                    if (leafNodes.contains(node)) {
                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": found in "  << mk_pp(concat, th.get_manager()) << std::endl;);
                        int prefix = findPrefixLen(mg, concat, node, m_root2value);
                        value = concatValue.extract(prefix, len);
                        return true;
                    }
                    return false;
                }
                return false;
            }

            int findPrefixLen(model_generator & mg, expr* concat, expr* subNode, obj_map<enode, app *> m_root2value){

                if (th.u.str.is_concat(concat)){
                    int prefix = 0;
                    findPrefixLen(mg, concat, subNode, m_root2value, prefix);
                    return prefix;
                }
                else
                    SASSERT(false);

                return -1;
            }

            bool findPrefixLen(model_generator & mg, expr* concat, expr* subNode, obj_map<enode, app *> m_root2value, int &prefix){
                if (concat == subNode)
                    return true;
                if (th.u.str.is_concat(concat)){
                    if (!findPrefixLen(mg, to_app(concat)->get_arg(0), subNode, m_root2value, prefix)) {
                        if (!findPrefixLen(mg, to_app(concat)->get_arg(1), subNode, m_root2value, prefix))
                            return false;
                        else
                            return true;
                    }
                    else
                        return true;
                }
                else {
                    int subLen = -1;
                    if (getIntValue(mg, th.get_context().get_enode(th.mk_strlen(concat)), m_root2value, subLen)) {
                        prefix += subLen;
                    }
                    else {
                        SASSERT(false);
                    }
                }
                return false;
            }

            bool getLenValue(model_generator & mg, app* n, obj_map<enode, app *> m_root2value, int &value){
                app* len_node = nullptr;
                if (th.u.str.is_concat(n)){
                    ptr_vector<expr> leafNodes;
                    th.get_nodes_in_concat(n, leafNodes);
                    int sum = 0;
                    for (int i = 0; i < leafNodes.size(); ++i) {
                        int val = -1;
                        if (getIntValue(mg, th.get_context().get_enode(th.mk_strlen(leafNodes[i])), m_root2value, val)){
                            sum += val;
                        }
                        else
                            return false;
                        value = sum;
                    }
                    return true;
                }

                else {
                    len_node = th.mk_strlen(n);
                    return getIntValue(mg, th.get_context().get_enode(len_node), m_root2value, value);
                }
            }

            bool getIntValue(model_generator & mg, enode* n, obj_map<enode, app *> m_root2value, int &value){
                STRACE("str",
                       tout << __LINE__ << " " << __FUNCTION__
                            << mk_pp(n->get_owner(), th.get_manager())
                            << std::endl;);
                app* val = nullptr;
                if (m_root2value.find(n->get_root(), val)) {
                    rational valInt;
                    if (th.m_autil.is_numeral(val, valInt)) {
                        value = valInt.get_int32();
                        return true;
                    }
                    else {
                        STRACE("str",
                               tout << __LINE__ << " " << __FUNCTION__
                                       << mk_pp(val, th.get_manager())
                                    << std::endl;);
                        return false;
                    }
                }
                else {
                    // query int theory
                    expr *value_ral = th.query_theory_arith_core(n->get_owner(), mg);
                    if (value_ral != nullptr) {

                        rational tmp;
                        if (th.m_autil.is_numeral(value_ral, tmp)) {
                            value = tmp.get_int32();
                            return true;
                        }
                        else
                            SASSERT(false);
                    }


                    STRACE("str",
                           tout << __LINE__ << " " << __FUNCTION__
                                << std::endl;);
                    return false;
                }
            }

            bool getSelectValue(model_generator & mg, enode* n, obj_map<enode, app *> m_root2value, int &value){
                STRACE("str",
                       tout << __LINE__ << " " << __FUNCTION__
                            << mk_pp(n->get_owner(), th.get_manager())
                            << std::endl;);
                app* val = nullptr;
                if (m_root2value.find(n->get_root(), val)) {
                    rational valInt;
                    if (th.m_autil.is_numeral(val, valInt)) {
                        value = valInt.get_int32();
                        return true;
                    }
                    else {
                        STRACE("str",
                               tout << __LINE__ << " " << __FUNCTION__
                                    << mk_pp(val, th.get_manager())
                                    << std::endl;);
                        return false;
                    }
                }
                else {
                    STRACE("str",
                           tout << __LINE__ << " " << __FUNCTION__
                                << std::endl;);
                    return false;
                }
            }


            bool getStrValue(enode* n, obj_map<enode, app *> m_root2value, zstring &value){
                app* val = nullptr;
                if (m_root2value.find(n->get_root(), val)) {
                    zstring valStr;
                    if (th.u.str.is_string(val, valStr)) {
                        value = valStr;
                        return true;
                    }
                    else {
                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": cannot get string: "  << mk_pp(n->get_owner(), th.get_manager()) << std::endl;);
                        return false;
                    }
                }
                else {
                    zstring tmp;
                    if (th.u.str.is_string(n->get_owner(), tmp)) {
                        value = tmp;
                        return true;
                    }
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": cannot get string: "  << mk_pp(n->get_owner(), th.get_manager()) << std::endl;);
                    return false;
                }
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
        app * mk_value_helper(app * n, model_generator& mg);
        model_value_proc *mk_value(enode *n, model_generator& mg) override;
        bool is_important(expr* n);
        bool is_important(expr* n, int &val);
        bool is_regex_var(expr* n, expr* &regexExpr);
        bool is_regex_var(expr* n);
        bool is_regex_concat(expr* n);
        std::set<expr*> getDependency(expr* n);

        void add_theory_assumptions(expr_ref_vector& assumptions) override;
        lbool validate_unsat_core(expr_ref_vector& unsat_core) override;
        void new_eq_eh(theory_var, theory_var) override;
            /*
            * x . "abc" = x . y && y = "abc"
            */
            bool is_trivial_eq_concat(expr* x, expr* y);
        void new_diseq_eh(theory_var, theory_var) override;
            bool is_inconsistent_inequality(expr* lhs, expr* rhs);
            bool is_not_added_diseq(expr_ref n1, expr_ref n2);
            void assert_cached_diseq_state();
            void breakdown_cached_diseq(expr* n1, expr* n2);
            /*
             * Add an axiom of the form:
             * len lhs != len rhs -> lhs != rhs
             * len lhs == 0 == len rhs --> lhs == rhs
             */
            void instantiate_str_diseq_length_axiom(expr * lhs, expr * rhs, bool& skip);
                expr* handle_trivial_diseq(expr * e, zstring value);
                    std::set<zstring> extract_const(expr* e, int lvl = 0);
        void create_pq();
        void init_search_eh() override;
        void relevant_eh(app *n) override;
        void assign_eh(bool_var v, bool is_true) override;
        void push_scope_eh() override;
        void pop_scope_eh(unsigned num_scopes) override;
        void reset_eh() override;
        final_check_status final_check_eh() override;
            bool eval_str_int();
            /*
             * Check agreement between integer and string theories for the term a = (str.to-int S).
             * Returns true if axioms were added, and false otherwise.
             */
            bool eval_str2int(app * a);
            bool eval_int2str(app * a);
            void refined_init_final_check(
                std::set<std::pair<expr *, int>> &importantVars,
                std::map<expr *, std::set<expr *>> &eq_combination);
            void init_final_check(
                std::set<std::pair<expr *, int>> &importantVars,
                std::map<expr *, std::set<expr *>> &eq_combination);
                void analyze_bound_str_int();
                bool analyze_upper_bound_str_int();
                rational log_10(rational n);
                rational ten_power(rational n);
            bool is_completed_branch(bool &addAxiom);
            void update_state();
            bool propagate_eq_combination(std::map<expr *, std::set<expr *>> eq_combination);
            bool is_notContain_consistent(std::map<expr *, std::set<expr *>> eq_combination);
                bool is_notContain_consistent(expr* lhs, expr* rhs, expr* core);
                bool is_notContain_const_consistent(expr* lhs, zstring containKey, expr_ref premise);
                    bool one_const_in_expr(expr* v, expr_ref_vector constList);

            bool implies_empty_str_from_notContain(std::map<expr *, std::set<expr *>> eq_combination);
                expr_ref_vector implies_empty_tail_str_from_notContain(std::set<expr *> v, expr* key, expr* lhs);
                expr_ref_vector implies_empty_start_str_from_notContain(std::set<expr *> v, expr* key, expr* lhs);
                    bool not_contain(expr* haystack, expr* needle, expr* &realHaystack);
                    bool does_contain(expr* haystack, expr* needle, expr* &realHaystack);

            bool parikh_image_check(std::map<expr *, std::set<expr *>> eq_combination);
                bool can_match(zstring value, expr* n);
                void not_contain_string_in_expr(expr* n, expr_ref_vector &constList);
                bool agree_on_not_contain(expr* n, expr* key);
                int get_lower_bound_image_in_expr(expr* n, expr* str);
                bool get_image_in_expr(expr* n, expr_ref_vector &constList);

            int get_actual_trau_lvl();
                bool at_same_eq_state(UnderApproxState state);
                bool at_same_diseq_state(str::state curr, str::state prev);

        bool review_starting_ending_combination(std::map<expr *, std::set<expr *>> eq_combination);
            bool all_length_solved();
            std::set<char> collect_char_domain_from_concat();
            std::set<char> collect_char_domain_from_eqmap(std::map<expr *, std::set<expr *>> eq_combination);
            bool handle_contain_family(std::map<expr *, std::set<expr *>> eq_combination);
                expr* create_equations_over_contain_vars(expr* x, expr* y);
            bool handle_charAt_family(
                std::map<expr *, std::set<expr *>> eq_combination);
                bool are_equal_exprs(expr* x, expr* y);
            std::set<expr*> get_eqc_roots();
            void add_theory_aware_branching_info(expr * term, double priority, lbool phase);
            std::vector<unsigned> sort_indexes(const std::vector<std::pair<expr*, rational>> v);
            bool assignValues(model_generator& mg, const std::vector<std::pair<expr*, rational>> freeVars, std::map<expr*, rational> varLens, std::set<std::pair<expr *, int>> importantVars);
            void syncVarValue(std::map<expr*, std::vector<int>> &strValue);
            void formatConnectedVars(
                std::vector<unsigned> indexes,
                std::map<expr*, zstring> solverValues,
                std::vector<std::pair<expr*, rational>> lenVector,
                std::map<expr*, rational> len,
                std::map<expr*, int> iterInt,
                std::map<expr*, std::vector<int>> &strValue,
                std::map<expr *, int> importantVars,
                bool &completion);
            void formatOtherVars(
                std::vector<unsigned> indexes,
                std::map<expr*, zstring> solverValues,
                std::vector<std::pair<expr*, rational>> lenVector,
                std::map<expr*, rational> len,
                std::map<expr*, int> iterInt,
                std::map<expr*, std::vector<int>> &strValue,
                std::map<expr *, int> importantVars,
                bool &completion);
                std::map<expr*, int> createSimpleEqualMap(
                std::map<expr*, rational> len);
                    bool isBlankValue(expr* name,
                                      std::map<expr*, rational> len,
                                      std::map<expr*, std::vector<int>> strValue);
            std::vector<int> createString(
                expr* name,
                zstring value,
                std::map<expr*, rational> len,
                std::map<expr*, std::vector<int>> strValue,
                std::vector<std::pair<int, int>> iters,
                bool &assigned,
                bool assignAnyway = false);
            bool needValue(expr* name,
                                   std::map<expr*, rational> len,
                                   std::map<expr*, std::vector<int>> strValue);
            void syncConst(
                std::map<expr*, rational> len,
                std::map<expr*, std::vector<int>> &strValue,
                bool &completion);
            rational getVarLength(
                expr* newlyUpdate,
                std::map<expr*, rational> len);
            void forwardPropagate(
                expr* newlyUpdate,
                std::map<expr*, rational> len,
                std::map<expr*, std::vector<int>> &strValue,
                bool &completion);
            void backwardPropagarate(
                expr* newlyUpdate,
                std::map<expr*, rational> len,
                std::map<expr*, std::vector<int>> &strValue,
                bool &completion);
            void backwardPropagarate_simple(
                expr* newlyUpdate,
                std::map<expr*, rational> len,
                std::map<expr*, std::vector<int>> &strValue,
                bool &completion);
            std::vector<int> getVarValue(
                expr* newlyUpdate,
                std::map<expr*, rational> len,
                std::map<expr*, std::vector<int>> &strValue);
            bool fixedValue(std::vector<std::pair<expr*, rational>> &freeVars, std::map<expr*, rational> varLens);
            bool fixedLength(std::set<expr*> &freeVars, std::map<expr*, rational> &varLens);
            bool propagate_concat();
            bool propagate_value(std::set<expr*> & concatSet);
            bool propagate_length(std::set<expr*> & varSet, std::set<expr*> & concatSet, std::map<expr*, int> & exprLenMap);
                void collect_var_concat(expr * node, std::set<expr*> & varSet, std::set<expr*> & concatSet);
                void get_unique_non_concat_nodes(expr * node, std::set<expr*> & argSet);
                bool propagate_length_within_eqc(expr * var);
            bool underapproximation(
                std::map<expr*, std::set<expr*>> eq_combination,
                std::set<std::pair<expr*, int>> importantVars);
                bool handle_str_int();
                    void handle_str2int(expr* num, expr* str);
                    void handle_int2str(expr* num, expr* str);
                        expr* unroll_str2int(expr* n);
                        expr* unroll_str_int(expr* num, expr* str);
                        expr* lower_bound_str_int(expr* num, expr* str);
                        expr* lower_bound_int_str(expr* num, expr* str);
                        expr* fill_0_at_begining(expr* n);
                std::map<expr*, std::vector<expr*>> mapset2mapvector(std::map<expr*, std::set<expr*>> m);
                std::map<expr*, int> set2map(std::set<std::pair<expr*, int>> s);
                void print_eq_combination(std::map<expr*, std::set<expr*>> eq_combination, int line = -1);
                bool is_equal(UnderApproxState preState, UnderApproxState currState);
                    bool are_some_empty_vars_omitted(expr* n, std::set<expr*> v);
                bool is_equal(expr_ref_vector corePrev, expr_ref_vector coreCurr);
                bool is_weaker_expr_sets(expr_ref_vector a, expr_ref_vector b);
            bool underapproximation_repeat();
            void init_underapprox(std::map<expr*, std::set<expr*>> eq_combination, std::map<expr*, int> &importantVars);
                void setup_str_int_arr(expr* v, int start);
                void setup_str_const(zstring val, expr* arr);
                void setup_regex_var(expr* rexpr, expr* arr);
                void create_notcontain_map();
                void create_const_set();
                char setupDefaultChar(std::set<char> includeChars, std::set<char> excludeChars);
                std::set<char> initExcludeCharSet();
                std::set<char> initIncludeCharSet();
                void createAppearanceMap(
                        std::map<expr*, std::set<expr*>> eq_combination);
                void setup_flats();
                bool should_use_flat();
            void init_underapprox_repeat();

            void handle_diseq(bool repeat = false);
                void handle_NOTEqual();
                void handle_NOTEqual_repeat();
                    void handle_NOTEqual(expr* lhs, expr* rhs);
                    void handle_NOTEqual_const(expr* lhs, zstring rhs);
                    void handle_NOTEqual_var(expr* lhs, expr* rhs);
                void handle_NOTContain();
                void handle_NOTContain_repeat();
                    void handle_NOTContain(expr* lhs, expr* rhs);
                    void handle_NOTContain_var(expr* lhs, expr* rhs, expr* premise);
                    void handle_NOTContain_const(expr* lhs, zstring rhs, expr* premise);
                    bool is_contain_equality(expr* n);
                    bool is_contain_equality(expr* n, expr* &contain);
                    bool is_trivial_contain(zstring s);
                void  init_connecting_size(std::map<expr*, std::set<expr*>> eq_combination, std::map<expr*, int> &importantVars, bool prep = true);
                    void static_analysis(std::map<expr*, std::set<expr*>> eq_combination);
            bool convert_equalities(std::map<expr*, std::vector<expr*>> eq_combination,
                                           std::map<expr*, int> importantVars,
                                           expr* premise);
                void assert_breakdown_combination(expr* e, expr* premise, expr_ref_vector &assertedConstraints, bool &axiomAdded);
                void assert_breakdown_combination(expr* e, expr* var);
                void negate_context();
                void negate_context(expr* e);
                void negate_context(expr_ref_vector v);
                expr* find_equivalent_variable(expr* e);
                bool isInternalVar(expr* e);
                std::vector<expr*> createExprFromRegexVector(std::vector<zstring> v);
                bool isInternalRegexVar(expr* e, expr* &regex);
                /*
                * (abc)*__XXX -> abc
                */
                zstring parse_regex_content(zstring str);
                zstring parse_regex_content(expr* str);
                /*
                 * a b c (abc)* --> abc (abc)*
                 */
                std::vector<std::vector<zstring>> combineConstStr(std::vector<std::vector<zstring>> regexElements);
                    bool isRegexStr(zstring str);
                    bool isUnionStr(zstring str);
                /*
                 * remove duplication
                 */
                std::vector<std::vector<zstring>> refineVectors(std::vector<std::vector<zstring>> list);
                    /*
                    *
                    */
                    bool equalStrVector(std::vector<zstring> a, std::vector<zstring> b);

                /*
                *
                */
                std::vector<std::vector<zstring>> parse_regex_components(zstring str);
                    /**
                     * (abc|cde|ghi)*
                     */
                    void optimizeFlatAutomaton(zstring &s);

                    /*
                    * (a)|(b | c) --> {a, b, c}
                    */
                    std::set<zstring> extendComponent(zstring s);

                    /*
                    * (a) | (b) --> {a, b}
                    */
                    std::vector<zstring> collectAlternativeComponents(zstring str);
                    std::vector<zstring> collectAlternativeComponents(expr* v);
                    bool collectAlternativeComponents(expr* v, std::vector<zstring>& ret);

                    /*
                    *
                    */
                    int find_correspond_right_parentheses(int leftParentheses, zstring str);

                    /*
                    * (a) --> a
                    */
                    void removeExtraParentheses(zstring &s);

                std::set<zstring> collect_strs_in_membership(expr* v);
                void collect_strs_in_membership(expr* v, std::set<zstring> &ret);
                zstring underApproxRegex(zstring str);
                zstring getStdRegexStr(expr* regex);
            /*
             * convert lhs == rhs to SMT formula
             */
            expr* equality_to_arith(
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
            expr_ref_vector collect_all_possible_arrangements(
                std::string lhs_str, std::string rhs_str,
                std::vector<std::pair<expr*, int>> lhs_elements,
                std::vector<std::pair<expr*, int>> rhs_elements,
                std::map<expr*, int> connectedVariables,
                int p = PMAX);

            void update_possible_arrangements(
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

            bool passSelfConflict(
                Arrangment a,
                std::vector<std::pair<expr*, int>> lhs_elements,
                std::vector<std::pair<expr*, int>> rhs_elements);
            /*
             * a_1 + a_2 + b_1 + b_2 = c_1 + c_2 + d_1 + d_2 ---> SMT
             */
            expr* generate_smt(int p,
                                            std::vector<int> left_arr,
                                            std::vector<int> right_arr,
                                            std::string lhs_str, std::string rhs_str,
                                            std::vector<std::pair<expr*, int>> lhs_elements,
                                            std::vector<std::pair<expr*, int>> rhs_elements,
                                            std::map<expr*, int> connectedVariables);

            /*
             *
             * Flat = empty
             */

            expr* generate_constraint00(
                    std::pair<expr*, int> a,
                    std::string l_r_hs);

            /*
             * Flat = Flat
             * size = size && it = it  ||
             * size = size && it = 1
             */
            expr* generate_constraint01(
                    std::string lhs_str, std::string rhs_str,
                    std::pair<expr*, int> a, std::pair<expr*, int> b,
                    int pMax,
                    std::map<expr*, int> connectedVariables,
                    bool optimizing);

            expr* generate_constraint_var_var(
                std::pair<expr*, int> a,
                std::pair<expr*, int> b,
                int pMax,
                rational bound);

            expr* generate_constraint_var_var(
                std::pair<expr*, int> a,
                std::vector<std::pair<expr*, int>> elementNames,
                int pos,
                int pMax,
                rational bound);

            expr* generate_constraint_flat_var(
                std::pair<expr*, int> a,
                std::vector<std::pair<expr*, int>> elementNames,
                int pos,
                int pMax,
                rational bound);

            expr* generate_constraint_flat_flat(
                std::pair<expr*, int> a,
                std::vector<std::pair<expr*, int>> elementNames,
                int pos,
                int pMax,
                rational bound);
            int lcd(int x, int y);
            bool matchRegex(expr* a, zstring b);
            bool matchRegex(expr* a, expr* b);
            /*
             * Flat = sum (flats)
             */
            expr* generate_constraint02(
                std::pair<expr*, int> a,
                std::vector<std::pair<expr*, int>> elements,
                std::string lhs_str, std::string rhs_str,
                int pMax,
                std::map<expr*, int> connectedVariables,
                bool optimizing);

                /*
                * Input: split a string
                * Output: SMT
                */
                expr* toConstraint_havingConnectedVar_andConst(
                        std::pair<expr*, int> a, /* const || regex */
                        std::vector<std::pair<expr*, int> > elementNames, /* const + connected var */
                        std::vector<int> split,
                        std::string lhs, std::string rhs,
                        std::map<expr*, int> connectedVariables,
                        bool optimizing,
                        int pMax);

                    /*
                    *
                    */
                    expr* lengthConstraint_toConnectedVarConstraint(
                            std::pair<expr*, int> a, /* const || regex */
                            std::vector<std::pair<expr*, int> > elementNames,
                            expr_ref_vector subElements,
                            int currentPos,
                            int subLength,
                            std::string lhs, std::string rhs,
                            std::map<expr*, int> connectedVariables,
                            bool optimizing,
                            int pMax);

                        /*
                        *
                        */
                        expr_ref connectedVar_atSpecificLocation(
                                std::pair<expr*, int> a, /* const or regex */
                                std::vector<std::pair<expr*, int>> elementNames, /* have connected var */
                                int connectedVarPos,
                                int connectedVarLength,
                                std::string lhs, std::string rhs,
                                std::map<expr*, int> connectedVariables,
                                bool optimizing,
                                int pMax);
                /*
                 * Input: split a string
                 * Output: SMT
                 */
                expr_ref_vector toConstraint_NoConnectedVar(
                        std::pair<expr*, int> a, /* const || regex */
                        std::vector<std::pair<expr*, int> > elementNames, /* no connected var */
                        std::vector<int> split,
                        std::string lhs, std::string rhs,
                        bool optimizing);
                /*
                 *
                 */
                expr* unroll_connected_variable(
                        std::pair<expr*, int> a, /* connected variable */
                        std::vector<std::pair<expr*, int> > elementNames, /* contain const */
                        std::string lhs_str, std::string rhs_str,
                        std::map<expr*, int> connectedVariables,
                        bool optimizing,
                        int pMax = PMAX);
                    /*
                     * Generate constraints for the case
                     * X = T . "abc" . Y . Z
                     * constPos: position of const element
                     * return: (or (and length header = i && X_i = a && X_[i+1] = b && X_[i+2] = c))
                     */
                    expr_ref handle_SubConst_WithPosition_array(
                            std::pair<expr*, int> a, // connected var
                            std::vector<std::pair<expr*, int>> elementNames,
                            std::string lhs_str, std::string rhs_str,
                            int constPos,
                            bool optimizing,
                            int pMax = PMAX);

                        /*
                        * Generate constraints for the case
                        * X = T . "abc"* . Y . Z
                        * regexPos: position of regex element
                        * return: forAll (i Int) and (i < |abc*|) (y[i + |T|] == a | b | c)
                        */
                        expr_ref handle_Regex_WithPosition_array(
                                std::pair<expr*, int> a, // connected var
                                std::vector<std::pair<expr*, int>> elementNames,
                                int regexPos,
                                bool optimizing,
                                int pMax = PMAX,
                                expr* extraConstraint = NULL/* length = ? */
                        );

                        /*
                        * Generate constraints for the case
                        * X = T . "abc" . Y . Z
                        * constPos: position of const element
                        * return: (or (and length header = i && X_i = a && X_[i+1] = b && X_[i+2] = c))
                        */
                        expr_ref handle_Const_WithPosition_array(
                                std::pair<expr*, int> a,
                                std::vector<std::pair<expr*, int>> elementNames,
                                std::string lhs_str, std::string rhs_str,
                                int constPos,
                                zstring value, /* value of regex */
                                int start, int finish,
                                bool optimizing,
                                int pMax = PMAX,
                                expr* extraConstraint = NULL /* length = ? */);

                    /*
                    * connected = a + connected + b
                    */
                    expr* handle_connected_connected_array(
                            std::pair<expr*, int> a,
                            std::vector<std::pair<expr*, int>> elementNames,
                            int pos,
                            int bound,
                            bool optimizing,
                            int pMax = PMAX);

                /*
                 *
                 */
                expr* toConstraint_ConnectedVar(
                        std::pair<expr*, int> a, /* const or regex */
                        std::vector<std::pair<expr*, int>> elementNames, /* have connected var, do not have const */
                        std::map<expr*, int> connectedVariables,
                        bool optimizing,
                        int pMax);
                /*
                 * elementNames[pos] is a connected.
                 * how many parts of that connected variable are in the const | regex
                 */
                expr* find_partsOfConnectedVariablesInAVector(
                        int pos,
                        std::vector<std::pair<expr*, int>> elementNames,
                        int &partCnt);
                /*
                * pre elements + pre fix of itself
                */
                expr* leng_prefix_lhs(std::pair<expr*, int> a,
                                          std::vector<std::pair<expr*, int>> elementNames,
                                          int pos,
                                          bool optimizing,
                                          bool unrollMode);

                /*
                *  pre fix of itself
                */
                expr* leng_prefix_rhs(
                        std::pair<expr*, int> a, /* var */
                        bool unrollMode);

                /*
                 * 0: No const, No connected var
                * 1: const		No connected var
                * 2: no const, connected var
                * 3: have both
                */
                int findSplitType(
                        std::vector<std::pair<expr*, int>> elementNames,
                        std::map<expr*, int> connectedVariables);

                /*
                * Input: constA and a number of flats
                * Output: all possible ways to split constA
                */
                std::vector<std::vector<int> > collectAllPossibleSplits(
                        std::pair<expr*, int> lhs,
                        std::vector<std::pair<expr*, int> > elementNames,
                        bool optimizing);

                /*
                * textLeft: length of string
                * nMax: number of flats
                * pMax: size of a flat
                *
                * Pre-Condition: 1st flat and n-th flat must be greater than 0
                * Output: of the form 1 * 1 + 1 * 0 + 1 * 0 + 1 * 0 + 1 * 0 + 1 * 0 + 1 * 0 + 1 * 0 + 1 * 3 + 2 * 3 = 10
                */
                void collectAllPossibleSplits_const(
                        int pos,
                        zstring str, /* const */
                        int pMax,
                        std::vector<std::pair<expr*, int> > elementNames,
                        std::vector<int> currentSplit,
                        std::vector<std::vector<int> > &allPossibleSplits
                );

                /*
                * (a|b|c)*_xxx --> range <a, c>
                */
                std::vector<std::pair<int, int>> collectCharRange(expr* a);
                void collectCharRange(expr* a, std::vector<bool> &chars);

                bool feasibleSplit_const(
                        zstring str,
                        std::vector<std::pair<expr*, int> > elementNames,
                        std::vector<int> currentSplit);
            /*
             * Given a flat,
             * generate its size constraint
             */
            std::string generateVarSize(std::pair<expr*, int> a, std::string l_r_hs = "");
            expr* getExprVarSize(std::pair<expr*, int> a);
            /*
             *
             */
            std::string generateFlatIter(std::pair<expr*, int> a);
            expr* getExprVarFlatIter(std::pair<expr*, int> a);
            /*
             * Given a flat,
             * generate its size constraint
             */
            std::string generateFlatSize(std::pair<expr*, int> a, std::string l_r_hs = "");
            expr* getExprVarFlatSize(std::pair<expr*, int> a);

            /*
             *
             */
            app* createEqualOperator(expr* x, expr* y);

            /*
             *
             */
            app* createMultiplyOperator(expr* x, expr* y);

            /*
             *
             */
            app* createModOperator(expr* x, expr* y);

            /*
             *
             */
            app* createMinusOperator(expr* x, expr* y);

            /*
             *
             */
            app* createAddOperator(expr* x, expr* y);

            /*
             *
             */
            app* createAddOperator(expr_ref_vector adds);
            /*
             *
             */
            app* createLessOperator(expr* x, expr* y);

            /*
             *
             */
            app* createLessEqOperator(expr* x, expr* y);

            /*
             *
             */
            app* createGreaterOperator(expr* x, expr* y);

            /*
             *
             */
            app* createGreaterEqOperator(expr* x, expr* y);

            /*
             *
             */
            app* createAndOperator(expr_ref_vector ands);

            /*
             *
             */
            app* createOrOperator(expr_ref_vector ors);

            /*
             *
             */
            expr* createNotOperator(const expr_ref x);

            /*
             *
             */
            expr* createImpliesOperator(expr* a, expr* b);

            /*
             *
             */
            app* createSelectOperator(expr* x, expr* y);

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
            expr* getExprVarFlatArray(std::pair<expr*, int> a);
            expr* getExprVarFlatArray(expr* e);
            expr* get_bound_str_int_control_var();
            expr* get_bound_p_control_var();
            expr* get_bound_q_control_var();

            app* createITEOperator(expr* c, expr* t, expr* e);
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
            std::vector<expr*> create_set_of_flat_variables(int flatP, std::map<expr*, int> &importantVars);
            /*
             * Input: x . y
             * Output: flat . flat . flat . flat . flat . flat
             */
            std::vector<std::pair<expr*, int>> create_equality(expr* node);
            std::vector<std::pair<expr*, int>> create_equality(ptr_vector<expr> list);
            std::vector<std::pair<expr*, int>> create_equality(std::vector<expr*> list);
                void create_internal_int_vars(expr* v);
                void setup_str_int_len(expr* e, int start);
                void reuse_internal_int_vars(expr* v);
            std::vector<expr*> set2vector(std::set<expr*> s);
            unsigned findMaxP(std::vector<expr*> v);

            /*
             * cut the same prefix and suffix and check if var is still there
             */
            bool check_var_after_optimizing(
                expr* lhs,
                expr* rhs,
                expr* var);
            /*
             * cut the same prefix and suffix
             */
            void optimize_equality(
                    expr* lhs,
                    expr* rhs,
                    ptr_vector<expr> &new_lhs,
                    ptr_vector<expr> &new_rhs);
                bool have_same_len(expr* lhs, expr* rhs);
            /*
             * cut the same prefix and suffix
             */
            void optimize_equality(
                    expr* lhs,
                    std::vector<expr*> rhs,
                    ptr_vector<expr> &new_lhs,
                    ptr_vector<expr> &new_rhs);
            /*
             * cut the same prefix and suffix
             */
            bool propagate_equality(
                        expr* lhs,
                        expr* rhs,
                        expr_ref_vector &imppliedEqualities);
            std::set<std::pair<expr*, int>> collect_important_vars();
            void collect_important_vars_str_int(std::map<expr*, int> &vars);
            void update_string_int_vars(expr* v, obj_hashtable<expr> &s);
            bool is_str_int_var(expr* e);
            void refine_important_vars(
                    std::set<std::pair<expr *, int>> &importantVars,
                    std::set<expr*> &notImportant,
                    std::map<expr *, std::set<expr *>> eq_combination);
                bool checkIfVarInUnionMembership(expr* nn, int &len);
                std::vector<zstring> collect_all_inequalities(expr* nn);
                expr* create_conjuct_all_inequalities(expr* nn);
                    bool is_trivial_inequality(expr* n, zstring s);
                bool collect_not_contains(expr* nn);
                bool collect_not_charAt(expr* nn, int &maxCharAt);
                bool more_than_two_occurrences(expr* n, std::map<expr*, int> occurrences);
                bool is_importantVar(
                    expr* nn,
                    std::map<expr*, int> occurrences,
                    int &len);
                bool is_importantVar_recheck(
                    expr* nn,
                    int len,
                    std::map<expr *, std::set<expr *>> combinations);
                    std::map<expr*, int> countOccurrences_from_root(std::set<expr*> eqc_roots);
                    std::map<expr*, int> countOccurrences_from_combination(std::map<expr *, std::set<expr *>> eq_combination);
            void print_all_assignments();
            void print_guessed_literals();
            std::map<expr*, std::set<expr*>> collect_inequalities_nonmembership(); // should be removed
            std::map<expr*, std::set<expr*>> construct_eq_combination(
                    std::map<expr*, std::set<expr*>> &causes,
                    std::set<expr*> &subNodes,
                    std::set<std::pair<expr*, int>> &importantVars);
                std::map<expr*, std::set<expr*>> refine_eq_combination(
                        std::set<std::pair<expr*, int>> &importantVars,
                        std::map<expr*, std::set<expr*>> combinations,
                        std::set<expr*> subNodes
                );
                std::map<expr*, std::set<expr*>> refine_eq_combination(
                        std::set<std::pair<expr*, int>> &importantVars,
                        std::map<expr*, std::set<expr*>> combinations,
                        std::set<expr*> subNodes,
                        std::set<expr*> notImportantVars
                );
                /*
                * true if var does not appear in eqs
                */
                bool appear_in_eqs(std::set<expr*> s, expr* var);

                bool appear_in_all_eqs(std::set<expr*> s, expr* var);

                /*
                * true if it has subvars
                */
                bool has_sub_var(expr* var);
                bool is_important_concat(expr* e, std::set<std::pair<expr*, int>> importantVars);
                bool is_trivial_combination(expr* v, std::set<expr*> eq, std::set<std::pair<expr*, int>> importantVars);
                std::set<expr*> refine_eq_set(
                        expr* var,
                    std::set<expr*> s,
                        std::set<std::pair<expr*, int>> importantVars,
                    std::set<expr*> notImportantVars);
                std::set<expr*> refine_eq_set(
                        expr* var,
                        std::set<expr*> s,
                        std::set<std::pair<expr*, int>> importantVars);
                    std::set<expr*> refine_all_duplications(std::set<expr*> s);
                    bool are_equal_concat(expr* lhs, expr* rhs);
                std::set<expr*> refine_eq_set(
                    std::set<expr*> s,
                    std::set<std::pair<expr*, int>> importantVars);
                bool is_important(expr *n, std::set<std::pair<expr*, int>> importantVars);
                bool is_important(expr *n, std::set<std::pair<expr*, int>> importantVars, int &l);
                std::set<expr*> extend_object(
                    expr* object,
                    std::map<expr*, std::set<expr*>> &combinations,
                    std::map<expr*, std::set<expr*>> &causes,
                    std::set<expr*> &subNodes,
                    std::set<expr*> parents,
                    std::set<std::pair<expr*, int>> importantVars);
                    expr* create_concat_with_concat(expr* n1, expr* n2);
                    expr* create_concat_with_str(expr* n, zstring str);
                    expr* create_concat_with_str(zstring str, expr* n);
                    expr* ends_with_str(expr* n);
                    expr* starts_with_str(expr* n);
                void add_subnodes(expr* concatL, expr* concatR, std::set<expr*> &subNodes);
        bool can_propagate() override;
        void propagate() override;
        expr* query_theory_arith_core(expr* n, model_generator& mg);
        expr* query_theory_array(expr* n, model_generator& mg);
        void init_model(model_generator& m) override;
        void finalize_model(model_generator& mg) override;

        void assert_cached_eq_state();
        void handle_equality(expr * lhs, expr * rhs);
            bool new_eq_check_wrt_disequalities(expr* n, expr_ref_vector premises, zstring containKey, expr_ref conclusion);
            void special_assertion_for_contain_vs_substr(expr* lhs, expr* rhs);
            expr_ref_vector collect_all_empty_start(expr* lhs, expr* rhs);
            expr_ref_vector collect_all_empty_end(expr* lhs, expr* rhs);
            expr_ref_vector negate_equality(expr* lhs, expr* rhs);
            bool is_inconsisten(
                std::set<expr*> concat_lhs,
                std::set<expr*> concat_rhs,
                std::set<expr*> const_lhs,
                std::set<expr*> const_rhs,
                bool &wrongStart, bool &wrongEnd);
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
            expr* collect_empty_node_in_concat(expr* n);
            void propagate_const_str(expr * lhs, expr * rhs, zstring value);
            void propagate_non_const(expr_ref_vector litems, expr * concat, expr * new_concat);
        void check_regex_in(expr * nn1, expr * nn2);
            void check_regex_in_lhs_rhs(expr * nn1, expr * nn2);
                expr* construct_overapprox(expr* nn, expr_ref_vector & litems);
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
        void instantiate_axiom_int_to_str(enode * e);
        void instantiate_axiom_str_to_int(enode * e);


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
        void get_all_nodes_in_concat(expr * node, ptr_vector<expr> & nodeList);
        expr * get_eqc_value(expr * n, bool & hasEqcValue);
        expr * z3str2_get_eqc_value(expr * n , bool & hasEqcValue);
        expr * get_eqc_next(expr * n);

        theory_var get_var(expr * n) const;
        app * get_ast(theory_var v);
        zstring get_std_regex_str(expr * regex);
        bool get_len_value(expr* e, rational& val);
        bool get_arith_value(expr* e, rational& val) const;
        bool lower_bound(expr* _e, rational& lo) const;
        bool upper_bound(expr* _e, rational& hi) const;
        bool upper_num_bound(expr* e, rational& hi) const;
        bool lower_num_bound(expr* e, rational& hi) const;
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
         * Check if there are empty vars in an AST node.
         */
        bool has_empty_vars(expr * node);

        /*
         * Collect important vars in AST node
         */
        void get_important_asts_in_node(expr * node, std::set<std::pair<expr*, int>> importantVars, expr_ref_vector & astList, bool consider_itself = false);
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
        obj_hashtable<expr> string_int_vars;
        obj_hashtable<expr> int_string_vars;

        expr_ref_vector m_persisted_axiom_todo;

        expr_ref_vector contains_map;

        theory_str_contain_pair_bool_map_t contain_pair_bool_map;
        obj_map<expr, std::set<std::pair<expr*, expr*> > > contain_pair_idx_map;
        obj_map<enode, std::pair<enode*,enode*>> contain_split_map;
        obj_map<expr, expr*> index_head;
        obj_map<expr, std::pair<expr*, expr*>> index_tail;
        std::set<std::pair<expr*, expr*>> length_relation;
        unsigned m_fresh_id;
        string_map stringConstantCache;
        unsigned long totalCacheAccessCount;

        obj_map<expr, eautomaton*>     m_re2aut;
        re2automaton                   m_mk_aut;
        expr_ref_vector                m_res;
        rational p_bound;
        rational q_bound;
        rational str_int_bound;
        rational max_str_int_bound = rational(5);
        rational max_p_bound = rational(3);
        rational max_q_bound = rational(20);
        expr* str_int_bound_expr = nullptr;
        expr* p_bound_expr = nullptr;
        expr* q_bound_expr = nullptr;
        bool flat_enabled = false;
        bool need_change = false;
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


        std::map<expr*, int> varPieces;
        std::map<expr*, int> currVarPieces;
        std::set<std::string> generatedEqualities;

        std::map<std::pair<int, int>, std::vector<Arrangment>> arrangements;
        std::set<zstring> constSet;
        std::set<char> sigmaDomain;
        std::map<expr*, std::vector<expr*>> lenMap;
        std::map<expr*, std::vector<expr*>> iterMap;
        std::map<expr*, std::set<expr*>> appearanceMap;
        std::map<expr*, std::set<expr*>> notContainMap;

        std::map<expr*, std::set<expr*>> backwardDep;
        std::map<expr*, expr*> arrMap;
        std::map<std::string, expr*> arrMap_reverse;
        std::map<std::string, expr*> varMap_reverse;
        int connectingSize;
        char defaultChar = 'a';
        UnderApproxState uState;
        std::vector<UnderApproxState> completedStates;


        expr_ref_vector impliedFacts;
    private:
        clock_t startClock;
        bool newConstraintTriggered = false;
        void assert_axiom(expr *e);
        void assert_axiom(expr *const e1, expr *const e2);
        void dump_assignments();
        void dump_literals();
        void fetch_guessed_core_exprs(
                std::map<expr*, std::set<expr*>> eq_combination,
                expr_ref_vector &guessedExprs,
                expr_ref_vector diseqExprs,
                rational bound = rational(0));
        void fetch_related_exprs(
                expr_ref_vector allvars,
                expr_ref_vector &guessedExprs);
        expr_ref_vector check_contain_related_vars(
                expr* v,
                zstring replaceKey);
        std::set<expr*> collect_all_vars_in_eq_combination(std::map<expr*, std::set<expr*>> eq_combination);
        void update_all_vars(std::set<expr*> &allvars, expr* e);
        bool check_intersection_not_empty(ptr_vector<expr> v, std::set<expr*> allvars);
        bool check_intersection_not_empty(ptr_vector<expr> v, expr_ref_vector allvars);
        void fetch_guessed_exprs_from_cache(UnderApproxState state, expr_ref_vector &guessedExprs);
        void fetch_guessed_exprs_with_scopes(expr_ref_vector &guessedEqs);
        void fetch_guessed_exprs_with_scopes(expr_ref_vector &guessedEqs, expr_ref_vector &guessedDisEqs);
        void fetch_guessed_literals_with_scopes(literal_vector &guessedLiterals);
        void fetch_guessed_str_int_with_scopes(expr_ref_vector &guessedEqs, expr_ref_vector &guessedDisEqs);
        void dump_bool_vars();
        const bool is_theory_str_term(expr *e) const;
        decl_kind get_decl_kind(expr *e) const;
        str::word_term get_word_term(expr *e) const;
        str::state build_state_from_memo() const;
        const bool block_dpllt_assignment_from_memo();
        void set_up_axioms(expr * ex);
    };


//    class int_expr_solver:expr_solver{
//        bool unsat_core=false;
//        kernel m_kernel;
//        ast_manager& m;
//        bool initialized;
//        expr_ref_vector erv;
//    public:
//        int_expr_solver(ast_manager& m, smt_params fp):
//                m_kernel(m, fp), m(m),erv(m){
//            fp.m_string_solver = symbol("none");
//            initialized=false;
//        }
//
//        lbool check_sat(expr* e) override;
//
//        void initialize(context& ctx);
//
//        void assert_expr(expr * e);
//    };

}

#endif /* _THEORY_STR_H_ */
