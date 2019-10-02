#ifndef _THEORY_TRAU_H_
#define _THEORY_TRAU_H_

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
            word_term() = default;
            word_term(std::initializer_list<element> list);
            void concat(const word_term& other);
            const std::size_t length() const { return m_elements.size(); }
            const bool empty() const { return m_elements.empty(); }
            explicit operator bool() const { return *this != null(); }
            const bool operator==(const word_term& other) const;
            const bool operator!=(const word_term& other) const { return !(*this == other); }
            const bool operator<(const word_term& other) const;
            friend std::ostream& operator<<(std::ostream& os, const word_term& w);
        };

        class word_equation {
            word_term m_lhs;
            word_term m_rhs;
        public:
            static const word_equation& null();
            word_equation(const word_term& lhs, const word_term& rhs);
            const word_term& lhs() const { return m_lhs; }
            const word_term& rhs() const { return m_rhs; }
            const bool empty() const { return m_lhs.empty() && m_rhs.empty(); }
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

        public:
            state() = default;
            explicit state(const bool allow_empty_var) : m_allow_empty_var{allow_empty_var} {}
            const bool operator<(const state& other) const;
            friend std::ostream& operator<<(std::ostream& os, const state& s);
            void satisfy_constraint(const word_equation& we);
            void fail_constraint(const word_equation& we);
            std::set<word_equation> m_wes_to_satisfy;
            std::set<word_equation> m_wes_to_fail;
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
        NON_FRESH__ONLY = 2,
        CONST_NON_FRESH = 3
    };


    class theory_str_contain_pair_bool_map_t : public obj_pair_map<expr, expr, expr*> {};

    class theory_trau : public theory {
        ast_manager&                    m;
        int                             m_scope_level;
        scoped_vector<expr_ref>         mful_scope_levels;
        const theory_str_params&        m_params;
        scoped_vector<str::expr_pair>   m_we_expr_memo;
        scoped_vector<str::expr_pair>   m_wi_expr_memo;
        scoped_vector<str::expr_pair>   membership_memo;
        scoped_vector<str::expr_pair>   non_membership_memo;

        typedef union_find<theory_trau>     th_union_find;
        typedef trail_stack<theory_trau>    th_trail_stack;
        struct zstring_hash_proc {
            unsigned operator()(zstring const & s) const {
                return string_hash(s.encode().c_str(), static_cast<unsigned>(s.length()), 17);
            }
        };
        typedef map<zstring, expr*, zstring_hash_proc, default_eq<zstring> > string_map;
        typedef old_svector<std::pair<expr*, int>> pair_expr_vector;
        class Arrangment{
        public:
            int_vector left_arr;
            int_vector right_arr;

            Arrangment(int_vector const& _left_arr,
                       int_vector const& _right_arr,
                       std::map<std::string, std::string> _constMap,
                       int _connectingSize){
                left_arr = _left_arr;
                right_arr = _right_arr;
            }

            Arrangment(int_vector const& _left_arr,
                       int_vector const& _right_arr){
                left_arr = _left_arr;
                right_arr = _right_arr;
            }

            void add_left(int number) {
                left_arr.push_back(number);
            }

            void add_right(int number) {
                right_arr.push_back(number);
            }

            bool can_split(int boundedFlat, int boundSize, int pos, std::string frame, std::vector<std::string> &flats) {
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
                        if (can_split(boundedFlat, boundSize, tmpPos, frame, flats))
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
                    if (can_split(i, PMAX, 0, frame, flats)){
                        return i;
                    }
                    flats.clear();
                }
                return -1;
            }

            void splitPrintTest(int_vector currentSplit, std::string msg = ""){
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
                for (int_vector::iterator it = list.begin(); it != list.end(); ++it) {
                    printf("%d ", *it);
                }
                printf("\n");
            }

            bool isUnionStr(std::string str){
                return str.find("|") != std::string::npos;
            }

            bool feasible_split_const(
                    std::string str,
                    std::vector<std::pair<std::string, int> > elements,
                    int_vector currentSplit,
                    int bound){
                /* check feasible const split */
                int pos = 0;
                for (unsigned i = 0; i < currentSplit.size(); ++i) {
                    if (elements[i].second == REGEX_CODE || isUnionStr(elements[i].first)) {
                    }

                        /* TODO: bound P */
                    else if (elements[i].second < 0) { /* const */
                        if (currentSplit[i] > (int)elements[i].first.length()) {
                        }
                        SASSERT ((int)elements[i].first.length() >= currentSplit[i]);

                        std::string lhs = str.substr(pos, currentSplit[i]);
                        std::string rhs = "";
                        if (elements[i].second % bound == -1) /* head */ {
                            rhs = elements[i].first.substr(0, currentSplit[i]);

                            if (i + 1 < elements.size()) {
                                if (bound == 1 || elements[i].first.length() == 1) {
                                    SASSERT (currentSplit[i] == (int)elements[i].first.length()); /* const length must be equal to length of const */
                                }
                                else {
                                    SASSERT ((currentSplit[i] + currentSplit[i + 1] == (int)elements[i].first.length())); /* sum of all const parts must be equal to length of const */
                                }
                            }
                        }
                        else { /* tail */
                            rhs = elements[i].first.substr(elements[i].first.length() - currentSplit[i], currentSplit[i]);
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
            bool is_possible_arrangement(){
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
                    std::vector<std::pair<expr*, int>> const& lhs_elements,
                    std::vector<std::pair<expr*, int>> const& rhs_elements) const {
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
            obj_map<expr, ptr_vector<expr>> eq_combination;
            obj_map<expr, int> non_fresh_vars;
            expr_ref_vector equalities;
            expr_ref_vector disequalities;
            str::state curr_state;
            bool reassertEQ = false;
            bool reassertDisEQ = false;
            int eqLevel = -1;
            int diseqLevel = -1;
            expr_ref_vector asserting_constraints;
            rational str_int_bound;

            UnderApproxState(ast_manager &m) : equalities(m), disequalities(m), asserting_constraints(m){
                eq_combination.reset();
            }

            UnderApproxState(ast_manager &m, int _eqLevel, int _diseqLevel,
                             obj_map<expr, ptr_vector<expr>> const& _eq_combination,
                             obj_map<expr, int> const& _non_fresh_vars,
                            expr_ref_vector const& _equalities,
                            expr_ref_vector const& _disequalities,
                            str::state const& _currState,
                            rational _str_int_bound):


                            eq_combination(_eq_combination),
                            non_fresh_vars(_non_fresh_vars),
                            equalities(m),
                            disequalities(m),
                            curr_state(_currState),

                            eqLevel(_eqLevel),
                            diseqLevel(_diseqLevel),
                            asserting_constraints(m),
                            str_int_bound(_str_int_bound){
                asserting_constraints.reset();
                equalities.reset();
                equalities.append(_equalities);
                disequalities.reset();
                disequalities.append(_disequalities);
                reassertEQ = true;
                reassertDisEQ = true;
            }

            UnderApproxState clone(ast_manager &m){
                UnderApproxState tmp(m, eqLevel, diseqLevel, eq_combination, non_fresh_vars, equalities, disequalities, curr_state, str_int_bound);
                tmp.add_asserting_constraints(asserting_constraints);
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
                non_fresh_vars = other.non_fresh_vars;

                equalities.reset();
                equalities.append(other.equalities);

                disequalities.reset();
                disequalities.append(other.disequalities);

                curr_state = other.curr_state;
                asserting_constraints.reset();
                reassertEQ = true;
                reassertDisEQ = true;
                for (int i = 0; i < other.asserting_constraints.size(); ++i)
                    asserting_constraints.push_back(other.asserting_constraints[i]);

                STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << ":  eq_combination: " << other.eq_combination.size() << " --> " << eq_combination.size() << std::endl;);
                return *this;
            }

            void add_asserting_constraints(expr_ref_vector _assertingConstraints){
                for (unsigned i = 0; i < _assertingConstraints.size(); ++i)
                    asserting_constraints.push_back(_assertingConstraints.get(i));
            }

            void add_asserting_constraints(expr_ref assertingConstraint){
                asserting_constraints.push_back(assertingConstraint);
            }

            bool operator==(const UnderApproxState state){
                obj_map<expr, ptr_vector<expr>> _eq_combination = state.eq_combination;
                STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << std::endl;);
                if (_eq_combination.size() != eq_combination.size()) {
                    STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << ": " << _eq_combination.size() << " vs " << eq_combination.size() <<  std::endl;);
                    return false;
                }

                for (const auto& v : non_fresh_vars)
                    if (!state.non_fresh_vars.contains(v.m_key)) {
                        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << std::endl;);
                        return false;
                    }

                for (const auto& n : eq_combination) {
                    if (_eq_combination.contains(n.m_key)) {
                        STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << std::endl;);
                        return false;
                    }
                    ptr_vector<expr> tmp = _eq_combination[n.m_key];
                    for (const auto &e : n.get_value()) {

                        if (!tmp.contains(e)) {
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
            theory_trau&                     th;
            sort*                           m_sort;
            svector<model_value_dependency> m_dependencies;
            app*                            node;
            enode*                          arr_node;
            bool                            non_fresh_var;
            expr*                           regex;
            expr*                           linker;
            int                             len;
        public:

            string_value_proc(theory_trau& th, sort * s, app* node, bool _non_fresh_var, enode* arr_node, expr* regex, int len = -1):
                    th(th),
                    m_sort(s),
                    node(node),
                    arr_node(arr_node),
                    non_fresh_var(_non_fresh_var),
                    regex(regex),
                    len(len){
            }

            string_value_proc(theory_trau& th, sort * s, app* node, bool _non_fresh_var, expr* regex, int len = -1):
                    th(th),
                    m_sort(s),
                    node(node),
                    non_fresh_var(_non_fresh_var),
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

            void set_linker(expr * link){
                linker = link;
            }

            void get_dependencies(buffer<model_value_dependency> & result) override {
                result.append(m_dependencies.size(), m_dependencies.c_ptr());
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__  << " " << mk_pp(node, th.get_manager()) << std::endl;);
            }

            app * mk_value(model_generator & mg, ptr_vector<expr> & values) override {
                // values must have size = m_num_entries * (m_dim + 1) + ((m_else || m_unspecified_else) ? 0 : 1)
                // an array value is a lookup table + else_value
                // each entry has m_dim indexes that map to a value.
                ast_manager & m = mg.get_manager();
                obj_map<enode, app *> m_root2value = mg.get_root2value();
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ":"  << mk_pp(node, m) << std::endl;);
                clock_t t = clock();
                for (int i = 0; i < (int)m_dependencies.size(); ++i){
                    app* val = nullptr;
                    if (m_root2value.find(m_dependencies[i].get_enode(), val)) {
                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ":"  << mk_pp(m_dependencies[i].get_enode()->get_owner(), m) << std::endl;);
                    }
                    else
                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ":"  << mk_pp(m_dependencies[i].get_enode()->get_owner(), m) << " no value " << std::endl;);
                }

                sort * str_sort = th.u.str.mk_string_sort();
                bool is_string = str_sort == m_sort;

                if (is_string) {
                    int len_int = len;
                    if (len_int != -1) {
                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": len : " << len_int << std::endl;);
                        if (non_fresh_var) {
                            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": important" << std::endl;);
                            if (len_int != -1) {
                                zstring strValue;
                                if (construct_string_from_array(mg, m_root2value, arr_node, len_int, strValue)) {
                                }
                                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": value = \"" << strValue << "\"" << std::endl;);
                                return to_app(th.mk_string(strValue));
                            }
                        }
                        if (regex != nullptr) {
                            zstring strValue;
                            if (construct_string_from_array(mg, m_root2value, arr_node, len_int, strValue)) {
                                return to_app(th.mk_string(strValue));
                            }
                            if (fetch_value_from_dep_graph(mg, m_root2value, len_int, strValue)) {
                                return to_app(th.mk_string(strValue));
                            }
                            if (construct_string_from_regex(mg, len_int, m_root2value, strValue)) {
                                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": regex value = \"" << strValue << "\"" << std::endl;);
                                return to_app(th.mk_string(strValue));
                            }
                        }
                        zstring strValue;
                        construct_normally(mg, len_int, m_root2value, strValue);
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
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ":"  << mk_pp(node, m) << " " <<  ((float)(clock() - t))/CLOCKS_PER_SEC<< std::endl;);
                return node;
            }

            bool construct_string_from_regex(model_generator &mg, int len_int, obj_map<enode, app *> const& m_root2value,
                                             zstring &strValue){
                std::vector<zstring> elements = collect_alternative_components(regex);
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
                    for (int i = 0; i < (int)elements.size(); ++i) {
                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " "  << elements[i] << std::endl;);
                    }
                    if (create_string_with_length(elements, valueStr, len_int)) {
                        strValue = valueStr;
                        return true;
                    }
                    else
                        return false;
                }
                return false;
            }

            bool create_string_with_length(std::vector<zstring> const& elements, zstring &currentStr, int remainLength){
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
                            while ((int)currentStr.length() > bak_len) {
                                if (create_string_with_length(elements, currentStr, tmpRemainLength)) {
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

            std::vector<zstring> collect_alternative_components(expr* v){
                std::vector<zstring> result;
                collect_alternative_components(v, result);
                return result;
            }


            void collect_alternative_components(expr* v, std::vector<zstring>& ret){
                if (th.u.re.is_to_re(v)){
                    expr* arg0 = to_app(v)->get_arg(0);
                    zstring tmpStr;
                    th.u.str.is_string(arg0, tmpStr);
                    ret.push_back(tmpStr);
                }
                else if (th.u.re.is_union(v)){
                    expr* arg0 = to_app(v)->get_arg(0);
                    collect_alternative_components(arg0, ret);
                    expr* arg1 = to_app(v)->get_arg(1);
                    collect_alternative_components(arg1, ret);
                }
                else if (th.u.re.is_star(v) || th.u.re.is_plus(v)) {
                    expr* arg0 = to_app(v)->get_arg(0);
                    collect_alternative_components(arg0, ret);
                }
                else if (th.u.re.is_range(v)){
                    expr* arg0 = to_app(v)->get_arg(0);
                    expr* arg1 = to_app(v)->get_arg(1);
                    zstring start, finish;
                    th.u.str.is_string(arg0, start);
                    th.u.str.is_string(arg1, finish);
                    SASSERT(start.length() == 1);
                    SASSERT(finish.length() == 1);

                    for (int i = start[0]; i <= (int)finish[0]; ++i){
                        zstring tmp(i);
                        ret.push_back(tmp);
                    }
                }
                else if (th.u.re.is_concat(v)) {
                    expr* tmp = is_regex_plus_breakdown(v);
                    if (tmp != nullptr){
                        return collect_alternative_components(tmp, ret);
                    }
                    else
                        NOT_IMPLEMENTED_YET();
                }
                else {
                    NOT_IMPLEMENTED_YET();
                }
            }

            expr* is_regex_plus_breakdown(expr* e){
                if (th.u.re.is_concat(e)){
                    expr* arg0 = to_app(e)->get_arg(0);
                    expr* arg1 = to_app(e)->get_arg(1);

                    if (th.u.re.is_star(arg1)){
                        expr* arg10 = to_app(arg1)->get_arg(0);
                        if (arg10 == arg0)
                            return arg1;
                    }

                    if (th.u.re.is_star(arg0)){
                        expr* arg00 = to_app(arg0)->get_arg(0);
                        if (arg00 == arg1)
                            return arg0;
                    }
                }
                return nullptr;
            }

            bool construct_normally(model_generator & mg, int len_int, obj_map<enode, app *> const& m_root2value, zstring& strValue){
                ast_manager & m = mg.get_manager();
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(node, mg.get_manager())  << ": NOT important" << std::endl;);
                if (len_int != -1) {
                    // non root var
                    clock_t t = clock();
                    bool constraint01 = !th.uState.eq_combination.contains(node);
                    bool constraint02 = th.dependency_graph[node].size() > 0;
                    if (constraint01 || constraint02) {
                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": case non root" << (constraint01 ? " true " : "false ") << (constraint02 ? " true " : "false ") << th.dependency_graph[node].size()<< std::endl;);
                        if (!constraint02) {
                            // free var
                            for (int i = 0; i < len_int; ++i)
                                strValue = strValue + th.default_char;
                            return to_app(th.mk_string(strValue));
                        } else {
                            if (fetch_value_from_dep_graph(mg, m_root2value, len_int, strValue))
                                return to_app(th.mk_string(strValue));
                        }
                    }
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": case root" << std::endl;);
                    // root var
                    int_vector val;
                    for (int i = 0; i < len_int; ++i)
                        val.push_back(-1);

                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ":  " << mk_pp(node, m) << std::endl;);
                    if (th.u.str.is_concat(node))
                        construct_string(mg, node, m_root2value, val);
                    if (th.uState.eq_combination.contains(node))
                        for (const auto &eq : th.uState.eq_combination[node]) {
                            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ":  " << mk_pp(eq, m) << std::endl;);
                            construct_string(mg, eq, m_root2value, val);
                        }
                    std::string ret = "";
                    for (int i = 0; i < len_int; ++i)
                        if (val[i] == -1) {
                            ret = ret + th.default_char;
                        } else
                            ret = ret + (char)val[i];
                    strValue = zstring(ret.c_str());
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": value = " << ret << std::endl;);
                    return to_app(th.mk_string(strValue));

                }
                else {
                    SASSERT(false);
                }

                return false;
            }

            bool construct_string_from_array(model_generator mg, obj_map<enode, app *> const& m_root2value, enode *arr,
                                             int len_int, zstring &val){
                SASSERT(arr->get_owner() != nullptr);
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(arr->get_owner(), mg.get_manager()) << " " << len_int << std::endl;);

                app* arr_val = nullptr;
                if (m_root2value.find(arr, arr_val)) {
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << std::endl;);
                    int_vector vValue (len_int, -1);

                    func_decl * fd = to_func_decl(arr_val->get_parameter(0).get_ast());
                    func_interp* fi = mg.get_model().get_func_interp(fd);

                    unsigned num_entries = fi->num_entries();
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " num_entries: " << num_entries << std::endl;);
                    for(unsigned i = 0; i < num_entries; i++)
                    {
                        func_entry const* fe = fi->get_entry(i);
                        expr* k =  fe->get_arg(0);
                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " key: " << mk_pp(k, mg.get_manager()) << std::endl;);
                        rational key;
                        if (th.m_autil.is_numeral(k, key) && key.get_int32() >=0 ) {
                            expr* v =  fe->get_result();

                            rational value;
                            if (th.m_autil.is_numeral(v, value)) {
                                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " key: " << key << "; value:" << value << std::endl;);
                                if (key.get_int32() < (int)vValue.size())
                                    vValue[key.get_int32()] = value.get_int32();
                            }
                        }
                    }

                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << std::endl;);

                    bool completed = true;
                    zstring value;

                    std::set<char> char_set;
                    get_char_range(char_set);
                    value = fill_chars(vValue, char_set, completed);

                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " value: "  << mk_pp(node, th.get_manager()) << " " << value << std::endl;);
                    val = value;

                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " value: "  << mk_pp(node, th.get_manager()) << " " << value << std::endl;);
                    // revise string basing on regex
                    if (char_set.size() == 0) {
                        if (regex != nullptr) {
                            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " value: "
                                               << mk_pp(node, th.get_manager()) << " " << value << std::endl;);
                            if (!match_regex(regex, val)) {
                                std::vector<zstring> elements = collect_alternative_components(regex);
                                for (int i = 0; i < (int)value.length(); ++i) {
                                    zstring tmp = val.extract(0, i);
                                    STRACE("str",
                                           tout << __LINE__ << " " << __FUNCTION__ << " tmp: " << tmp << std::endl;);
                                    if (!match_regex(regex, tmp)) {
                                        int err_pos = i;
                                        for (err_pos = i + 1; err_pos < (int)value.length(); ++err_pos)
                                            if (value[err_pos] != value[i]) {
                                                break;
                                            }

                                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " value: "
                                                           << mk_pp(node, th.get_manager()) << " " << value
                                                           << " " << i
                                                           << std::endl;);
                                        zstring working_str("");
                                        if (i > 0)
                                            working_str = val.extract(0, i - 1);

                                        zstring new_str("");
                                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " value: "
                                                           << mk_pp(node, th.get_manager()) << " " << working_str
                                                           << std::endl;);
                                        if (create_string_with_length(elements, new_str, err_pos - i)) {
                                            val = working_str + new_str + val.extract(i + new_str.length(),
                                                                                      val.length() -
                                                                                      (i + new_str.length()));
                                        }
                                        else
                                            NOT_IMPLEMENTED_YET();
                                        i = i + new_str.length() - 1;
                                    }
                                }
                            }
                        }
                    }

                    if (completed == false) {
                        return false;
                    }

                    return true;
                }

                return false;
            }

            bool get_char_range(std::set<char> & char_set){
                if (regex != nullptr) {
                    // special case for numbers
                    std::vector<zstring> elements = collect_alternative_components(regex);
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " s: "
                                       << mk_pp(regex, th.get_manager()) << " "
                                       << elements.size()
                                       << std::endl;);
                    for (const auto& s : elements) {
                        if (s.length() != 1) {
                            char_set.clear();
                            return false;
                        } else {
                            char_set.insert(s[0]);
                        }
                    }
                    return true;
                }
                return false;
            }

            zstring fill_chars(int_vector const& vValue, std::set<char> const& char_set, bool &completed){
                std::string value;

                for (unsigned i = 0; i < vValue.size(); ++i) {
                    if (char_set.size() > 0){
                        char tmp = (char)vValue[i];
                        if (char_set.find(tmp) == char_set.end())
                            value = value + (char)(*(char_set.begin()));
                        else
                            value = value + (char) vValue[i];
                    }
                    else {
                        if (vValue[i] <= 0 || vValue[i] >= 128) {
                            value = value + th.default_char;
                            completed = false;
                        } else
                            value = value + (char) vValue[i];
                    }
                }
                return zstring(value.c_str());
            }

            void construct_string(model_generator &mg, expr *eq, obj_map<enode, app *> const& m_root2value,
                                  int_vector &val){
                if (th.u.str.is_concat(eq)){
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": sync"  << mk_pp(eq, th.get_manager()) << std::endl;);
                    ptr_vector<expr> leafNodes;
                    th.get_nodes_in_concat(eq, leafNodes);

                    int sum = 0;
                    for (int i = 0; i < (int)leafNodes.size(); ++i){
                        if (th.is_important(leafNodes[i]) || th.u.str.is_string(leafNodes[i]) || th.is_regex_var(leafNodes[i])){
                            zstring leafVal;

                            if (get_str_value(th.get_context().get_enode(leafNodes[i]), m_root2value, leafVal)){
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
                            }
                        }
                        else {
                            int len_int = -1;
                            if (get_int_value(mg, th.get_context().get_enode(th.mk_strlen(leafNodes[i])), m_root2value,
                                              len_int)){
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

            bool fetch_value_from_dep_graph(model_generator &mg, obj_map<enode, app *> const& m_root2value, int len,
                                            zstring &value){
                // component var
                for (const auto &ancestor : th.dependency_graph[node]) {
                    STRACE("str",
                           tout << __LINE__ << " " << __FUNCTION__ << " "
                                << mk_pp(ancestor, mg.get_manager())
                                << std::endl;);
                    zstring ancestorValue;
                    if (get_str_value(th.get_context().get_enode(ancestor), m_root2value,
                                      ancestorValue)) {
                        if (th.u.str.is_concat(ancestor)) {
                            if (fetch_value_belong_to_concat(mg, ancestor, ancestorValue, m_root2value,
                                                             len, value)) {
                                return true;
                            }
                        }



                        // find in its eq
                        if (th.uState.eq_combination.contains(ancestor)) {
                            for (const auto &ancestor_i : th.uState.eq_combination[ancestor]) {
                                if (th.u.str.is_concat(ancestor_i)) {
                                    if (fetch_value_belong_to_concat(mg, ancestor_i, ancestorValue,
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

            bool fetch_value_belong_to_concat(model_generator &mg, expr *concat, zstring concatValue,
                                              obj_map<enode, app *> const& m_root2value, int len, zstring &value){
                if (th.u.str.is_concat(concat)){

                    ptr_vector<expr> leafNodes;
                    th.get_all_nodes_in_concat(concat, leafNodes);

                    if (leafNodes.contains(node) || (linker != nullptr && leafNodes.contains(linker))) {
                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": found in "  << mk_pp(concat, th.get_manager()) << std::endl;);
                        expr* tmp = nullptr;
                        if (leafNodes.contains(node))
                            tmp = node;
                        else
                            tmp = linker;
                        int prefix = find_prefix_len(mg, concat, tmp, m_root2value);
                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": prefix = "  << prefix << std::endl;);
                        value = concatValue.extract(prefix, len);
                        return true;
                    }
                    return false;
                }
                return false;
            }

            int find_prefix_len(model_generator &mg, expr *concat, expr *subNode, obj_map<enode, app *> const& m_root2value){

                if (th.u.str.is_concat(concat)){
                    int prefix = 0;
                    find_prefix_len(mg, concat, subNode, m_root2value, prefix);
                    return prefix;
                }
                else
                    SASSERT(false);

                return -1;
            }

            bool find_prefix_len(model_generator &mg, expr *concat, expr *subNode, obj_map<enode, app *> const& m_root2value,
                                 int &prefix){
                if (concat == subNode)
                    return true;
                if (th.u.str.is_concat(concat)){
                    if (!find_prefix_len(mg, to_app(concat)->get_arg(0), subNode, m_root2value, prefix)) {
                        if (!find_prefix_len(mg, to_app(concat)->get_arg(1), subNode, m_root2value, prefix))
                            return false;
                        else
                            return true;
                    }
                    else
                        return true;
                }
                else {
                    int subLen = -1;
                    zstring val_str;
                    if (th.u.str.is_string(concat, val_str)){
                        prefix += val_str.length();
                    }
                    else if (get_int_value(mg, th.get_context().get_enode(th.mk_strlen(concat)), m_root2value, subLen)) {
                        prefix += subLen;
                    }
                    else {
                        SASSERT(false);
                    }
                }
                return false;
            }

            bool get_int_value(model_generator &mg, enode *n, obj_map<enode, app *> const& m_root2value, int &value){
                app* val = nullptr;
                if (m_root2value.find(n->get_root(), val)) {
                    rational valInt;
                    if (th.m_autil.is_numeral(val, valInt)) {
                        value = valInt.get_int32();
                        return true;
                    }
                    else {
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
                    return false;
                }
            }

            bool get_str_value(enode *n, obj_map<enode, app *> const& m_root2value, zstring &value){
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

            bool match_regex(expr *a, zstring b){
                expr* tmp = th.u.re.mk_to_re(th.u.str.mk_string(b));
                return match_regex(a, tmp);
            }

            bool match_regex(expr *a, expr *b) {
                expr* intersection = th.u.re.mk_inter(a, b);
                eautomaton *au01 = get_automaton(intersection);
                return !au01->is_empty();
            }

            eautomaton* get_automaton(expr* re) {
                eautomaton* result = nullptr;
                if (th.m_re2aut.find(re, result)) {
                    return result;
                }

                result = th.m_mk_aut(re);
                th.m_automata.push_back(result);
                th.m_re2aut.insert(re, result);
                th.m_res.push_back(re);
                return result;
            }
        };


    public:
        theory_trau(ast_manager& m, const theory_str_params& params);
        ~theory_trau() override;
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
        theory *mk_fresh(context *) override { return alloc(theory_trau, get_manager(), m_params); }

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
        expr_ref_vector get_dependencies(expr *n);

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

            bool eval_disequal_str_int();
                bool eq_to_i2s(expr* n, expr* &i2s);

            /*
             * Check agreement between integer and string theories for the term a = (str.to-int S).
             * Returns true if axioms were added, and false otherwise.
             */
            bool eval_str2int(app * a);
                rational string_to_int(zstring str, bool &valid);
                int eval_invalid_str2int(expr* e, expr* &eq_node);
            bool eval_int2str(app * a);
            void refined_init_chain_free(
                    obj_map<expr, int> &non_fresh_vars,
                    obj_map<expr, ptr_vector<expr>> &eq_combination);
            void init_chain_free(
                    obj_map<expr, int> &non_fresh_vars,
                    obj_map<expr, ptr_vector<expr>> &eq_combination);
                bool analyze_upper_bound_str_int();
                rational log_10(rational n);
                rational ten_power(rational n);

            void refine_not_contain_vars(obj_map<expr, int> &non_fresh_vars, obj_map<expr, ptr_vector<expr>> const& eq_combination);
            bool is_not_important(expr* haystack, zstring needle, obj_map<expr, ptr_vector<expr>> const& eq_combination, obj_map<expr, int> const& non_fresh_vars);
                bool appear_in_eq(expr* haystack, zstring needle, ptr_vector<expr> const& s, obj_map<expr, int> const& non_fresh_vars);
                bool eq_in_list(expr* n, ptr_vector<expr> const& nodes);
            bool can_omit(expr* lhs, expr* rhs, zstring needle);
            bool appear_in_other_eq(expr* root, zstring needle, obj_map<expr, ptr_vector<expr>> const& eq_combination);
            bool is_completed_branch(bool &addAxiom, expr_ref_vector &diff);
            void update_state();
            bool propagate_eq_combination(obj_map<expr, ptr_vector<expr>> const& eq_combination);
            bool is_notContain_consistent(obj_map<expr, ptr_vector<expr>> const& eq_combination);
                bool is_notContain_consistent(expr* lhs, expr* rhs, expr* core);
                bool is_notContain_const_consistent(expr* lhs, zstring containKey, expr_ref premise);

            bool not_contain(expr* haystack, expr* needle, expr* &realHaystack);
            bool does_contain(expr* haystack, expr* needle, expr* &realHaystack);

            bool parikh_image_check(obj_map<expr, ptr_vector<expr>> const& eq_combination);
                bool equal_parikh(expr* nn, expr* n);
                    void get_parikh_from_strs(zstring s, map<char, int, unsigned_hash, default_eq<char>> &img);
                    bool eq_parikh(map<char, int, unsigned_hash, default_eq<char>> const& lhs, map<char, int, unsigned_hash, default_eq<char>> const& rhs);
                bool same_prefix_same_parikh(expr* nn, expr* n);
                bool can_match(zstring value, expr* n);
                void not_contain_string_in_expr(expr* n, expr_ref_vector &constList);
                bool agree_on_not_contain(expr* n, expr* key);
                int get_lower_bound_image_in_expr(expr* n, expr* str);
                bool get_image_in_expr(expr* n, expr_ref_vector &constList);

            int get_actual_trau_lvl();
                bool at_same_eq_state(UnderApproxState const& state, expr_ref_vector &diff);
                bool at_same_diseq_state(str::state const& curr, str::state const& prev);

        bool review_starting_ending_combination(obj_map<expr, ptr_vector<expr>> const& eq_combination);
            std::set<char> collect_char_domain_from_concat();
            std::set<char> collect_char_domain_from_eqmap(obj_map<expr, ptr_vector<expr>> const& eq_combination);
            bool handle_contain_family(obj_map<expr, ptr_vector<expr>> const& eq_combination);
                expr* create_equations_over_contain_vars(expr* x, expr* y);
            bool handle_charAt_family(obj_map<expr, ptr_vector<expr>> const& eq_combination);
                bool are_equal_exprs(expr* x, expr* y);
            std::set<expr*> get_eqc_roots();
            void add_theory_aware_branching_info(expr * term, double priority, lbool phase);


            bool propagate_concat();
            bool propagate_value(expr_ref_vector & concat_set);
            bool propagate_length(expr_ref_vector & varSet, expr_ref_vector & concatSet, std::map<expr*, int> & exprLenMap);
                void collect_var_concat(expr * node, expr_ref_vector & vars, expr_ref_vector & concats);
                void get_unique_non_concat_nodes(expr * node, expr_ref_vector & argSet);
                bool propagate_length_within_eqc(expr * var);
            bool underapproximation(
                    obj_map<expr, ptr_vector<expr>> const& eq_combination,
                    obj_map<expr, int> & non_fresh_vars,
                    expr_ref_vector const& diff);
                bool assert_state(expr_ref_vector const& guessedEqs, expr_ref_vector const& guessedDisEqs, str::state const& root);
                bool handle_str_int();
                    void handle_str2int(expr* num, expr* str);
                    void handle_int2str(expr* num, expr* str);
                        rational get_max_s2i(expr* n);
                        bool quickpath_str2int(expr* num, expr* str, bool cached = true);
                        bool quickpath_int2str(expr* num, expr* str, bool cached = true);
                        expr* unroll_str2int(expr* n);
                        expr* unroll_str_int(expr* num, expr* str);
                        expr* valid_str_int(expr* str);
                        expr* lower_bound_str_int(expr* num, expr* str);
                        expr* lower_bound_int_str(expr* num, expr* str);
                        expr* fill_0_1st_loop(expr* num, expr* str);
                            bool is_char_at(expr* str);
                void print_eq_combination(obj_map<expr, ptr_vector<expr>> const& eq_combination, int line = -1);
                bool is_equal(UnderApproxState const& preState, UnderApproxState const& currState);
                    bool are_some_empty_vars_omitted(expr* n, ptr_vector<expr> const& v);
                bool is_equal(expr_ref_vector const& corePrev, expr_ref_vector const& coreCurr);
            bool underapproximation_cached();
            void init_underapprox(obj_map<expr, ptr_vector<expr>> const& eq_combination, obj_map<expr, int> &non_fresh_vars);
                void mk_and_setup_arr(expr* v, obj_map<expr, int> &non_fresh_vars);
                void setup_str_int_arr(expr* v, int start);
                void setup_str_const(zstring val, expr* arr, expr* premise = nullptr);
                expr* setup_regex_var(expr* var, expr* rexpr, expr* arr, rational bound, expr* prefix);
                    expr* setup_char_range_arr(expr* e, expr* arr, rational bound, expr* prefix);
                void create_notcontain_map();
                void create_const_set();
                char setup_default_char(std::set<char> const& includeChars, std::set<char> const& excludeChars);
                std::set<char> init_excluded_char_set();
                std::set<char> init_included_char_set();
                void create_appearance_map(obj_map<expr, ptr_vector<expr>> const& eq_combination);
                void setup_flats();
                bool should_use_flat();
            void init_underapprox_cached();

            void handle_diseq_notcontain(bool cached = false);
                void handle_disequalities();
                void handle_disequalities_cached();

            bool review_not_contain(expr* lhs, expr* needle, obj_map<expr, ptr_vector<expr>> const& eq_combination);
                expr* remove_empty_in_concat(expr* s);
                bool review_notcontain_trivial(expr* lhs, expr* needle);
            bool review_disequalities_not_contain(obj_map<expr, ptr_vector<expr>> const& eq_combination);
                bool review_disequality(expr* lhs, expr* rhs, obj_map<expr, ptr_vector<expr>> const& eq_combination);
                bool review_disequality_trivial(expr* lhs, expr* rhs);
                    void handle_disequality(expr *lhs, expr *rhs);
                    void handle_disequality_const(expr *lhs, zstring rhs);
                    void handle_disequality_var(expr *lhs, expr *rhs);
                void handle_not_contain();
                void handle_not_contain_cached();
                    void handle_not_contain(expr *lhs, expr *rhs, bool cached = false);
                    void handle_not_contain_var(expr *lhs, expr *rhs, expr *premise, bool cached = false);
                    void handle_not_contain_const(expr *lhs, zstring rhs, expr *premise, bool cached = false);
                    bool is_contain_equality(expr* n);
                    bool is_contain_equality(expr* n, expr* &contain);
                    bool is_trivial_contain(zstring s);
                void  init_connecting_size(obj_map<expr, ptr_vector<expr>> const& eq_combination, obj_map<expr, int> &non_fresh_vars, bool prep = true);
                    void static_analysis(obj_map<expr, ptr_vector<expr>> const& eq_combination);
            bool convert_equalities(obj_map<expr, ptr_vector<expr>> const& eq_combination,
                                           obj_map<expr, int> & non_fresh_vars,
                                           expr* premise);
                bool is_long_equality(ptr_vector<expr> const& eqs);
                expr* convert_other_equalities(ptr_vector<expr> const& eqs, obj_map<expr, int> const& non_fresh_vars);
                expr* convert_long_equalities(expr* var, ptr_vector<expr> const& eqs, obj_map<expr, int> &non_fresh_vars);
                expr* convert_const_nonfresh_equalities(expr* var, ptr_vector<expr> const& eqs, obj_map<expr, int> const& non_fresh_vars);
                void convert_regex_equalities(expr* regexExpr, expr* var, obj_map<expr, int> const& non_fresh_vars, expr_ref_vector &assertedConstraints, bool &axiomAdded);
                expr* const_contains_key(zstring c, expr* pre_contain, expr* key, rational len);
                void assert_breakdown_combination(expr* e, expr* premise, expr_ref_vector &assertedConstraints, bool &axiomAdded);
                void assert_breakdown_combination(expr* e, expr* var);
                void negate_context();
                void negate_equalities();
                void negate_context(expr* e);
                void negate_context(expr_ref_vector const& v);
                expr* find_equivalent_variable(expr* e);
                bool is_internal_var(expr* e);
                bool is_internal_regex_var(expr* e, expr* &regex);
                /*
                * (abc)*__XXX -> abc
                */
                zstring parse_regex_content(zstring str);
                zstring parse_regex_content(expr* str);
                expr_ref_vector combine_const_str(expr_ref_vector const& v);
                    bool isRegexStr(zstring str);
                    bool isUnionStr(zstring str);

                expr_ref_vector parse_regex_components(expr* reg);

                    /*
                    * (a) | (b) --> {a, b}
                    */
                    std::vector<zstring> collect_alternative_components(zstring str);
                    expr_ref_vector collect_alternative_components(expr* v);
                    bool collect_alternative_components(expr* v, expr_ref_vector& ret);
                    bool collect_alternative_components(expr* v, std::vector<zstring>& ret);
                    int find_correspond_right_parentheses(int leftParentheses, zstring str);

                std::set<zstring> collect_strs_in_membership(expr* v);
                void collect_strs_in_membership(expr* v, std::set<zstring> &ret);
                    expr* remove_star_in_star(expr* reg);
                    bool contain_star(expr* reg);
                zstring getStdRegexStr(expr* regex);
            /*
             * convert lhs == rhs to SMT formula
             */
            expr* equality_to_arith(
                std::vector<std::pair<expr*, int>> const& lhs_elements,
                std::vector<std::pair<expr*, int>> const& rhs_elements,
                obj_map<expr, int> const& non_fresh_variables,
                int p = PMAX);
                expr* equality_to_arith_ordered(
                        std::vector<std::pair<expr*, int>> const& lhs_elements,
                        std::vector<std::pair<expr*, int>> const& rhs_elements,
                        obj_map<expr, int> const& non_fresh_variables,
                        int p);
                std::string create_string_representation(std::vector<std::pair<expr*, int>> const& lhs_elements,
                                                              std::vector<std::pair<expr*, int>> const& rhs_elements);
            /*
             * lhs: size of the lhs
             * rhs: size of the rhs
             * lhs_elements: elements of lhs
             * rhs_elements: elements of rhs
             *
             * Pre-Condition: x_i == 0 --> x_i+1 == 0
             *
             */
            expr_ref_vector arrange(
                std::vector<std::pair<expr*, int>> const& lhs_elements,
                std::vector<std::pair<expr*, int>> const& rhs_elements,
                obj_map<expr, int> const& non_fresh_variables,
                int p = PMAX);

            void get_arrangements(std::vector<std::pair<expr*, int>> const& lhs_elements,
                                          std::vector<std::pair<expr*, int>> const& rhs_elements,
                                          obj_map<expr, int> const& non_fresh_variables,
                                          std::vector<Arrangment> &possibleCases);

            void update_possible_arrangements(
                std::vector<std::pair<expr*, int>> const& lhs_elements,
                std::vector<std::pair<expr*, int>> const& rhs_elements,
                std::vector<Arrangment> const& tmp,
                std::vector<Arrangment> &possibleCases);

            /*
             *
             */
            Arrangment create_arrangments_manually(
                std::vector<std::pair<expr*, int>> const& lhs_elements,
                std::vector<std::pair<expr*, int>> const& rhs_elements);

            /*
             * a_1 + a_2 + b_1 + b_2 = c_1 + c_2 + d_1 + d_2 ---> SMT
             */
            expr* to_arith(int p,
                                            int_vector const& left_arr,
                                            int_vector const& right_arr,
                                            std::vector<std::pair<expr*, int>> const& lhs_elements,
                                            std::vector<std::pair<expr*, int>> const& rhs_elements,
                                            obj_map<expr, int> const& non_fresh_variables);
                expr* to_arith_others(bool (&checkLeft)[10000], bool (&checkRight)[10000], int p,
                                           int_vector const& left_arr,
                                           int_vector const& right_arr,
                                           std::vector<std::pair<expr*, int>> const& lhs_elements,
                                           std::vector<std::pair<expr*, int>> const& rhs_elements,
                                            obj_map<expr, int> const& non_fresh_variables);
                expr* to_arith_emptyflats(bool (&checkLeft)[10000], bool (&checkRight)[10000],
                                          int_vector const& left_arr,
                                          int_vector const& right_arr,
                              std::vector<std::pair<expr*, int>> const& lhs_elements,
                              std::vector<std::pair<expr*, int>> const& rhs_elements);
                expr* to_arith_right(bool (&checkLeft)[10000], bool (&checkRight)[10000], int p,
                                     int_vector const& left_arr,
                                     int_vector const& right_arr,
                              std::vector<std::pair<expr*, int>> const& lhs_elements,
                              std::vector<std::pair<expr*, int>> const& rhs_elements,
                              obj_map<expr, int> const& non_fresh_variables);
                expr* to_arith_left(bool (&checkLeft)[10000], bool (&checkRight)[10000], int p,
                              int_vector const& left_arr,
                              int_vector const& right_arr,
                              std::vector<std::pair<expr*, int>> const& lhs_elements,
                              std::vector<std::pair<expr*, int>> const& rhs_elements,
                              obj_map<expr, int> const& non_fresh_variables);

            /*
             * Flat = Flat
             * size = size && it = it  ||
             * size = size && it = 1
             */
            expr* gen_constraint01(
                    std::pair<expr *, int> a, std::pair<expr *, int> b,
                    int pMax,
                    obj_map<expr, int> const& non_fresh_variables,
                    bool optimizing);

                void gen_constraint01_const_var(
                        std::pair<expr *, int> a, std::pair<expr *, int> b,
                        obj_map<expr, int> const& non_fresh_variables,
                        bool optimizing,
                        expr_ref_vector &result);

                void gen_constraint01_const_const(
                        std::pair<expr *, int> a, std::pair<expr *, int> b,
                        bool optimizing,
                        expr *nameA,
                        expr_ref_vector &result);

                expr* gen_constraint01_regex_head(std::pair<expr *, int> a, std::pair<expr *, int> b, expr *nameA);

                expr* gen_constraint01_regex_tail(std::pair<expr *, int> a, std::pair<expr *, int> b, expr *nameA);

                expr* gen_constraint01_regex_regex(std::pair<expr *, int> a, std::pair<expr *, int> b, expr *nameA);

                expr* gen_constraint01_const_const(std::pair<expr *, int> a, std::pair<expr *, int> b, expr *nameA);

                void gen_constraint01_var_var(
                        std::pair<expr *, int> a, std::pair<expr *, int> b,
                        int pMax,
                        obj_map<expr, int> const& non_fresh_variables,
                        bool optimizing,
                        expr *nameA,
                        expr_ref_vector &result);

            expr* gen_constraint_var_var(
                    std::pair<expr *, int> a,
                    std::pair<expr *, int> b,
                    int pMax,
                    rational bound);

            expr* gen_constraint_flat_var(
                    std::pair<expr *, int> a,
                    std::vector<std::pair<expr *, int>> const& elements,
                    int pos,
                    int pMax,
                    rational bound);

            expr* gen_constraint_flat_flat(
                    std::pair<expr *, int> a,
                    std::vector<std::pair<expr *, int>> const& elements,
                    int pos,
                    int pMax,
                    rational bound,
                    bool skip_init = false);
            int lcd(int x, int y);
            bool match_regex(expr* a, zstring b);
            bool match_regex(expr* a, expr* b);
            /*
             * Flat = sum (flats)
             */
            expr* gen_constraint02(
                    std::pair<expr *, int> a,
                    std::vector<std::pair<expr *, int>> const& elements,
                    int pMax,
                    obj_map<expr, int> const& non_fresh_variables,
                    bool optimizing);

                bool gen_constraint02_const_regex(std::pair<expr *, int> a,
                                                  std::vector<std::pair<expr *, int>> const& elements,
                                                  int pMax,
                                                  obj_map<expr, int> const& non_fresh_variables,
                                                  bool optimizing,
                                                  expr_ref_vector &result);

                bool generate_constraint02_var(std::pair<expr*, int> a,
                                                    std::vector<std::pair<expr*, int>> const& elements,
                                                    obj_map<expr, int> const& non_fresh_variables,
                                                    bool optimizing,
                                                    expr_ref_vector &result);

                bool is_reg_union(expr* n);
                /*
                * Input: split a string
                * Output: SMT
                */
                expr* gen_constraint_non_fresh_var_const(
                        std::pair<expr *, int> a, /* const || regex */
                        std::vector<std::pair<expr *, int> > const& elements, /* const + non_fresh_ var */
                        int_vector const& split,
                        obj_map<expr, int> const& non_fresh_variables,
                        bool optimizing,
                        int pMax);

                    /*
                    *
                    */
                    expr* lengthConstraint_tonon_fresh_VarConstraint(
                            std::pair<expr*, int> a, /* const || regex */
                            std::vector<std::pair<expr*, int> > const& elements,
                            expr_ref_vector const& subElements,
                            int currentPos,
                            int subLength,
                            obj_map<expr, int> const& non_fresh_variables,
                            bool optimizing,
                            int pMax);

                        /*
                        *
                        */
                        expr_ref positional_non_fresh_var_in_array(
                                std::pair<expr *, int> a, /* const or regex */
                                std::vector<std::pair<expr *, int>> const& elements, /* have non_fresh_ var */
                                int var_pos,
                                int var_length,
                                obj_map<expr, int> const& non_fresh_variables,
                                bool optimizing,
                                int pMax);
                /*
                 * Input: split a string
                 * Output: SMT
                 */
                expr_ref_vector gen_constraint_without_non_fresh_vars(
                        std::pair<expr *, int> a, /* const || regex */
                        std::vector<std::pair<expr *, int> > const& elements, /* no non_fresh_ var */
                        int_vector const& split,
                        bool optimizing);
                /*
                 *
                 */
                expr* unroll_non_fresh_variable(
                        std::pair<expr*, int> a, /* non_fresh_ variable */
                        std::vector<std::pair<expr*, int> > const& elements, /* contain const */
                        obj_map<expr, int> const& non_fresh_variables,
                        bool optimizing,
                        int pMax = PMAX);
                    /*
                     * Generate constraints for the case
                     * X = T . "abc" . Y . Z
                     * constPos: position of const element
                     * return: (or (and length header = i && X_i = a && X_[i+1] = b && X_[i+2] = c))
                     */
                    expr_ref handle_positional_subconst_in_array(
                            std::pair<expr *, int> a, // non_fresh_ var
                            std::vector<std::pair<expr *, int>> const& elements,
                            int constPos,
                            bool optimizing,
                            int pMax = PMAX);

                        /*
                        * Generate constraints for the case
                        * X = T . "abc"* . Y . Z
                        * regexPos: position of regex element
                        * return: forAll (i Int) and (i < |abc*|) (y[i + |T|] == a | b | c)
                        */
                        expr_ref handle_positional_regex_in_array(
                                std::pair<expr *, int> a, // non_fresh_ var
                                std::vector<std::pair<expr *, int>> const& elements,
                                int regexPos,
                                bool optimizing,
                                int pMax = PMAX,
                                expr *extraConstraint = NULL/* length = ? */
                        );

                        /*
                        * Generate constraints for the case
                        * X = T . "abc" . Y . Z
                        * constPos: position of const element
                        * return: (or (and length header = i && X_i = a && X_[i+1] = b && X_[i+2] = c))
                        */
                        expr_ref handle_positional_const_in_array(
                                std::pair<expr *, int> a,
                                std::vector<std::pair<expr *, int>> const& elements,
                                int constPos,
                                zstring value, /* value of regex */
                                int start, int finish,
                                bool optimizing,
                                int pMax = PMAX,
                                expr *extraConstraint = NULL /* length = ? */);

                    /*
                    * non_fresh_ = a + non_fresh_ + b
                    */
                    expr* handle_non_fresh_non_fresh_array(
                            std::pair<expr *, int> a,
                            std::vector<std::pair<expr *, int>> const& elements,
                            int pos,
                            int bound,
                            bool optimizing,
                            int pMax = PMAX);

                /*
                 *
                 */
                expr* gen_constraint_non_fresh_var(
                        std::pair<expr *, int> a, /* const or regex */
                        std::vector<std::pair<expr *, int>> const& elements, /* have non_fresh_ var, do not have const */
                        obj_map<expr, int> const& non_fresh_variables,
                        bool optimizing,
                        int pMax);

                expr* unroll_regex_non_fresh_variable(
                        std::pair<expr *, int> const& a, /* const or regex */
                        std::pair<expr *, int> const& b,
                        int pMax,
                        int part_cnt,
                        int max_len,
                        expr* sub_len,
                        expr* prefix_lhs,
                        expr* prefix_rhs);

                expr* unroll_var_non_fresh_variable(
                        std::pair<expr *, int> a, /* const or regex */
                        std::vector<std::pair<expr *, int>> const& elements, /* have non_fresh_ var, do not have const */
                        int pMax,
                        int pos,
                        int part_cnt);

                expr* unroll_const_variable(
                        std::pair<expr *, int> a, /* const or regex */
                        std::pair<expr *, int> b,
                        int pMax,
                        int max_len,
                        expr* sub_len,
                        expr* prefix_lhs,
                        expr* prefix_rhs);

                expr* unroll_const_non_fresh_variable_str2int(
                        std::pair<expr *, int> a, /* const or regex */
                        std::pair<expr *, int> b,
                        int max_len,
                        expr* sub_len,
                        expr* prefix_lhs,
                        expr* prefix_rhs);

                expr* unroll_const_non_fresh_variable(
                        std::pair<expr *, int> a, /* const or regex */
                        std::pair<expr *, int> b,
                        int pMax,
                        int max_len,
                        expr* sub_len,
                        expr* prefix_lhs,
                        expr* prefix_rhs);

                expr* gen_regex_non_fresh_variable(
                        std::pair<expr *, int> a, /* const or regex */
                        std::vector<std::pair<expr *, int>> const& elements, /* have non_fresh_ var, do not have const */
                        obj_map<expr, int> const& non_fresh_variables,
                        int pMax,
                        int pos,
                        int part_cnt,
                        expr* sub_len,
                        expr* prefix_rhs);
                expr* gen_regex_regex(
                    std::pair<expr *, int> a, /* const or regex */
                    std::vector<std::pair<expr *, int>> const& elements, /* have non_fresh_ var, do not have const */
                    obj_map<expr, int> const& non_fresh_variables,
                    int pMax,
                    int pos);

                /*
                 * elements[pos] is a non_fresh_.
                 * how many parts of that non_fresh_ variable are in the const | regex
                 */
                expr* find_partsOfnon_fresh_variablesInAVector(
                        int pos,
                        std::vector<std::pair<expr*, int>> const& elements,
                        int &partCnt);
                /*
                * pre elements + pre fix of itself
                */
                expr* leng_prefix_lhs(std::pair<expr*, int> a,
                                          std::vector<std::pair<expr*, int>> const& elements,
                                          int pos,
                                          bool optimizing,
                                          bool unrollMode);

                /*
                *  pre fix of itself
                */
                expr* leng_prefix_rhs(std::pair<expr*, int> a, /* var */ bool unrollMode);

                /*
                 * 0: No const, No non_fresh_ var
                * 1: const		No non_fresh_ var
                * 2: no const, non_fresh_ var
                * 3: have both
                */
                int choose_split_type(
                        std::vector<std::pair<expr*, int>> const& elements,
                        obj_map<expr, int> const& non_fresh_variables,
                        expr* lhs);

                /*
                * Input: constA and a number of flats
                * Output: all possible ways to split constA
                */
                std::vector<int_vector > collect_splits(
                        std::pair<expr*, int> lhs,
                        std::vector<std::pair<expr*, int> > const& elements,
                        bool optimizing);
                    bool not_contain_check(expr* e, std::vector<std::pair<expr*, int> > const& elements);
                    bool const_vs_regex(expr* reg, std::vector<std::pair<expr*, int> > const& elements);
                    bool const_vs_str_int(expr* e, std::vector<std::pair<expr*, int> > const& elements, expr* &extra_assert);
                        expr* find_i2s(expr* e);
                    bool length_base_split(expr* e, std::vector<std::pair<expr*, int> > const& elements);
                /*
                * textLeft: length of string
                * nMax: number of flats
                * pMax: size of a flat
                *
                * Pre-Condition: 1st flat and n-th flat must be greater than 0
                * Output: of the form 1 * 1 + 1 * 0 + 1 * 0 + 1 * 0 + 1 * 0 + 1 * 0 + 1 * 0 + 1 * 0 + 1 * 3 + 2 * 3 = 10
                */
                void collect_const_splits(
                        int pos,
                        zstring str, /* const */
                        int pMax,
                        std::vector<std::pair<expr*, int> > const& elements,
                        int_vector currentSplit,
                        std::vector<int_vector > &allPossibleSplits
                );
                    /*
                     * (a)|(b | c) --> {a, b, c}
                     */
                     std::set<zstring> get_regex_components(zstring s);
                    /*
                    * (a) --> a
                    */
                    void remove_parentheses(zstring &s);
                /*
                * (a|b|c)*_xxx --> range <a, c>
                */
                std::vector<std::pair<int, int>> collect_char_range(expr* a);
                void collect_char_range(expr* a, std::vector<bool> &chars);

                bool feasibleSplit_const(
                        zstring str,
                        std::vector<std::pair<expr*, int> > const& elements,
                        int_vector const& currentSplit,
                        int bound);
            /*
             * Given a flat,
             * generate its size constraint
             */
            expr* get_var_size(std::pair<expr*, int> const& a);
            /*
             *
             */
            std::string gen_flat_iter(std::pair<expr*, int> const& a);
            expr* get_flat_iter(std::pair<expr*, int> const& a);
            /*
             * Given a flat,
             * generate its size constraint
             */
            std::string gen_flat_size(std::pair<expr*, int> const& a);
            expr* get_var_flat_size(std::pair<expr*, int> const& a);

            /*
             *
             */
            app* createEqualOP(expr* x, expr* y);
            app* createMulOP(expr *x, expr *y);
            app* createModOP(expr* x, expr* y);
            app* createMinusOP(expr* x, expr* y);
            app* createAddOP(expr* x, expr* y);
            app* createAddOP(expr_ref_vector adds);
            app* createLessOP(expr* x, expr* y);
            app* createLessEqOP(expr* x, expr* y);
            app* createGreaterOP(expr* x, expr* y);
            app* createGreaterEqOP(expr* x, expr* y);
            app* createAndOP(expr_ref_vector ands);
            app* createOrOP(expr_ref_vector ors);
            app* createSelectOP(expr* x, expr* y);

            int optimized_lhs(
                    int i, int startPos, int j,
                    int_vector const& left_arr,
                    int_vector const& right_arr,
                    std::vector<std::pair<std::string, int>> const& lhs_elements,
                    std::vector<std::pair<std::string, int>> const& rhs_elements);

            int optimized_rhs(
                    int i, int startPos, int j,
                    int_vector const& left_arr,
                    int_vector const& right_arr,
                    std::vector<std::pair<std::string, int>> const& lhs_elements,
                    std::vector<std::pair<std::string, int>> const& rhs_elements);
            /*
             * Given a flat,
             * generate its array name
             */
            std::string gen_flat_arr(std::pair<expr*, int> const& a);
            expr* get_var_flat_array(std::pair<expr*, int> const& a);
            expr* get_var_flat_array(expr* e);
            expr* get_bound_str_int_control_var();
            expr* get_bound_p_control_var();
            expr* get_bound_q_control_var();

            app* createITEOP(expr* c, expr* t, expr* e);
            /*
            * First base case
            */
            void setup_0_0_general();
            /*
             * 2nd base case [0] = (sum rhs...)
             */
            void setup_0_n_general(int lhs, int rhs);
            /*
             * 2nd base case (sum lhs...) = [0]
             */
            void setup_n_0_general(int lhs, int rhs);
            /*
             * general case
             */
            void setup_n_n_general(int lhs, int rhs);
            std::vector<std::pair<std::string, int>> vectorExpr2vectorStr(std::vector<std::pair<expr*, int>> const& v);
            std::string expr2str(expr* node);

            /*
             * Input: x . y
             * Output: flat . flat . flat . flat . flat . flat
             */
            std::vector<std::pair<expr*, int>> create_equality(expr* node, bool unfold = true);
            std::vector<std::pair<expr*, int>> create_equality(ptr_vector<expr> const& list, bool unfold = true);
            std::vector<std::pair<expr*, int>> create_equality_final(ptr_vector<expr> const& list, bool unfold = true);
                void create_internal_int_vars(expr* v);
                void setup_str_int_len(expr* e, int start);
                void reuse_internal_int_vars(expr* v);
            unsigned findMaxP(ptr_vector<expr> const& v);

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
                expr* create_concat_from_vector(ptr_vector<expr> const& v, int from_pos);
                expr* create_concat_from_vector(ptr_vector<expr> const& v);
                bool have_same_len(expr* lhs, expr* rhs);
            /*
             * cut the same prefix and suffix
             */
            void optimize_equality(
                    expr* lhs,
                    ptr_vector<expr> const& rhs,
                    ptr_vector<expr> &new_lhs,
                    ptr_vector<expr> &new_rhs);
            /*
             * cut the same prefix and suffix
             */
            bool propagate_equality(
                    expr* lhs,
                    expr* rhs,
                    expr_ref_vector &to_assert);

                bool propagate_equality_right_2_left(
                        expr* lhs,
                        expr* rhs,
                        int &suffix,
                        expr_ref_vector &and_rhs,
                        expr_ref_vector &to_assert);

                bool propagate_equality_left_2_right(
                        expr* lhs,
                        expr* rhs,
                        int &prefix,
                        expr_ref_vector &and_lhs,
                        expr_ref_vector &to_assert);

            obj_map<expr, int> collect_important_vars();
            void collect_non_fresh_vars_str_int(obj_map<expr, int> &vars);
            void add_non_fresh_var(expr* const &e, obj_map<expr, int> &vars, int len);
            void update_string_int_vars(expr* v, obj_hashtable<expr> &s);
            bool is_str_int_var(expr* e);
            void refine_important_vars(
                    obj_map<expr, int> &non_fresh_vars,
                    expr_ref_vector &notImportant,
                    obj_map<expr, ptr_vector<expr>> const& eq_combination);
                bool checkIfVarInUnionMembership(expr* nn, int &len);
                bool belong_to_var_var_inequality(expr* nn);
                std::vector<zstring> collect_all_inequalities(expr* nn);
                    bool is_var_var_inequality(expr* x, expr* y);
                expr* create_conjuct_all_inequalities(expr* nn);
                    bool is_trivial_inequality(expr* n, zstring s);
                bool collect_not_contains(expr* nn);
                bool collect_not_charAt(expr* nn, int &maxCharAt);
                bool more_than_two_occurrences(expr* n, obj_map<expr, int> const& occurrences);
                bool is_non_fresh_occurrences(expr *nn, obj_map<expr, int> const &occurrences, int &len);
                bool is_non_fresh_recheck(expr *nn, int len, obj_map<expr, ptr_vector<expr>> const& combinations);
                obj_map<expr, int> count_occurrences_from_root();
                        bool is_replace_var(expr* x);
                    obj_map<expr, int> count_occurrences_from_combination(
                            obj_map<expr, ptr_vector<expr>> const &eq_combination,
                            obj_map<expr, int> const &non_fresh_vars);
            void print_all_assignments();
            void print_guessed_literals();
            obj_map<expr, ptr_vector<expr>> normalize_eq(
                    expr_ref_vector &subNodes,
                    obj_map<expr, int> &non_fresh_vars);
            obj_map<expr, ptr_vector<expr>> refine_eq_combination(
                    obj_map<expr, int> &non_fresh_vars,
                        obj_map<expr, ptr_vector<expr>> const& combinations,
                        expr_ref_vector const& subNodes
                );

                obj_map<expr, ptr_vector<expr>> refine_eq_combination(
                        obj_map<expr, int> &non_fresh_vars,
                        obj_map<expr, ptr_vector<expr>> combinations,
                        expr_ref_vector subNodes,
                        expr_ref_vector notnon_fresh_vars
                );

                bool can_merge_combination(obj_map<expr, ptr_vector<expr>> const& combinations);
                    bool concat_in_set(expr* n, ptr_vector<expr> const& s);
                /*
                * true if var does not appear in eqs
                */
                bool appear_in_eqs(ptr_vector<expr> const& s, expr* var);

                bool is_important_concat(expr* e, obj_map<expr, int> const& non_fresh_vars);
                bool is_trivial_combination(expr* v, ptr_vector<expr> const& eq, obj_map<expr, int> const& non_fresh_vars);
                ptr_vector<expr> refine_eq_set(
                        expr* var,
                        ptr_vector<expr> s,
                        obj_map<expr, int> const& non_fresh_vars,
                        expr_ref_vector const& notnon_fresh_vars);
                ptr_vector<expr> refine_eq_set(
                        expr* var,
                        ptr_vector<expr> s,
                        obj_map<expr, int> const& non_fresh_vars);
                    void refine_all_duplications(ptr_vector<expr> &s);
                    bool are_equal_concat(expr* lhs, expr* rhs);
                    ptr_vector<expr> refine_eq_set(ptr_vector<expr> const& s, obj_map<expr, int> const& non_fresh_vars);
                bool is_non_fresh(expr *n, obj_map<expr, int> const &non_fresh_vars);
                bool is_non_fresh(expr *n, obj_map<expr, int> const &non_fresh_vars, int &l);
                ptr_vector<expr> extend_object(
                    expr* object,
                    obj_map<expr, ptr_vector<expr>> &combinations,
                    expr_ref_vector &subNodes,
                    expr_ref_vector parents,
                    obj_map<expr, int> non_fresh_vars);
                    expr* create_concat_with_concat(expr* n1, expr* n2);
                    expr* create_concat_with_str(expr* n, zstring str);
                    expr* create_concat_with_str(zstring str, expr* n);
                    expr* ends_with_str(expr* n);
                    expr* starts_with_str(expr* n);
                void add_subnodes(expr* concatL, expr* concatR, expr_ref_vector &subNodes);
        bool can_propagate() override;
        void propagate() override;
        expr* query_theory_arith_core(expr* n, model_generator& mg);
        expr* query_theory_array(expr* n, model_generator& mg);
        void init_model(model_generator& m) override;
        void finalize_model(model_generator& mg) override;

        void assert_cached_eq_state();
        void handle_equality(expr * lhs, expr * rhs);
            bool new_eq_check_wrt_disequalities(expr* n, zstring containKey, expr_ref conclusion);
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

        bool can_solve_contain_family(enode * e);
        bool can_reduce_contain_family(expr* ex);
        app* mk_replace(expr* a, expr* b, expr* c) const;
        app* mk_at(expr* a, expr* b) const;
        expr* is_regex_plus_breakdown(expr* e);
        void sync_index_head(expr* pos, expr* base, expr* first_part, expr* second_part);
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
        void get_nodes_in_reg_concat(expr * node, ptr_vector<expr> & nodeList);
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
        void get_important_asts_in_node(expr * node, obj_map<expr, int> const& non_fresh_vars, expr_ref_vector & astList, bool consider_itself = false);
        eautomaton* get_automaton(expr* re);

        void track_variable_scope(expr * var);
        expr * rewrite_implication(expr * premise, expr * conclusion);
        void assert_implication(expr * premise, expr * conclusion);

        enode* ensure_enode(expr* e);
        bool                                                search_started;
        th_rewriter                                         m_rewrite;
        seq_rewriter                                        m_seq_rewrite;
        arith_util                                          m_autil;
        array_util                                          m_arrayUtil;
        seq_util                                            u;
        expr_ref_vector                                     m_trail; // trail for generated terms
        th_union_find                                       m_find;
        th_trail_stack                                      m_trail_stack;

        std::map<int, obj_hashtable<expr> >                 internal_variable_scope_levels;
        obj_pair_map<expr, expr, expr*>                     concat_astNode_map;

        std::map<std::pair<expr*, zstring>, expr*>          regex_in_bool_map;
        obj_map<expr, std::set<zstring> >                   regex_in_var_reg_str_map;

        scoped_ptr_vector<eautomaton>                       m_automata;
        ptr_vector<eautomaton>                              regex_automata;
        obj_hashtable<expr>                                 regex_terms;
        obj_map<expr, ptr_vector<expr> >                    regex_terms_by_string; // S --> [ (str.in.re S *) ]

        // hashtable of all exprs for which we've already set up term-specific axioms --
        // this prevents infinite recursive descent with respect to axioms that
        // include an occurrence of the term for which axioms are being generated
        obj_hashtable<expr>                                 axiomatized_terms;
        obj_hashtable<expr>                                 variable_set;
        obj_hashtable<expr>                                 internal_variable_set;
        obj_hashtable<expr>                                 regex_variable_set;

        expr_ref_vector                                     m_delayed_axiom_setup_terms;

        ptr_vector<enode>                                   m_basicstr_axiom_todo;
        svector<std::pair<enode*,enode*> >                  m_str_eq_todo;
        ptr_vector<enode>                                   m_concat_axiom_todo;
        ptr_vector<enode>                                   m_concat_eval_todo;
        expr_ref_vector                                     m_delayed_assertions_todo;

        // enode lists for library-aware/high-level string terms (e.g. substr, contains)
        ptr_vector<enode>                                   m_library_aware_axiom_todo;
        obj_hashtable<expr>                                 input_var_in_len;
        expr_ref_vector                                     string_int_conversion_terms;
        obj_hashtable<expr>                                 string_int_axioms;
        obj_hashtable<expr>                                 string_int_vars;
        obj_hashtable<expr>                                 int_string_vars;

        expr_ref_vector                                     m_persisted_axiom_todo;

        expr_ref_vector                                     contains_map;

        theory_str_contain_pair_bool_map_t                  contain_pair_bool_map;
        obj_map<expr, std::set<std::pair<expr*, expr*> > >  contain_pair_idx_map;
        obj_map<enode, std::pair<enode*,enode*>>            contain_split_map;
        obj_map<expr, expr*>                                index_head;
        obj_map<expr, std::pair<expr*, expr*>>              index_tail;
        std::set<std::pair<expr*, expr*>>                   length_relation;
        unsigned                                            m_fresh_id;
        string_map                                          stringConstantCache;
        unsigned long                                       totalCacheAccessCount;

        obj_map<expr, eautomaton*>                          m_re2aut;
        re2automaton                                        m_mk_aut;
        expr_ref_vector                                     m_res;
        rational                                            p_bound = rational(2);
        rational                                            q_bound = rational(10);
        rational                                            str_int_bound;
        rational                                            max_str_int_bound = rational(10);
        rational                                            max_p_bound = rational(3);
        rational                                            max_q_bound = rational(20);
        expr*                                               str_int_bound_expr = nullptr;
        expr*                                               p_bound_expr = nullptr;
        expr*                                               q_bound_expr = nullptr;
        bool                                                flat_enabled = false;
        bool                                                need_change = false;
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
        bool                                                opt_DisableIntegerTheoryIntegration;

        /*
         * If ConcatOverlapAvoid is set to true,
         * the check to simplify Concat = Concat in handle_equality() will
         * avoid simplifying wrt. pairs of Concat terms that will immediately
         * result in an overlap. (false = Z3str2 behaviour)
         */
        bool                                                 opt_ConcatOverlapAvoid;


        // under approximation vars
        const int                                           CONNECTINGSIZE = 300;
        static const int                                    PMAX = 2;
        const std::string                                   FLATPREFIX = "__flat_";
        int                                                 flat_var_counter = 0;


        std::map<expr*, int>                                var_pieces_counter;
        std::map<expr*, int>                                curr_var_pieces_counter;
        std::set<std::string>                               generated_equalities;

        std::map<std::pair<int, int>, std::vector<Arrangment>> arrangements;
        std::set<zstring>                                   const_set;
        std::set<char>                                      sigma_domain;
        std::map<expr*, std::vector<expr*>>                 length_map;
        std::map<expr*, std::vector<expr*>>                 iter_map;
        std::map<expr*, std::set<expr*>>                    appearance_map;
        std::map<expr*, std::set<expr*>>                    not_contain_map;

        std::map<expr*, std::set<expr*>>                    dependency_graph;
        std::map<expr*, expr*>                              expr_array_linkers;
        std::map<expr*, expr*>                              array_map;
        std::map<std::string, expr*>                        array_map_reverse;
        std::map<std::string, expr*>                        varMap_reverse;
        std::map<expr*, expr*>                              arr_linker;
        int                                                 connectingSize;
        char                                                default_char = 'a';
        UnderApproxState                                    uState;
        std::vector<UnderApproxState>                       completed_branches;


        expr_ref_vector                                     implied_facts;
    private:
        clock_t                                             startClock;
        bool                                                newConstraintTriggered = false;
        void assert_axiom(expr *e);
        void assert_axiom(expr *const e1, expr *const e2);
        void dump_assignments();
        void dump_literals();
        void fetch_guessed_core_exprs(
                obj_map<expr, ptr_vector<expr>> eq_combination,
                expr_ref_vector &guessed_exprs,
                expr_ref_vector diseq_exprs,
                rational bound = rational(0));
        void add_equalities_to_core(expr_ref_vector guessed_exprs, expr_ref_vector &all_vars, expr_ref_vector &core);
        void add_disequalities_to_core(expr_ref_vector diseq_exprs, expr_ref_vector &core);
        void add_assignments_to_core(expr_ref_vector all_vars, expr_ref_vector &core);
        unsigned get_assign_lvl(expr* a, expr* b);
        void fetch_related_exprs(
                expr_ref_vector allvars,
                expr_ref_vector &guessedExprs);
        expr_ref_vector check_contain_related_vars(
                expr* v,
                zstring replaceKey);
        expr_ref_vector collect_all_vars_in_eq_combination(obj_map<expr, ptr_vector<expr>> eq_combination);
        void update_all_vars(expr_ref_vector &allvars, expr* e);
        bool check_intersection_not_empty(ptr_vector<expr> v, std::set<expr*> allvars);
        bool check_intersection_not_empty(ptr_vector<expr> v, expr_ref_vector allvars);
        void fetch_guessed_exprs_from_cache(UnderApproxState state, expr_ref_vector &guessed_exprs);
        void fetch_guessed_exprs_with_scopes(expr_ref_vector &guessedEqs);
        void fetch_guessed_exprs_with_scopes(expr_ref_vector &guessedEqs, expr_ref_vector &guessedDisEqs);
        void fetch_guessed_literals_with_scopes(literal_vector &guessedLiterals);
        void fetch_guessed_str_int_with_scopes(expr_ref_vector &guessedEqs, expr_ref_vector &guessedDisEqs);
        void dump_bool_vars();
        const bool is_theory_str_term(expr *e) const;
        decl_kind get_decl_kind(expr *e) const;
        str::word_term get_word_term(expr *e) const;
        str::state build_state_from_memo() const;
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

#endif /* _THEORY_TRAU_H_ */
