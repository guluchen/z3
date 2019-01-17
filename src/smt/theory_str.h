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

            std::map<std::string, std::string> constMap; // extra info for all Arrangement
            int connectingSize; // extra info for all Arrangement

            Arrangment(std::vector<int> _left_arr,
                       std::vector<int> _right_arr,
                       std::map<std::string, std::string> _constMap,
                       int _connectingSize){

                constMap.clear();

                left_arr.insert(left_arr.end(), _left_arr.begin(), _left_arr.end());
                right_arr.insert(right_arr.end(), _right_arr.begin(), _right_arr.end());

                /* extra info */
                constMap.insert(_constMap.begin(), _constMap.end());
                connectingSize = _connectingSize;
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
             * (lhs)* = (rhs)* where lhs starts at posLHS
             */
            std::vector<int> regex_in_regex_at_pos(std::string lhs, std::string rhs, int posLhs) {
                STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " ***: " << lhs << " = " << rhs << " at " << posLhs << std::endl;);
                /* extend string if it is short */
                rhs = parse_regex_content(rhs);
                std::vector<std::string> componentsRhs = collectAlternativeComponents(rhs);
                if (isUnionStr(lhs)){
                    std::vector<std::string> componentsLhs = collectAlternativeComponents(lhs);
                    std::vector<int> ret;
                    for (const auto& r : componentsRhs)
                        for (const auto& l: componentsLhs)
                            for (int i = 0; i < (int)l.length() - (int)r.length(); ++i) {
                                if (l.substr(i, r.length()).compare(r) == 0)
                                    ret.emplace_back(i);
                            }
                    return ret;
                }


                std::string initialLhs = lhs;
                while (rhs.length() + posLhs > initialLhs.length()) /* make sure that | initialLhs | > | rhs | */
                    initialLhs = initialLhs + lhs;

                std::vector<int> possibleCases;
                possibleCases.emplace_back(0);
                int getIn = -1;
                for (const auto& r : componentsRhs)
                    if (r.compare(initialLhs.substr(posLhs, r.length())) == 0) {
                        getIn = (int)r.length();
                        break;
                    }
                if (getIn >= 0) {
                    int pos_lhs = (posLhs + getIn) % lhs.length();
                    int iterRhs = 1;

                    possibleCases.emplace_back(1);

                    std::string double_str = initialLhs + initialLhs;
                    while (pos_lhs != posLhs) {
                        bool foundNextIter = false;
                        for (const auto& r : componentsRhs)
                            /* loop until it goes back the initial position */
                            if (r.compare(double_str.substr(pos_lhs, r.length())) == 0) {
                                possibleCases.emplace_back(++iterRhs);
                                pos_lhs = (pos_lhs + r.length()) % lhs.length();
                                foundNextIter = true;
                                break;
                            }
                        if (!foundNextIter)
                            break;
                    }
                }
                else /* cannot happens */ {
                    // isloopExist = false;
                }

                return possibleCases;
            }

            /*
             * (lhs)* = .* rhs .* where rhs starts at posLhs
             */
            bool const_in_regex_at_pos(std::string lhs, std::string rhs, int posLhs){

                /* extend string if it is short */
                std::string initialLhs = lhs;
                while (rhs.length() + posLhs > initialLhs.length()) /* make sure that | initialLhs | > | rhs | */
                    initialLhs = initialLhs + lhs;

                if (rhs.compare(initialLhs.substr(posLhs, rhs.length())) == 0) {
                    return true;
                }
                return false;
            }

            /*
             * (lhs)* = .* rhs.-2 .* where rhs starts at posLHS
             */
            std::vector<int> tail_in_regex_at_pos(std::string lhs, std::string rhs, int posLhs){

                std::vector<int> potentialPos;
                for (int i = 0; i <= (int)rhs.length(); ++i) {
                    /* length = i */
                    std::string tmpRhs = rhs.substr(i);

                    /* extend string if it is short */
                    std::string initialLhs = lhs;
                    while (tmpRhs.length() + posLhs > initialLhs.length()) /* make sure that | initialLhs | > | rhs | */
                        initialLhs = initialLhs + lhs;

                    if (tmpRhs.compare(initialLhs.substr(posLhs, tmpRhs.length())) == 0) {
                        potentialPos.emplace_back(rhs.length() - i);
                    }
                }
                return potentialPos;
            }

            /*
             * (lhs)* = .* rhs.-1 .* where lhs starts at posLHS
             */
            std::vector<int> head_in_regex_at_pos(std::string lhs, std::string rhs, int posLhs){

                std::vector<int> potentialPos;
                for (int i = 0; i <= (int)rhs.length(); ++i) {
                    /* length = i */
                    std::string tmpRhs = rhs.substr(0, i);

                    /* extend string if it is short */
                    std::string initialLhs = lhs;
                    while (tmpRhs.length() + posLhs > initialLhs.length()) /* make sure that | initialLhs | > | rhs | */
                        initialLhs = initialLhs + lhs;

                    if (tmpRhs.compare(initialLhs.substr(posLhs, tmpRhs.length())) == 0) {
                        potentialPos.emplace_back(i);
                    }
                    else
                        return potentialPos;
                }
                return potentialPos;
            }

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
                    std::string str, /* const */
                    int pMax,
                    std::vector<std::pair<std::string, int> > elementNames,
                    std::vector<int> currentSplit,
                    std::vector<std::vector<int> > &allPossibleSplits
            ) {
                SASSERT(pos <= (int) str.length());
                /* reach end */
                if (currentSplit.size() == elementNames.size()){
                    if (pos == (int)str.length() &&
                        feasibleSplit_const(str, elementNames, currentSplit)) {
                        allPossibleSplits.emplace_back(currentSplit);
                    }
                    else {
                    }
                    return;
                }

                unsigned textLeft = str.length() - pos;

                /* special case for const: leng = leng */
                if (elementNames[currentSplit.size()].second % QCONSTMAX == -1 && (QCONSTMAX == 1 || elementNames[currentSplit.size()].first.length() == 1)) {
                    if (elementNames[currentSplit.size()].first.length() <= textLeft) {
                        std::string constValue = str.substr(pos, elementNames[currentSplit.size()].first.length());

                        if (constValue.compare(elementNames[currentSplit.size()].first) == 0) {
                            currentSplit.emplace_back(elementNames[currentSplit.size()].first.length());
                            collectAllPossibleSplits_const(pos + elementNames[currentSplit.size() - 1].first.length(), str, pMax, elementNames, currentSplit, allPossibleSplits);
                            currentSplit.pop_back();
                        }
                    }
                }

                    /* const head */
                else if (elementNames[currentSplit.size()].second % QCONSTMAX == -1 &&
                         QCONSTMAX == 2) {
                    if (elementNames[currentSplit.size()].first.length() <= textLeft) {
                        std::set<std::string> values;
                        if (isUnionStr(elementNames[currentSplit.size()].first)){
                            values = extendComponent(elementNames[currentSplit.size()].first);
                        }
                        else
                            values.emplace(elementNames[currentSplit.size()].first);
//				__debugPrint(logFile, "%d %s -> values size = %ld\n", __LINE__, elementNames[currentSplit.size()].first.c_str(),
//						values.size());
                        for (const auto& value : values) {
                            std::string constValue = str.substr(pos, value.length());
                            if (constValue.compare(value) == 0) {
                                if (values.size() > 1)
                                STRACE("str", tout << __LINE__ << " assed value:  " << value << std::endl;);
                                for (int i = 0; i < std::min(7, (int)value.length()); ++i) {
                                    currentSplit.emplace_back(i);
                                    collectAllPossibleSplits_const(pos + i, str, pMax, elementNames, currentSplit, allPossibleSplits);
                                    currentSplit.pop_back();
                                }
                            }
                        }
                    }
                }

                    /* special case for const tail, when we know the length of const head */
                else if (currentSplit.size() > 0 &&
                         elementNames[currentSplit.size()].second % QCONSTMAX == 0 &&
                         elementNames[currentSplit.size()].second < 0 &&
                         elementNames[currentSplit.size()].second > REGEX_CODE &&
                         QCONSTMAX == 2) /* const */ {
                    assert (elementNames[currentSplit.size() - 1].second % QCONSTMAX == -1);
                    std::set<std::string> values;
                    if (isUnionStr(elementNames[currentSplit.size()].first)){
                        values = extendComponent(elementNames[currentSplit.size()].first);
                    }
                    else
                        values.emplace(elementNames[currentSplit.size()].first);

                    for (const auto& value : values) {
                        std::string constValue = str.substr(pos - currentSplit[currentSplit.size() - 1], value.length());
                        unsigned length = (unsigned)value.length() - currentSplit[currentSplit.size() - 1]; /* this part gets all const string remaining */

                        if (constValue.compare(value) == 0) {
                            if (length <= textLeft) {
                                currentSplit.emplace_back(length);
                                collectAllPossibleSplits_const(pos + length, str, pMax, elementNames, currentSplit, allPossibleSplits);
                                currentSplit.pop_back();
                            }
                        }
                    }
                }

                    /* head is const part 2*/
                else if (currentSplit.size() == 0 &&
                         elementNames[0].second % QCONSTMAX == 0 &&
                         elementNames[0].second < 0 &&
                         elementNames[0].second > REGEX_CODE &&
                         QCONSTMAX == 2) /* const */ {
                    std::set<std::string> values;
                    if (isUnionStr(elementNames[currentSplit.size()].first)){
                        values = extendComponent(elementNames[currentSplit.size()].first);
                    }
                    else
                        values.emplace(elementNames[currentSplit.size()].first);
                    for (const auto& value : values)
                        for (unsigned i = 0; i < std::min(value.length(), str.length()); ++i) {
                            if (values.size() > 1)
                            STRACE("str", tout << __LINE__ << " assed value:  " << value << std::endl;);
                            std::string tmp00 = value.substr(i);
                            std::string tmp01 = str.substr(0, i);
                            if (tmp00.compare(tmp01) == 0){
                                currentSplit.emplace_back(tmp00.length());
                                collectAllPossibleSplits_const(pos + tmp00.length(), str, pMax, elementNames, currentSplit, allPossibleSplits);
                                currentSplit.pop_back();
                            }
                        }
                }

                else {
                    SASSERT(!(elementNames[currentSplit.size()].second < 0 && elementNames[currentSplit.size()].second > REGEX_CODE));

                    std::string regexContent = "";
                    RegEx re;
                    bool canCompile = false;
                    if (elementNames[currentSplit.size()].second == REGEX_CODE) /* regex */ {
                        regexContent = parse_regex_full_content(elementNames[currentSplit.size()].first);
                        if (regexContent.find('|') != std::string::npos) {
                            SASSERT(regexContent.find('&') == std::string::npos);
                            re.Compile(regexContent);
                            canCompile = true;
                        }
                        else
                            regexContent = parse_regex_content(elementNames[currentSplit.size()].first);
                    }

                    for (unsigned i = 0; i <= textLeft; ++i) {
                        unsigned length = i;
                        if (elementNames[currentSplit.size()].second == REGEX_CODE) /* regex */ {
                            std::string regexValue = str.substr(pos, length);
                            if (canCompile == true) {
                                if (re.MatchAll(regexValue) == true) {
                                    currentSplit.emplace_back(length);
                                    collectAllPossibleSplits_const(pos + length, str, pMax, elementNames, currentSplit, allPossibleSplits);
                                    currentSplit.pop_back();
                                }
                            }
                            else {
                                /* manually doing matching regex */
                                std::string tmp = "";
                                if (elementNames[currentSplit.size()].first.find('+') != std::string::npos)
                                    tmp = regexContent;
                                else
                                SASSERT(elementNames[currentSplit.size()].first.find('*') != std::string::npos);
                                while(tmp.length() < regexValue.length())
                                    tmp += regexContent;
                                STRACE("str", tout << __LINE__ << " matching: " << tmp << " --- " << regexValue << std::endl;);

                                if (tmp.compare(regexValue) == 0) {
                                    currentSplit.emplace_back(length);
                                    collectAllPossibleSplits_const(pos + length, str, pMax, elementNames, currentSplit, allPossibleSplits);
                                    currentSplit.pop_back();
                                }
                            }
                        }
                        else {
                            currentSplit.emplace_back(length);
                            collectAllPossibleSplits_const(pos + length, str, pMax, elementNames, currentSplit, allPossibleSplits);
                            currentSplit.pop_back();
                        }
                    }
                }
            }

            void collectAllPossibleSplits_regex(
                    int pos,
                    std::string str, /* regex */
                    int pMax,
                    std::vector<std::pair<std::string, int> > elementNames,
                    std::vector<int> currentSplit,
                    std::vector<std::vector<int> > &allPossibleSplits) {

                /* reach end */
                if (currentSplit.size() == elementNames.size() &&
                    (pos == 0 || pos == MINUSZERO)) {

                    allPossibleSplits.emplace_back(currentSplit);
                    return;
                }
                else if (currentSplit.size() >= elementNames.size()) {
                    return;
                }

                /* special case for const: regex = .* const .* */
                if (elementNames[currentSplit.size()].second == -1 && QCONSTMAX == 1) {
                    /* compare text, check whether the string can start from the location pos in text */
                    if (const_in_regex_at_pos(str, elementNames[currentSplit.size()].first, pos)) {
                        currentSplit.emplace_back(elementNames[currentSplit.size()].first.length());
                        collectAllPossibleSplits_regex((pos + elementNames[currentSplit.size() - 1].first.length()) % str.length(), str, pMax, elementNames, currentSplit, allPossibleSplits);
                        currentSplit.pop_back();
                    }
                }

                    /* special case for const tail, when we know the length of const head */
                else if (elementNames[currentSplit.size()].second % QCONSTMAX == 0 &&
                         elementNames[currentSplit.size()].second < 0 &&
                         elementNames[currentSplit.size()].second > REGEX_CODE &&
                         currentSplit.size() > 0) /* tail, not the first */ {
                    SASSERT (elementNames[currentSplit.size() - 1].second - 1 == elementNames[currentSplit.size()].second);
                    int length = elementNames[currentSplit.size()].first.length() - currentSplit[currentSplit.size() - 1]; /* this part gets all const string remaining */

                    currentSplit.emplace_back(length);
                    collectAllPossibleSplits_regex((pos + length) % str.length(), str, pMax, elementNames, currentSplit, allPossibleSplits);
                    currentSplit.pop_back();
                }

                else if (elementNames[currentSplit.size()].second % QCONSTMAX == 0 &&
                         elementNames[currentSplit.size()].second < 0 &&
                         elementNames[currentSplit.size()].second > REGEX_CODE &&
                         currentSplit.size() == 0) /* tail, first */ {
                    /* find all possible start points */
                    std::vector<int> tail = tail_in_regex_at_pos(str, elementNames[currentSplit.size()].first, pos);
                    for (unsigned i = 0 ; i < tail.size(); ++i) {
                        currentSplit.emplace_back(tail[i]);
                        collectAllPossibleSplits_regex((pos + tail[i]) % str.length(), str, pMax, elementNames, currentSplit, allPossibleSplits);
                        currentSplit.pop_back();
                    }
                }

                else if (elementNames[currentSplit.size()].second % QCONSTMAX == -1 &&
                         elementNames[currentSplit.size()].second < 0 &&
                         elementNames[currentSplit.size()].second > REGEX_CODE &&
                         currentSplit.size() + 1 == elementNames.size() &&
                         QCONSTMAX == 2) /* head, the last element */ {
                    /* find all possible start points */
                    std::vector<int> head = head_in_regex_at_pos(str, elementNames[currentSplit.size()].first, pos);
                    for (unsigned i = 0 ; i < head.size(); ++i) {
                        currentSplit.emplace_back(head[i]);
                        collectAllPossibleSplits_regex((pos + head[i]) % str.length(), str, pMax, elementNames, currentSplit, allPossibleSplits);
                        currentSplit.pop_back();
                    }
                }

                else if (elementNames[currentSplit.size()].second % QCONSTMAX == -1 &&
                         elementNames[currentSplit.size()].second < 0 &&
                         elementNames[currentSplit.size()].second > REGEX_CODE &&
                         currentSplit.size() + 1 < elementNames.size() &&
                         QCONSTMAX == 2) /* head, not the last element */ {
                    /* check full string */
                    bool canProcess;
                    if (isUnionStr(str))
                        canProcess = true;
                    else
                        canProcess = const_in_regex_at_pos(str, elementNames[currentSplit.size()].first, pos);
                    if (elementNames[currentSplit.size() + 1].second == elementNames[currentSplit.size()].second - 1){
                        if (canProcess) {
                            for (unsigned i = 1 ; i <= elementNames[currentSplit.size()].first.length(); ++i) { /* cannot be empty */
                                currentSplit.emplace_back(i);
                                collectAllPossibleSplits_regex((pos + i) % str.length(), str, pMax, elementNames, currentSplit, allPossibleSplits);
                                currentSplit.pop_back();
                            }
                        }
                    }
                    else {
                        /* this const only has 1 part */
                        if (canProcess) {
                            for (unsigned i = 1 ; i <= elementNames[currentSplit.size()].first.length(); ++i) { /* cannot be empty */
                                currentSplit.emplace_back(i);
                                collectAllPossibleSplits_regex((pos + i) % str.length(), str, pMax, elementNames, currentSplit, allPossibleSplits);
                                currentSplit.pop_back();
                            }
                        }
                    }
                }

                else if (elementNames[currentSplit.size()].second == REGEX_CODE) /* regex */ {
                    std::string content = parse_regex_content(elementNames[currentSplit.size()].first);
                    int contentLength = (int)content.length();

                    std::vector<std::string> components = {content};
                    if (isUnionStr(content)) {
                        components = collectAlternativeComponents(content);
                        for (const auto& s : components)
                            contentLength = std::min(contentLength, (int)s.length());
                    }
                    std::vector<int> regexPos = regex_in_regex_at_pos(str, elementNames[currentSplit.size()].first, pos);
                    /* loop ? */
                    bool loop = false;
                    if (regexPos.size() > 0 &&
                        regexPos[regexPos.size() - 1] * contentLength % str.length() == 0) {
                        loop = true;
                    }

                    // __debugPrint(logFile, "%d loop = %d, regexPos size = %ld, contentLength = %d\n", __LINE__, loop ? 1 : 0, regexPos.size(), contentLength);

                    if (regexPos.size() == 0) {
                        currentSplit.emplace_back(0);
                        collectAllPossibleSplits_regex(pos, str, pMax, elementNames, currentSplit, allPossibleSplits);
                        currentSplit.pop_back();
                    }
                    else {
                        if (loop == true) /* assign value < 0 */
                            for (unsigned i = 0 ; i < regexPos.size(); ++i) {
                                /* because of loop, do not care about 0 iteration */
                                int tmp = (contentLength * regexPos[i]) % str.length();
                                if (tmp == 0)
                                    currentSplit.emplace_back(MINUSZERO);
                                else
                                    currentSplit.emplace_back(-tmp);
                                collectAllPossibleSplits_regex((pos + contentLength * regexPos[i]) % str.length(), str, pMax, elementNames, currentSplit, allPossibleSplits);
                                currentSplit.pop_back();
                            }
                        else
                            for (unsigned i = 0 ; i < regexPos.size(); ++i) { /* assign value >= 0 */
                                int tmp = (pos + contentLength * regexPos[i]) % str.length();
                                currentSplit.emplace_back(contentLength * regexPos[i]);
                                collectAllPossibleSplits_regex(tmp, str, pMax, elementNames, currentSplit, allPossibleSplits);
                                currentSplit.pop_back();
                            }
                    }
                }

                else {
                    for (unsigned i = 0; i < str.length(); ++i) { /* assign value < 0 because it can iterate many times */
                        int length = i;
                        if (length == 0)
                            currentSplit.emplace_back(MINUSZERO);
                        else
                            currentSplit.emplace_back(- length);
                        collectAllPossibleSplits_regex((pos + length) % str.length(), str, pMax, elementNames, currentSplit, allPossibleSplits);
                        currentSplit.pop_back();
                    }
                }
            }

            /*
             * Given a flat,
             * generate its size constraint
             */
            std::string generateVarSize(std::pair<std::string, int> a, std::string l_r_hs = ""){
                std::string result = "";
                if (a.second >= 0) {
                    /* simpler version */
                    result += LENPREFIX;
                    result += a.first;
                }
                else {
                    /* const string */
                    SASSERT (constMap.find(a.first) != constMap.end());
                    result += LENPREFIX;
                    result += constMap[a.first];
                }
                return result;
            }

            /*
             * Given a flat,
             * generate its size constraint
             */
            std::string generateFlatSize(std::pair<std::string, int> a, std::string l_r_hs = ""){
                std::string result = "";
                if (a.second >= 0) {
                    /* simpler version */
                    result += LENPREFIX;
                    result += a.first;
                    result += "_";
                    result += std::to_string(a.second);
                }
                else {
                    /* const string */
                    SASSERT (l_r_hs.length() > 0);

                    SASSERT (constMap.find(a.first) != constMap.end());
                    result += LENPREFIX;
                    result += constMap[a.first];
                    result += "_";
                    result += std::to_string(std::abs(a.second));
                }
                return result;
            }

            /*
             *
             */
            std::string generateFlatIter(std::pair<std::string, int> a){

                std::string result = "";
                if (a.second >= 0) {
                    /* simpler version */
                    result += a.first;
                    result += "_";
                    result += std::to_string(a.second);
                    result += ITERSUFFIX;
                }
                else {
                    /* const string */
                    SASSERT (constMap.find(a.first) != constMap.end());
//			if (isRegexStr(a.first) || isUnionStr(a.first)){
//				result += constMap[a.first];
//				result += "_";
//				result += std::to_string(std::abs(a.second));
//				result += ITERSUFFIX;
//			}
//			else
                    result = "1";
                }
                return result;
            }

            /*
             * Given a flat,
             * generate its array name
             */
            std::string generateFlatArray(std::pair<std::string, int> a, std::string l_r_hs = ""){
                std::string result = "";
                if (a.second >= 0) {
                    /* simpler version */
                    result += ARRPREFIX;
                    result += a.first;
                }
                else {
                    /* const string */
                    SASSERT (l_r_hs.length() > 0);
                    result += ARRPREFIX;
                    result += constMap[a.first];
                }
                return result;
            }

            /*
             * Given a flat,
             * generate its array name
             */
            std::string generateFlatArray_forComponent(std::pair<std::string, int> a, std::string l_r_hs = ""){
                SASSERT(a.second != REGEX_CODE);
                std::string result =  generateFlatArray(a, l_r_hs) + "_" + std::to_string(a.second);
                return result;
            }

            std::string addConstraint(std::vector<std::string> elements) {
                std::string result = "";
                if (elements.size() > 1) {
                    result = "(+ ";
                    for (unsigned int i = 0; i < elements.size(); ++i)
                        result = result + elements[i] + " ";
                    result = result + ")";
                }
                else if (elements.size() == 1){
                    result = elements[0];
                }
                else
                    result = ZERO;
                return result;
            }

            /*
             * (+ a b c)
             */
            std::string addConstraint_full(std::vector<std::string> elements) {
                std::string result = "";
                if (elements.size() == 0)
                    return ZERO;
                if (elements.size() == 1)
                    return elements[0];
                if (elements.size() > 1) {
                    result = "(+ ";
                    for (unsigned i = 0; i < elements.size(); ++i)
                        result = result + elements[i] + " ";
                    result = result + ")";
                }
                return result;
            }

            /*
             * Input: constA and a number of flats
             * Output: all possible ways to split constA
             */
            std::vector<std::vector<int> > collectAllPossibleSplits(
                    std::pair<std::string, int> lhs,
                    std::vector<std::pair<std::string, int> > elementNames,
                    bool optimizing){
                /* create alias elementNames with smaller number of elements*/
                std::vector<std::pair<std::string, int> > alias;
                int pre = 0;
                int cnt = 0;
                for (unsigned i = 0; i < elementNames.size(); ++i)
                    if (elementNames[i].second < 0) {
                        if (pre > 0) {
                            alias.emplace_back(std::make_pair("e" + std::to_string(cnt++), pre));
                            pre = 0;
                        }
                        alias.emplace_back(elementNames[i]);
                    }
                    else
                        pre++;
                if (pre > 0)
                    alias.emplace_back(std::make_pair("e" + std::to_string(cnt++), pre));

                /* use alias instead of elementNames */
                std::vector<std::vector<int> > allPossibleSplits;
                SASSERT(lhs.second < 0);

                if (lhs.second == REGEX_CODE) /* regex */ {
                    std::vector<int> curr;
                    std::string regexContent = parse_regex_content(lhs.first);
                    collectAllPossibleSplits_regex(0, regexContent, 10, alias, curr, allPossibleSplits);
                }
                else if (lhs.second % QMAX == 0) /* tail */ {
                    if (optimizing){
                        std::vector<int> curr;
                        collectAllPossibleSplits_const(0, lhs.first, 10, alias, curr, allPossibleSplits);
                    }
                    else for (unsigned i = 0; i <= lhs.first.length(); ++i) {
                            std::vector<int> curr;
                            collectAllPossibleSplits_const(0, lhs.first.substr(i), 10, alias, curr, allPossibleSplits);
                        }
                }
                else if (lhs.second % QMAX == -1) /* head */ {
                    if (QCONSTMAX == 1 || optimizing) {
                        std::vector<int> curr;
                        collectAllPossibleSplits_const(0, lhs.first, 10, alias, curr, allPossibleSplits);
                    }
                    else for (unsigned i = 0; i <= lhs.first.length(); ++i) {
                            std::vector<int> curr;

                            collectAllPossibleSplits_const(0, lhs.first.substr(0, i), 10, alias, curr, allPossibleSplits);

                        }
                }
                else {
                    STRACE("str", tout << __LINE__ << " " << lhs.first << " --- " << lhs.second << ": " << lhs.second % QMAX << std::endl;);
                    SASSERT(false);
                }

                /* print test */
                STRACE("str", tout << __LINE__ <<  " ***" << __FUNCTION__ << "***" << std::endl;);
                for (unsigned int i = 0; i < allPossibleSplits.size(); ++i){
                    splitPrintTest(allPossibleSplits[i], "Accepted");
                }

                return allPossibleSplits;
            }

            /*
             * a b c
             */
            std::string addConstraint_half(std::vector<std::string> elements) {
                std::string result = "";
                if (elements.size() == 0)
                    return ZERO;
                if (elements.size() == 1)
                    return elements[0];
                if (elements.size() > 1) {
                    result = "";
                    for (unsigned int i = 0; i < elements.size(); ++i)
                        result = result + elements[i] + " ";
                }
                return result;
            }

            /*
             * pre elements + pre fix of itself
             */
            std::string leng_prefix_lhs(std::pair<std::string, int> a,
                                        std::vector<std::pair<std::string, int>> elementNames,
                                        std::string lhs, std::string rhs,
                                        int pos,
                                        bool optimizing,
                                        bool unrollMode) {
                std::vector<std::string> addElements;

                if (a.second != REGEX_CODE && !optimizing && unrollMode) {
                    if (a.second % QCONSTMAX != -1)
                        for (int i = a.second + 1; i < 0; ++i){ /* prefix of a - const */
                            addElements.emplace_back(
                                    createMultiplyOperator(
                                            generateFlatSize(std::make_pair(a.first, i), lhs),
                                            generateFlatIter(std::make_pair(a.first, i))));
                            if (i % QCONSTMAX == -1)
                                break;
                        }

                    if (a.second % QMAX != 0)
                        for (int i = a.second - 1; i >= 0; --i){ /* a is var */
                            addElements.emplace_back(
                                    createMultiplyOperator(
                                            generateFlatSize(std::make_pair(a.first, i), lhs),
                                            generateFlatIter(std::make_pair(a.first, i))));
                            if (i % QMAX == 0)
                                break;
                        }
                }

                for (int i = pos - 1; i >= 0; --i) { /* pre-elements */
                    addElements.emplace_back(
                            createMultiplyOperator(
                                    generateFlatSize(elementNames[i], rhs),
                                    generateFlatIter(elementNames[i])));
                }

                return addConstraint_half(addElements);
            }

            /*
             *  pre fix of itself
             */
            std::string leng_prefix_rhs(
                    std::pair<std::string, int> a, /* var */
                    std::string rhs,
                    bool unrollMode) {
                std::vector<std::string> addElements;
                if (a.second != REGEX_CODE && unrollMode) {
                    if (a.second % QCONSTMAX != -1)
                        for (int i = a.second + 1; i < 0; ++i){ /* a is const */
                            addElements.emplace_back(createMultiplyOperator(generateFlatSize(std::make_pair(a.first, i), rhs), generateFlatIter(std::make_pair(a.first, i))));
                            if (i % QCONSTMAX == -1)
                                break;
                        }

                    if (a.second % QMAX != 0)
                        for (int i = a.second - 1; i >= 0; --i){ /* a is var */
                            addElements.emplace_back(createMultiplyOperator(generateFlatSize(std::make_pair(a.first, i), rhs), generateFlatIter(std::make_pair(a.first, i))));
                            if (i % QMAX == 0)
                                break;
                        }
                }
                else {
                    // skip
                }

                return addConstraint_half(addElements);
            }

            /*
             * 0: No const, No connected var
             * 1: const		No connected var
             * 2: no const, connected var
             * 3: have both
             */
            int findSplitType(
                    std::vector<std::pair<std::string, int>> elementNames,
                    std::map<std::string, int> connectedVariables){

                bool havingConst = false;
                bool havingConnectedVar = false;

                /* check if containing const | regex */
                for (unsigned int i = 0 ; i < elementNames.size(); ++i)
                    if (elementNames[i].second < 0) {
                        havingConst = true;
                        break;
                    }

                /* check if containing connected vars */
                for (unsigned int i = 0 ; i < elementNames.size(); ++i)
                    if (connectedVariables.find(elementNames[i].first) != connectedVariables.end()) {
                        havingConnectedVar = true;
                        break;
                    }

                if (!havingConnectedVar && !havingConst)
                    return SIMPLE_CASE;
                else if (!havingConnectedVar && havingConst)
                    return CONST_ONLY;
                else if (havingConnectedVar && !havingConst)
                    return CONNECTED_ONLY;
                else
                    return CONST_CONNECTED;
            }

            /*
             *
             */
            std::string lengthConstraint_toConnectedVarConstraint(
                    std::pair<std::string, int> a, /* const || regex */
                    std::vector<std::pair<std::string, int> > elementNames,
                    std::vector<std::string> subElements,
                    int currentPos,
                    int subLength,
                    std::string lhs, std::string rhs,
                    std::map<std::string, int> connectedVariables,
                    bool optimizing,
                    int pMax){
                int connectedVarPos = -1;
                int connectedVarCnt = 0;
                std::string constraint = "";
                for (int i = currentPos - subElements.size() + 1; i <= currentPos; ++i)
                    if (connectedVariables.find(elementNames[i].first) != connectedVariables.end()) {
                        connectedVarPos = i;
                        connectedVarCnt += 1;
                        constraint += connectedVar_atSpecificLocation(
                                a, /* const or regex */
                                elementNames, /* have connected var */
                                connectedVarPos,
                                subLength,
                                lhs, rhs,
                                connectedVariables,
                                optimizing,
                                pMax);
                    }

                if (connectedVarCnt == 0 || constraint.length() < 3)
                    return "";
                else if (connectedVarCnt == 1)
                    return constraint;
                else
                    return "(and " + constraint + ")";
            }

            /*
             * Input: split a string
             * Output: SMT
             */
            std::string toConstraint_havingConnectedVar_andConst(
                    std::pair<std::string, int> a, /* const || regex */
                    std::vector<std::pair<std::string, int> > elementNames, /* const + connected var */
                    std::vector<int> split,
                    std::string lhs, std::string rhs,
                    std::map<std::string, int> connectedVariables,
                    bool optimizing,
                    int pMax){
//		__debugPrint(logFile, "%d const|regex = const + connected var\n", __LINE__);
                int totalLength = 0;
                for (unsigned int j = 0; j < split.size(); ++j)
                    if (split[j] > 0 && split[j] != MINUSZERO)
                        totalLength = totalLength + split[j];
                    else {
                        totalLength = -1;
                        break;
                    }

                std::vector<std::string> strAnd;
                std::string lhs_length = "";
                if (optimizing)
                    lhs_length = generateVarSize(a, lhs);
                else
                    lhs_length = generateFlatSize(a, lhs);

                if (totalLength > 0) /* only has const, does not have regex */ {
                    strAnd.emplace_back(createEqualConstraint(lhs_length, std::to_string(totalLength)));
                }
                std::vector<std::string> addElements;

                addElements.clear();
                unsigned int splitPos = 0;

                std::string content = "";
                if (a.second == REGEX_CODE)
                    content = parse_regex_content(a.first);

                for (unsigned i = 0; i < elementNames.size(); ++i){
                    if (elementNames[i].second >= 0) /* not const */ {
                        addElements.emplace_back(createMultiplyOperator(generateFlatSize(elementNames[i]),
                                                                        generateFlatIter(elementNames[i])));
                    }
                    else { /* const */
                        if (addElements.size() > 0){ /* create a sum for previous elements */
                            std::string constraintForConnectedVar = lengthConstraint_toConnectedVarConstraint(
                                    a, /* const or regex */
                                    elementNames, /* have connected var */
                                    addElements,
                                    i - 1,
                                    split[splitPos],
                                    lhs, rhs,
                                    connectedVariables,
                                    optimizing,
                                    pMax);
                            strAnd.emplace_back(constraintForConnectedVar);
                            if (split[splitPos] == MINUSZERO) {
                                /* looping */
                                SASSERT(a.second == REGEX_CODE);
                                strAnd.emplace_back(createEqualConstraint(ZERO, createModOperator(addConstraint_full(addElements), std::to_string(content.length()))));
                            }
                            else if (split[splitPos] < 0) {
                                /* looping */
                                SASSERT(a.second == REGEX_CODE);
                                strAnd.emplace_back(createEqualConstraint(createModOperator(addConstraint_full(addElements), std::to_string(content.length())),
                                                                          std::to_string(std::abs(split[splitPos]))));
                            }
                            else {
                                strAnd.emplace_back(createEqualConstraint(addConstraint_full(addElements), std::to_string(split[splitPos])));
                            }
                            splitPos++;
                            addElements.clear();

                        }

                        if (elementNames[i].second % QCONSTMAX == -1 && i < elementNames.size() - 1) {
                            if (QCONSTMAX == 1 || elementNames[i].first.length() == 1) {
                                strAnd.emplace_back(createEqualConstraint(generateFlatSize(elementNames[i], rhs), std::to_string(split[splitPos])));
                                splitPos++;
                            }
                            else {
                                assert(elementNames[i + 1].second % QCONSTMAX == 0);
                                strAnd.emplace_back(createEqualConstraint(
                                        "(+ " + generateFlatSize(elementNames[i], rhs) + " " + generateFlatSize(elementNames[i + 1], rhs) + ")",
                                        std::to_string(split[splitPos] + split[splitPos + 1])));
                                i++;
                                splitPos += 2;
                            }
                        }
                        else {
                            if (split[splitPos] == MINUSZERO) {
                                /* looping at 0 */
                                SASSERT(elementNames[i].second == REGEX_CODE);
                                SASSERT(a.second == REGEX_CODE);
                                strAnd.emplace_back(createEqualConstraint(
                                        ZERO,
                                        createModOperator(generateFlatSize(elementNames[i], rhs), std::to_string(content.length()))));
                                splitPos++;
                            }
                            else if (split[splitPos] < 0) {
                                /* looping */
                                SASSERT(elementNames[i].second == REGEX_CODE);
                                SASSERT(a.second == REGEX_CODE);
                                strAnd.emplace_back(createEqualConstraint(
                                        createModOperator(generateFlatSize(elementNames[i], rhs), std::to_string(content.length())),
                                        std::to_string(std::abs(split[splitPos++]))));
                            }
                            else
                                strAnd.emplace_back(createEqualConstraint(
                                        generateFlatSize(elementNames[i], rhs),
                                        std::to_string(split[splitPos++])));
                        }
                    }
                }

                if (addElements.size() > 0) {
                    std::string constraintForConnectedVar = lengthConstraint_toConnectedVarConstraint(
                            a, /* const or regex */
                            elementNames, /* have connected var */
                            addElements,
                            elementNames.size() - 1,
                            split[splitPos],
                            lhs, rhs,
                            connectedVariables,
                            optimizing,
                            pMax);
                    strAnd.emplace_back(constraintForConnectedVar);

                    /* create a sum for previous elements */
                    if (split[splitPos] == MINUSZERO) {
                        /* looping */
                        SASSERT(a.second == REGEX_CODE);
                        strAnd.emplace_back(createEqualConstraint(
                                ZERO,
                                createModOperator(addConstraint_full(addElements), std::to_string(content.length()))));
                    }
                    else if (split[splitPos] < 0) {
                        /* looping */
                        SASSERT(a.second == REGEX_CODE);
                        strAnd.emplace_back(createEqualConstraint(
                                createModOperator(addConstraint_full(addElements), std::to_string(content.length())),
                                std::to_string(std::abs(split[splitPos]))));
                    }
                    else {
                        strAnd.emplace_back(createEqualConstraint(addConstraint_full(addElements), std::to_string(split[splitPos])));
                    }
                    splitPos++;
                }
                SASSERT(splitPos == split.size());
                return andConstraint(strAnd);
            }

            /*
             * Input: split a string
             * Output: SMT
             */
            std::string toConstraint_NoConnectedVar(
                    std::pair<std::string, int> a, /* const || regex */
                    std::vector<std::pair<std::string, int> > elementNames, /* no connected var */
                    std::vector<int> split,
                    std::string lhs, std::string rhs,
                    bool optimizing){
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ <<  " const|regex = const + ..." << std::endl;);

                int totalLength = 0;
                for (unsigned j = 0; j < split.size(); ++j)
                    if (split[j] > 0 && split[j] != MINUSZERO)
                        totalLength = totalLength + split[j];
                    else {
                        totalLength = -1;
                        break;
                    }

                std::vector<std::string> strAnd;
                std::string lenLhs = "";
                if (optimizing)
                    lenLhs = generateVarSize(a, lhs);
                else
                    lenLhs = generateFlatSize(a, lhs);
                if (totalLength > 0) /* only has const, does not have regex */
                    strAnd.emplace_back(createEqualConstraint(lenLhs, std::to_string(totalLength)));

                std::vector<std::string> addElements;

                /* simple case: check if size of all consts = 0 */
                bool sumConst_0 = true, metVar = false;
                unsigned splitPos = 0;
                for (unsigned i = 0; i < elementNames.size(); ++i) {
                    if (elementNames[i].second < 0) {
                        if (metVar)
                            splitPos++;
                        if (split[splitPos++] > 0){
                            sumConst_0 = false;
                            break;
                        }
                        addElements.emplace_back(createMultiplyOperator(
                                generateFlatSize(elementNames[i], rhs),
                                generateFlatIter(elementNames[i])));
                        metVar = false;
                    }
                    else
                        metVar = true;
                }

                if (sumConst_0 == true) {
                    return createEqualConstraint(ZERO, addConstraint_full(addElements));
                }

                /* work as usual */
                addElements.clear();
                splitPos = 0;
                std::string content = "";
                if (a.second == REGEX_CODE)
                    content = parse_regex_content(a.first);

                for (unsigned i = 0; i < elementNames.size(); ++i){
                    if (elementNames[i].second >= 0) /* not const */ {
                        addElements.emplace_back(createMultiplyOperator(generateFlatSize(elementNames[i]),
                                                                        generateFlatIter(elementNames[i])));
                    }
                    else { /* const */
                        if (addElements.size() > 0){ /* create a sum for previous elements */
                            if (split[splitPos] == MINUSZERO) {
                                /* looping */
                                SASSERT(a.second == REGEX_CODE);
                                strAnd.emplace_back(createEqualConstraint(ZERO, createModOperator(addConstraint_full(addElements), std::to_string(content.length()))));
                            }
                            else if (split[splitPos] < 0) {
                                /* looping */
                                SASSERT(a.second == REGEX_CODE);
                                strAnd.emplace_back(createEqualConstraint(createModOperator(addConstraint_full(addElements), std::to_string(content.length())), std::to_string(std::abs(split[splitPos]))));
                            }
                            else {
                                strAnd.emplace_back(createEqualConstraint(addConstraint_full(addElements), std::to_string(split[splitPos])));
                            }
                            splitPos++;
                            addElements.clear();
                        }

                        if (elementNames[i].second % QCONSTMAX == -1 && i < elementNames.size() - 1) {
                            if (QCONSTMAX == 1 || elementNames[i].first.length() == 1) {
                                strAnd.emplace_back(createEqualConstraint(generateFlatSize(elementNames[i], rhs), std::to_string(split[splitPos])));
                                splitPos++;
                            }
                            else {
                                assert(elementNames[i + 1].second % QCONSTMAX == 0);
                                strAnd.emplace_back(createEqualConstraint("(+ " + generateFlatSize(elementNames[i], rhs) + " " + generateFlatSize(elementNames[i + 1], rhs) + ")", std::to_string(split[splitPos] + split[splitPos + 1])));
                                i++;
                                splitPos += 2;
                            }
                        }
                        else {
                            if (split[splitPos] == MINUSZERO) {
                                /* looping at 0 */
                                SASSERT(elementNames[i].second == REGEX_CODE);
                                SASSERT(a.second == REGEX_CODE);
                                strAnd.emplace_back(createEqualConstraint(
                                        ZERO,
                                        createModOperator(generateFlatSize(elementNames[i], rhs), std::to_string(content.length()))));
                                splitPos++;
                            }
                            else if (split[splitPos] < 0) {
                                /* looping */
                                SASSERT(elementNames[i].second == REGEX_CODE);
                                SASSERT(a.second == REGEX_CODE);
                                strAnd.emplace_back(createEqualConstraint(
                                        createModOperator(generateFlatSize(elementNames[i], rhs), std::to_string(content.length())),
                                        std::to_string(std::abs(split[splitPos++]))));
                            }
                            else
                                strAnd.emplace_back(createEqualConstraint(generateFlatSize(elementNames[i], rhs), std::to_string(split[splitPos++])));
                        }
                    }
                }

                if (addElements.size() > 0) {
                    /* create a sum for previous elements */
                    if (split[splitPos] == MINUSZERO) {
                        /* looping */
                        SASSERT(a.second == REGEX_CODE);
                        strAnd.emplace_back(createEqualConstraint(ZERO, createModOperator(addConstraint_full(addElements), std::to_string(content.length()))));
                    }
                    else if (split[splitPos] < 0) {
                        /* looping */
                        SASSERT(a.second == REGEX_CODE);
                        strAnd.emplace_back(createEqualConstraint(
                                createModOperator(addConstraint_full(addElements), std::to_string(content.length())),
                                std::to_string(std::abs(split[splitPos]))));
                    }
                    else {
                        strAnd.emplace_back(createEqualConstraint(addConstraint_full(addElements), std::to_string(split[splitPos])));
                    }
                    splitPos++;
                }
                SASSERT(splitPos == split.size());
                return andConstraint(strAnd);
            }

            /*
             * elementNames[pos] is a connected.
             * how many parts of that connected variable are in the const | regex
             */
            int find_partsOfConnectedVariablesInAVector(
                    int pos,
                    std::vector<std::pair<std::string, int>> elementNames,
                    std::string &subLen){
                int partCnt = 1;
                std::vector<std::string> addElements;
                addElements.emplace_back(generateFlatSize(elementNames[pos]));
                unsigned int j = pos + 1;
                for (j = pos + 1; j < elementNames.size(); ++j)
                    if (elementNames[j].second > elementNames[j - 1].second &&
                        elementNames[j].second > 0 &&
                        elementNames[j].first.compare(elementNames[j - 1].first) == 0 &&
                        elementNames[j].second % QMAX != 0 &&
                        elementNames[j].second != REGEX_CODE) {
                        partCnt++;
                        addElements.emplace_back(createMultiplyOperator(generateFlatSize(elementNames[j]),
                                                                        generateFlatIter(elementNames[j])));
                    }
                    else
                        break;

                /* sublen = part_1 + part2 + .. */
                subLen = addConstraint_full(addElements);
                return partCnt;
            }

            /*
             *
             */
            std::string toConstraint_ConnectedVar(
                    std::pair<std::string, int> a, /* const or regex */
                    std::vector<std::pair<std::string, int>> elementNames, /* have connected var, do not have const */
                    std::string lhs, std::string rhs,
                    std::map<std::string, int> connectedVariables,
                    bool optimizing,
                    int pMax){
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ <<  " const|regex = connected var + ..." << std::endl;);

                std::string arrayLhs = generateFlatArray(a, lhs);
                std::vector<std::string> resultParts;

                std::string content = "";
                if (a.second == REGEX_CODE)
                    content = parse_regex_content(a.first);
                else
                    content = a.first;

                bool unrollMode = PMAX == pMax;
                for (unsigned i = 0; i < elementNames.size(); ++i){
                    SASSERT(elementNames[i].second >= 0);
                    if (elementNames[i].second >= 0) /* not const */ {

                        /* connected variable */
                        if (connectedVariables.find(elementNames[i].first) != connectedVariables.end()) {

                            /* sublen = part_1 + part2 + .. */
                            std::string subLen = "";
                            int partCnt = find_partsOfConnectedVariablesInAVector(i, elementNames, subLen);
                            std::string prefix_rhs = leng_prefix_rhs(elementNames[i], rhs, unrollMode);
                            std::string prefix_lhs = leng_prefix_lhs(a, elementNames, lhs, rhs, i, optimizing, false);

                            if (a.second == REGEX_CODE) {
                                std::vector<std::string> conditions;
                                if (partCnt == 1) {
                                    STRACE("str", tout << __LINE__ << " const|regex = connected var partCnt = 1. NOT TESTED " << std::endl;);
                                    /* this part = regex */
                                    /* prefix mod lenth = 0 */
                                    conditions.emplace_back(createEqualConstraint(ZERO, createModOperator(prefix_rhs, std::to_string(content.length()))));
                                    conditions.emplace_back(createEqualConstraint(ZERO, createModOperator(subLen, std::to_string(content.length()))));

#if 0
                                    std::string partArray = generateFlatArray_forComponent(elementNames[i], rhs);
							for (unsigned int j = 0; j < content.length(); ++j)
								subcase.emplace_back(createEqualConstraint(createSelectConstraint(partArray, std::to_string(j)), std::to_string(content[j])));

#else
                                    std::string arrName = generateFlatArray(elementNames[i], rhs);
                                    std::string prefix = leng_prefix_rhs(elementNames[i], rhs, unrollMode);

                                    std::vector<std::string> cases;
                                    for (unsigned iter = 0; iter < connectingSize / content.length(); ++iter) {
                                        std::vector<std::string> subcase;
                                        subcase.emplace_back(createEqualConstraint(subLen, std::to_string(iter * content.length())));
                                        for (unsigned int j = 0; j < iter * content.length(); ++j)
                                            subcase.emplace_back(createEqualConstraint(createSelectConstraint(arrName, "(+ " + prefix + " " + std::to_string(j) + ")"), std::to_string(content[j % content.length()])));
                                        cases.emplace_back(andConstraint(subcase));
                                    }
                                    conditions.emplace_back(orConstraint(cases));
#endif

                                    resultParts.emplace_back(andConstraint(conditions));
                                    STRACE("str", tout << __LINE__ << " --> " << andConstraint(conditions) << std::endl;);
                                }
                                else {
                                    STRACE("str", tout << __LINE__ << " const|regex = connected var partCnt = 2. " << std::endl;);
                                    SASSERT(partCnt == 2);

                                    /* this part = regex */
                                    /* prefix mod lenth = 0 */
                                    conditions.emplace_back(createEqualConstraint(ZERO, createModOperator(prefix_rhs, std::to_string(content.length()))));
                                    conditions.emplace_back(createEqualConstraint(ZERO, createModOperator(subLen, std::to_string(content.length()))));

                                    std::string arrName = generateFlatArray(elementNames[i], rhs);
                                    for (unsigned iter = 0; iter < connectingSize / content.length(); ++iter) {
                                        for (unsigned int j = 0; j < content.length(); ++j)
                                            conditions.emplace_back(createEqualConstraint(createSelectConstraint(arrName, std::to_string(j + iter * content.length())), std::to_string(content[j])));
                                    }
                                    resultParts.emplace_back(andConstraint(conditions));
                                    STRACE("str", tout << __LINE__ << " --> " << andConstraint(conditions) << std::endl;);
                                }
                            }
                            else {
                                bool lhs_zero = false;
                                bool rhs_zero = false;
                                if (prefix_lhs.length() == 1 && prefix_lhs[0] == '0')
                                    lhs_zero = true;
                                if (prefix_rhs.length() == 1 && prefix_rhs[0] == '0')
                                    rhs_zero = true;

                                std::string arrayRhs = generateFlatArray(elementNames[i], rhs);

                                if (QCONSTMAX == 1) {
                                    resultParts.emplace_back(createEqualConstraint(subLen, std::to_string(content.length())));
                                    for (unsigned k = 0; k < content.length(); ++k){
                                        resultParts.emplace_back(createEqualConstraint(
                                                createSelectConstraint(arrayLhs, createPlusOperator(std::to_string(k), prefix_lhs)),
                                                createSelectConstraint(arrayRhs, createPlusOperator(std::to_string(k), prefix_rhs))));
                                    }
                                }
                                else {
                                    /* exists and forall */
#if 0
                                    char strTmp[1000];
							sprintf(strTmp, "(exists ((%s Int)) (implies (and (< %s %d) (< %s %d))) (forall ((i Int)) (and (< i %s) (= (select %s i) (select %s i)))))",
									subLen.c_str(),
									subLen.c_str(),
									LOCALSPLITMAX,
									a.first.length(),
									subLen.c_str(),
									arrayLhs.c_str(),
									arrayRhs.c_str());
							__debugPrint(logFile, "%d %s\n", __LINE__, strTmp);
#endif
                                    int localSplit = connectedVariables[elementNames[i].first];
                                    std::vector<std::string> possibleCases; /* sublen = 0 || sublen = 1 || .. */
                                    if (!unrollMode) {
                                        for (int j = 0; j <= std::min(localSplit, (int)content.length()); j++){
                                            std::vector<std::string> subpossibleCases; /*at_0 = x && at_1 == y && ..*/
                                            subpossibleCases.emplace_back(createEqualConstraint(subLen, std::to_string(j)));
                                            for (int k = 0; k < j; ++k){
                                                subpossibleCases.emplace_back(createEqualConstraint(
                                                        createSelectConstraint(arrayLhs, createPlusOperator(std::to_string(k), prefix_lhs)),
                                                        createSelectConstraint(arrayRhs,
                                                                               createModOperator(createPlusOperator(std::to_string(k), prefix_rhs), std::to_string(pMax))
                                                        )));
                                            }
                                            possibleCases.emplace_back(andConstraint(subpossibleCases));
                                        }
                                    }
                                        /* clone to optimise length of generated string */
                                    else if (lhs_zero && rhs_zero) {
                                        for (int j = 0; j <= std::min(localSplit, (int)content.length()); j++){
                                            std::vector<std::string> subpossibleCases; /*at_0 = x && at_1 == y && ..*/
                                            subpossibleCases.emplace_back(createEqualConstraint(subLen, std::to_string(j)));
                                            for (int k = 0; k < j; ++k){
                                                subpossibleCases.emplace_back(createEqualConstraint(
                                                        createSelectConstraint(arrayLhs, std::to_string(k)),
                                                        createSelectConstraint(arrayRhs, std::to_string(k))));
                                            }
                                            possibleCases.emplace_back(andConstraint(subpossibleCases));
                                        }
                                    }
                                    else if (lhs_zero && !rhs_zero){
                                        for (int j = 0; j <= std::min(localSplit, (int)content.length()); j++){
                                            std::vector<std::string> subpossibleCases; /*at_0 = x && at_1 == y && ..*/
                                            subpossibleCases.emplace_back(createEqualConstraint(subLen, std::to_string(j)));
                                            for (int k = 0; k < j; ++k){
                                                subpossibleCases.emplace_back(createEqualConstraint(
                                                        createSelectConstraint(arrayLhs, std::to_string(k)),
                                                        createSelectConstraint(arrayRhs,  createPlusOperator(std::to_string(k), prefix_rhs))));
                                            }
                                            possibleCases.emplace_back(andConstraint(subpossibleCases));
                                        }
                                    }
                                    else if (!lhs_zero && rhs_zero){
                                        for (int j = 0; j <= std::min(localSplit, (int)content.length()); j++){
                                            std::vector<std::string> subpossibleCases; /*at_0 = x && at_1 == y && ..*/
                                            subpossibleCases.emplace_back(createEqualConstraint(subLen, std::to_string(j)));
                                            for (int k = 0; k < j; ++k){
                                                subpossibleCases.emplace_back(createEqualConstraint(
                                                        createSelectConstraint(arrayLhs, createPlusOperator(std::to_string(k), prefix_lhs)),
                                                        createSelectConstraint(arrayRhs, std::to_string(k))));
                                            }
                                            possibleCases.emplace_back(andConstraint(subpossibleCases));
                                        }
                                    }
                                    else for (int j = 0; j <= std::min(localSplit, (int)content.length()); j++){
                                            std::vector<std::string> subpossibleCases; /*at_0 = x && at_1 == y && ..*/
                                            subpossibleCases.emplace_back(createEqualConstraint(subLen, std::to_string(j)));
                                            for (int k = 0; k < j; ++k){
                                                subpossibleCases.emplace_back(createEqualConstraint(
                                                        createSelectConstraint(arrayLhs, createPlusOperator(std::to_string(k), prefix_lhs)),
                                                        createSelectConstraint(arrayRhs,  createPlusOperator(std::to_string(k), prefix_rhs))));
                                            }
                                            possibleCases.emplace_back(andConstraint(subpossibleCases));
                                        }
                                    possibleCases.push_back(createLessConstraint(std::to_string(std::min(localSplit, (int)content.length())), subLen));
                                    resultParts.emplace_back(orConstraint(possibleCases));
                                }
                            }
                            i += (partCnt - 1);
                        }
                    }
                }

                return andConstraint(resultParts);
            }

            /*
             *
             */
            std::string connectedVar_atSpecificLocation(
                    std::pair<std::string, int> a, /* const or regex */
                    std::vector<std::pair<std::string, int>> elementNames, /* have connected var */
                    int connectedVarPos,
                    int connectedVarLength,
                    std::string lhs, std::string rhs,
                    std::map<std::string, int> connectedVariables,
                    bool optimizing,
                    int pMax){
                bool unrollMode = pMax == PMAX;
                std::vector<std::string> resultParts;

                std::string content = "";
                if (a.second == REGEX_CODE)
                    content = parse_regex_content(a.first);
                else
                    content = a.first;

                SASSERT(connectedVariables.find(elementNames[connectedVarPos].first) != connectedVariables.end());

                /* how many parts of that connected variable are in the const | regex */
                /* sublen = part_1 + part2 + .. */
                std::string subLen = "";
                find_partsOfConnectedVariablesInAVector(connectedVarPos, elementNames, subLen);

                std::string prefix_rhs = leng_prefix_rhs(elementNames[connectedVarPos], rhs, unrollMode);
                std::string prefix_lhs = leng_prefix_lhs(a, elementNames, lhs, rhs, connectedVarPos, optimizing, false);

                std::string arrayRhs = generateFlatArray(elementNames[connectedVarPos], rhs);
                std::string arrayLhs = generateFlatArray(a, lhs);

                if (connectedVarLength >= 0 && connectedVarLength != MINUSZERO) {
                    /* sublen = connectedVarLength */
                    /* at_0 = x && at_1 == y && ..*/
                    int considerLength = connectedVarLength;
                    if (connectedVariables[elementNames[connectedVarPos].first] >= 0)
                        considerLength = std::min(connectedVariables[elementNames[connectedVarPos].first], considerLength);

                    for (int k = 0; k < considerLength; ++k){
                        resultParts.emplace_back(createEqualConstraint(
                                createSelectConstraint(arrayLhs, createPlusOperator(std::to_string(k), prefix_lhs)),
                                createSelectConstraint(arrayRhs, createPlusOperator(std::to_string(k), prefix_rhs))));
                    }
                }
                else {
                    SASSERT(a.second == REGEX_CODE);
                    /* at_0 = x && at_1 == y && ..*/
                    char strTmp[1000];
                    std::string len_connectedVar = generateFlatSize(elementNames[connectedVarPos], rhs);
#if 0
                    sprintf(strTmp, "(forall ((i Int)) (implies (and (< i %s) (>= i 0)) (= (select %s (+ i %s)) (select %s (mod (+ i %s) %ld)))))",
					subLen.c_str(),
					arrayRhs.c_str(),
					prefix_rhs.c_str(),
					arrayLhs.c_str(),
					prefix_lhs.c_str(),
					content.length());
			resultParts.emplace_back(strTmp);
#else
                    if (!unrollMode){
                        for (int i = 0; i < (int)content.length(); ++i){
                            sprintf(strTmp, "(or (= (select %s %d) (select %s (mod (+ %d %s) %ld))) (< %s %d))",
                                    arrayRhs.c_str(),
                                    i,
                                    arrayLhs.c_str(),
                                    i,
                                    prefix_lhs.c_str(),
                                    content.length(),
                                    len_connectedVar.c_str(),
                                    i + 1);
                            resultParts.emplace_back(strTmp);
                        }
                        resultParts.emplace_back(createImpliesOperator(
                                createLessConstraint(len_connectedVar, std::to_string(content.length())),
                                createEqualConstraint(generateFlatIter(elementNames[connectedVarPos]), "1")));
                    }
                    else {
                        resultParts.emplace_back(createLessEqualConstraint(subLen, std::to_string(connectedVariables[elementNames[connectedVarPos].first])));

                        for (int i = 0; i < std::min(connectingSize, 50); ++i) {
                            sprintf(strTmp, "(or (= (select %s (+ %d %s)) (select %s (mod (+ %d %s) %ld))) (< %s %d))",
                                    arrayRhs.c_str(),
                                    i,
                                    prefix_rhs.c_str(),
                                    arrayLhs.c_str(),
                                    i,
                                    prefix_lhs.c_str(),
                                    content.length(),
                                    len_connectedVar.c_str(),
                                    i + 1);
                            resultParts.emplace_back(strTmp);
                        }
                    }
#endif
                }

                return andConstraint(resultParts);
            }

            /*
             * Case: X =  "abc"
             * return: (and X_0 = a && X_[1] = b && X_[1] = c)
             */
            std::string const_to_var(
                    std::pair<std::string, int> a,
                    std::string constB) {
                std::string result = "";

                std::string varName = a.first + "_" + std::to_string(a.second) + "_";
                for (unsigned int i = 0; i < constB.length(); ++i) {
                    /* constraint */
                    result += createEqualConstraint(varName + std::to_string(i), std::to_string(constB[i]));
                }
                return result;
            }

            /*
             * (a|b|c)*_xxx --> range <a, c>
             */
            std::pair<int, int> collectCharRange(std::string str){
                std::vector<std::string> components = collectAlternativeComponents(parse_regex_content(str));
                std::vector<int> tmpList;
                for (const auto& s : components)
                    if (s.length() != 1)
                        return std::make_pair(-1, -1);
                    else
                        tmpList.emplace_back(s[0]);

                if (tmpList.size() <= 1)
                    return std::make_pair(-1, -1);

                std::sort(tmpList.begin(), tmpList.end());
                for (unsigned i = 0; i < tmpList.size() - 1; ++i)
                    if (tmpList[i] + 1 != tmpList[i + 1]) {
                        return std::make_pair(-1, -1);
                    }

                return std::make_pair(tmpList[0], tmpList[tmpList.size() - 1]);
            }

            /*
             * Generate constraints for the case
             * const = T . "abc"* . Y . Z
             * connectPos: position of connected var
             */
//	std::string handle_Const_Regex(
//			std::pair<std::string, int> a,
//			std::vector<std::pair<std::string, int>> elementNames,
//			std::string lhs_str, std::string rhs_str,
//			int regexPos,
//			std::string extraConstraint = "" /* length = ? */) {
//		assert (elementNames[regexPos].second < 0);
//
//		std::vector<std::string> locationConstraint;
//		if (extraConstraint.length() > 0)
//			locationConstraint.emplace_back(extraConstraint);
//
//		/* find the start position --> */
//		std::string pre_lhs = "(+ " + leng_prefix_lhs(a, elementNames, lhs_str, rhs_str, regexPos) + " 0)";
//
//		/* optimize length of generated string */
//		std::string cntArray = generateFlatArray(elementNames[regexPos], rhs_str);
//		std::string cntLength = generateFlatSize(elementNames[regexPos], rhs_str);
//		std::vector<std::string> cases;
//		for (unsigned i = 0; i < a.first.length(); ++i) {
//			std::vector<std::string> andConstraints;
//			andConstraints.emplace_back(createEqualConstraint(pre_lhs, std::to_string(i)));
//			for (unsigned j = i; j < a.first.length(); ++j){
//				std::vector<std::string> orConstraints;
//				orConstraints.emplace_back(createEqualConstraint(
//						std::to_string(a.first[j]),
//						createSelectConstraint(cntArray, createPlusOperator(pre_rhs, std::to_string(j - i)))));
//				orConstraints.emplace_back(createLessConstraint(cntLength, std::to_string(j - i + 1)));
//				andConstraints.emplace_back(orConstraint(orConstraints));
//			}
//			cases.emplace_back(andConstraint(andConstraints));
//		}
//
//
//		return orConstraint(cases);
//	}

            /*
             * Generate constraints for the case
             * X = T . "abc"* . Y . Z
             * regexPos: position of regex element
             * return: forAll (i Int) and (i < |abc*|) (y[i + |T|] == a | b | c)
             */
            std::string handle_Regex_WithPosition_array(
                    std::pair<std::string, int> a, // connected var
                    std::vector<std::pair<std::string, int>> elementNames,
                    std::string lhs_str, std::string rhs_str,
                    int regexPos,
                    bool optimizing,
                    int pMax,
                    std::string extraConstraint = "" /* length = ? */
            ) {
                SASSERT (elementNames[regexPos].second < 0);
                bool unrollMode = pMax == PMAX;

                std::vector<std::string> locationConstraint;
                if (extraConstraint.length() > 0)
                    locationConstraint.emplace_back(extraConstraint);

                /* find the start position --> */
                std::string pre_lhs = leng_prefix_lhs(a, elementNames, lhs_str, rhs_str, regexPos, optimizing, unrollMode);

                /* optimize length of generated string */
                std::string lhs_array = generateFlatArray(a, lhs_str);
                std::string rhs_array = generateFlatArray(elementNames[regexPos], rhs_str);

                std::string regex_length = generateFlatSize(elementNames[regexPos], rhs_str);

                char strTmp[5000];

#if 0
                /* forall ((i Int)) (and (< i a.first.length()))*/
		sprintf(strTmp, "(forall ((i Int)) (implies (and (< i %s) (>= i 0)) (= (select %s (+ i %s)) (select %s (mod i %ld)))))",
				regex_length.c_str(),
				lhs_array.c_str(),
				pre_lhs.c_str(),
				rhs_array.c_str(),
				parse_regex_content(elementNames[regexPos].first).length());
		printf("%d %s\n", __LINE__, strTmp);
		return strTmp;

#else
                std::vector<std::string> andConstraints;
                andConstraints.emplace_back(createLessEqualConstraint(regex_length, std::to_string(connectingSize)));
                std::pair<int, int> charRange = collectCharRange(elementNames[regexPos].first);
                if (charRange.first != -1) {
                    if (!unrollMode) {
                        for (int i = 0; i < pMax; ++i) {
                            sprintf(strTmp, "(or (and (>= (select %s (+ %d %s)) %d) (<= (select %s (+ %d %s)) %d)) (> %d %s))",
                                    lhs_array.c_str(),
                                    i,
                                    pre_lhs.c_str(),
                                    charRange.first,

                                    lhs_array.c_str(),
                                    i,
                                    pre_lhs.c_str(),
                                    charRange.second,
                                    i + 1,
                                    generateFlatSize(elementNames[regexPos], rhs_str).c_str()
                            );
                            andConstraints.emplace_back(strTmp);
                        }
                    }
                    else for (int i = 0; i < std::min(connectingSize, 50); ++i) {
                            sprintf(strTmp, "(or (and (>= (select %s (+ %d %s)) %d) (<= (select %s (+ %d %s)) %d)) (> %d %s))",
                                    lhs_array.c_str(),
                                    i,
                                    pre_lhs.c_str(),
                                    charRange.first,

                                    lhs_array.c_str(),
                                    i,
                                    pre_lhs.c_str(),
                                    charRange.second,
                                    i + 1,
                                    generateFlatSize(elementNames[regexPos], rhs_str).c_str()
                            );
                            andConstraints.emplace_back(strTmp);
                        }
                }
                else {
                    unsigned int tmpNum = parse_regex_content(elementNames[regexPos].first).length();
                    if (!unrollMode){
                        for (int i = 0; i < pMax; ++i) {
                            sprintf(strTmp, "(or (= (select %s (+ %d %s)) (select %s %d)) (> %d %s))",
                                    lhs_array.c_str(),
                                    i,
                                    pre_lhs.c_str(),
                                    rhs_array.c_str(),
                                    i % tmpNum,
                                    i + 1,
                                    generateFlatSize(elementNames[regexPos], rhs_str).c_str());
                            andConstraints.emplace_back(strTmp);
                        }
                    }
                    else for (int i = 0; i < std::min(connectingSize, 50); ++i) {
                            sprintf(strTmp, "(or (= (select %s (+ %d %s)) (select %s %d)) (> %d %s))",
                                    lhs_array.c_str(),
                                    i,
                                    pre_lhs.c_str(),
                                    rhs_array.c_str(),
                                    i % tmpNum,
                                    i + 1,
                                    generateFlatSize(elementNames[regexPos], rhs_str).c_str());
                            andConstraints.emplace_back(strTmp);
                        }
                }

                return andConstraint(andConstraints);
#endif
            }

            /*
             * Generate constraints for the case
             * X = T . "abc" . Y . Z
             * constPos: position of const element
             * return: (or (and length header = i && X_i = a && X_[i+1] = b && X_[i+2] = c))
             */
            std::string handle_Const_WithPosition_array(
                    std::pair<std::string, int> a,
                    std::vector<std::pair<std::string, int>> elementNames,
                    std::string lhs_str, std::string rhs_str,
                    int constPos,
                    std::string value, /* value of regex */
                    int start, int finish,
                    bool optimizing,
                    int pMax = PMAX,
                    std::string extraConstraint = "" /* length = ? */) {

                SASSERT (elementNames[constPos].second < 0);
                bool unrollMode = pMax == PMAX;
                std::vector<std::string> locationConstraint;
                if (extraConstraint.length() > 0)
                    locationConstraint.emplace_back(extraConstraint);

                /* find the start position --> */
                std::string startPos = leng_prefix_lhs(a, elementNames, lhs_str, rhs_str, constPos, optimizing, unrollMode);

                /* optimize length of generated string */
                std::string tmp01 = generateFlatArray(a, lhs_str);
                std::string tmp02 = generateFlatArray(elementNames[constPos], rhs_str);

                std::vector<std::string> components = {value};
                if (isUnionStr(value))
                    components = collectAlternativeComponents(value);

                std::vector<std::string> orConstraints;
                for (const auto& v : components)
                    if ((int)v.length() == finish - start){
                        if (startPos.size() == 1 && startPos[0] == '0') {
                            if (components.size() != 1)
                                for (int i = start; i < finish; ++i) {
                                    unrollMode ?
                                    locationConstraint.emplace_back(createEqualConstraint(
                                            createSelectConstraint(tmp01, std::to_string((i - start))),
                                            createSelectConstraint(tmp02, std::to_string(i))))
                                               :
                                    locationConstraint.emplace_back(createEqualConstraint(
                                            createSelectConstraint(tmp01, std::to_string((i - start) % pMax)),
                                            createSelectConstraint(tmp02, std::to_string(i))));
                                }
                            else
                                for (int i = start; i < finish; ++i) {
                                    unrollMode ?
                                    locationConstraint.emplace_back(createEqualConstraint(
                                            createSelectConstraint(tmp01, std::to_string(i - start)),
                                            std::to_string(v[i])))
                                               :
                                    locationConstraint.emplace_back(createEqualConstraint(
                                            createSelectConstraint(tmp01, std::to_string((i - start) % pMax)),
                                            std::to_string(v[i])));
                                }
                        }

                        else {
                            if (components.size() != 1)
                                for (int i = start; i < finish; ++i) {
                                    unrollMode ?
                                    locationConstraint.emplace_back(createEqualConstraint(
                                            createSelectConstraint(tmp01,
                                                                   createPlusOperator(std::to_string(i - start), startPos)),
                                            createSelectConstraint(tmp02, std::to_string(i))))
                                               :
                                    locationConstraint.emplace_back(createEqualConstraint(
                                            createSelectConstraint(tmp01,
                                                                   createModOperator(
                                                                           createPlusOperator(std::to_string(i - start), startPos),
                                                                           std::to_string(pMax))),
                                            createSelectConstraint(tmp02, std::to_string(i))));
                                }
                            else
                                for (int i = start; i < finish; ++i) {
                                    unrollMode ?
                                    locationConstraint.emplace_back(createEqualConstraint(
                                            createSelectConstraint(tmp01,
                                                                   createPlusOperator(std::to_string(i - start), startPos)),
                                            std::to_string(v[i]))) :
                                    locationConstraint.emplace_back(createEqualConstraint(
                                            createSelectConstraint(tmp01,
                                                                   createModOperator(
                                                                           createPlusOperator(std::to_string(i - start), startPos),
                                                                           std::to_string(pMax))),
                                            std::to_string(v[i])));
                                }
                        }
                        orConstraints.emplace_back(andConstraint(locationConstraint));
                    }

                return orConstraint(orConstraints);
            }

            /*
             * connected = a + connected + b
             */
            std::string handle_connected_connected_array(
                    std::pair<std::string, int> a,
                    std::vector<std::pair<std::string, int>> elementNames,
                    std::string lhs_str, std::string rhs_str,
                    int pos,
                    int bound,
                    bool optimizing,
                    int pMax = PMAX){
                bool unrollMode = pMax == PMAX;
                /* find the start position --> */
                std::string startLhs = leng_prefix_lhs(a, elementNames, lhs_str, rhs_str, pos, optimizing, unrollMode);
                std::string startRhs = leng_prefix_rhs(elementNames[pos], rhs_str, unrollMode);

                /* optimize length of generated string */
                std::string arrLhs = generateFlatArray(a, lhs_str);
                std::string arrRhs = generateFlatArray(elementNames[pos], rhs_str);

                std::string lenA = generateFlatSize(a, lhs_str);
                std::string lenB = generateFlatSize(elementNames[pos], rhs_str);

                std::string iterB = generateFlatIter(elementNames[pos]);

                std::vector<std::string> andConstraints;
                std::string lenRhs = "";
                /* combine two parts if it is possible */
                if (elementNames[pos].second % QMAX == 0 &&
                    pos < (int)elementNames.size() - 1 &&
                    QMAX > 1 && elementNames[pos].second >= 0) {
                    assert(elementNames[pos + 1].second % QMAX == 1);
                    assert(QMAX == 2);
                    lenRhs = generateFlatSize(elementNames[pos], rhs_str);
                    if (elementNames[pos + 1].second < 10)
                        lenRhs = lenRhs.substr(0, lenRhs.length() - 2);
                    else if (elementNames[pos + 1].second < 100)
                        lenRhs = lenRhs.substr(0, lenRhs.length() - 3);
                    else if (elementNames[pos + 1].second < 1000)
                        lenRhs = lenRhs.substr(0, lenRhs.length() - 4);
                    else if (elementNames[pos + 1].second < 10000)
                        lenRhs = lenRhs.substr(0, lenRhs.length() - 5);
                }
                else
                    lenRhs = generateFlatSize(elementNames[pos], rhs_str);

                if (!unrollMode){
                    for (int i = 1; i <= pMax; ++i){
                        std::vector<std::string> orConstraints;
                        orConstraints.emplace_back(
                                createEqualConstraint(
                                        createSelectConstraint(arrLhs,
                                                               createModOperator(
                                                                       createPlusOperator(std::to_string(i - 1), startLhs),
                                                                       std::to_string(pMax))),

                                        createSelectConstraint(arrRhs,
                                                               createModOperator(
                                                                       createPlusOperator(std::to_string(i - 1), startRhs),
                                                                       std::to_string(pMax)))));

                        orConstraints.emplace_back(createLessConstraint(lenRhs, std::to_string(i)));
                        andConstraints.emplace_back(orConstraint(orConstraints));
                    }

                    andConstraints.emplace_back(
                            createImpliesOperator(
                                    createLessConstraint(lenB, lenA),
                                    createEqualConstraint(iterB, "1")));
                }
                else {
                    int consideredSize = bound + 1;

                    if (startLhs.compare(ZERO) != 0 && startRhs.compare(ZERO) != 0) {
                        for (int i = 1; i <= consideredSize; ++i){
                            std::vector<std::string> orConstraints;
                            orConstraints.emplace_back(createEqualConstraint(
                                    createSelectConstraint(arrLhs, createPlusOperator(std::to_string(i - 1), startLhs)),
                                    createSelectConstraint(arrRhs, createPlusOperator(std::to_string(i - 1), startRhs))));
                            orConstraints.emplace_back(createLessConstraint(lenRhs, std::to_string(i)));
                            andConstraints.emplace_back(orConstraint(orConstraints));
                        }
                    }
                    else if (startLhs.compare(ZERO) == 0 && startRhs.compare(ZERO) == 0){

                        for (int i = 1; i <= consideredSize; ++i){
                            std::vector<std::string> orConstraints;
                            orConstraints.emplace_back(createEqualConstraint(
                                    createSelectConstraint(arrLhs, std::to_string(i - 1)),
                                    createSelectConstraint(arrRhs, std::to_string(i - 1))));
                            orConstraints.emplace_back(createLessConstraint(lenRhs, std::to_string(i)));
                            andConstraints.emplace_back(orConstraint(orConstraints));
                        }
                    }
                    else if (startLhs.compare(ZERO) == 0){
                        for (int i = 1; i <= consideredSize; ++i){
                            std::vector<std::string> orConstraints;
                            orConstraints.emplace_back(createEqualConstraint(
                                    createSelectConstraint(arrLhs, std::to_string(i - 1)),
                                    createSelectConstraint(arrRhs, createPlusOperator(std::to_string(i - 1), startRhs))));
                            orConstraints.emplace_back(createLessConstraint(lenRhs, std::to_string(i)));
                            andConstraints.emplace_back(orConstraint(orConstraints));
                        }
                    }
                    else if (startRhs.compare(ZERO) == 0){
                        for (int i = 1; i <= consideredSize; ++i){
                            std::vector<std::string> orConstraints;
                            orConstraints.emplace_back(createEqualConstraint(
                                    createSelectConstraint(arrLhs, createPlusOperator(std::to_string(i - 1), startLhs)),
                                    createSelectConstraint(arrRhs, std::to_string(i - 1))));
                            orConstraints.emplace_back(createLessConstraint(lenRhs, std::to_string(i)));
                            andConstraints.emplace_back(orConstraint(orConstraints));
                        }
                    }
                    andConstraints.emplace_back(createLessEqualConstraint(lenRhs, std::to_string(connectingSize)));
                }
                std::string result = andConstraint(andConstraints) + "\n";
                return result;
            }

            /*
             * Generate constraints for the case
             * X = T . "abc" . Y . Z
             * constPos: position of const element
             * return: (or (and length header = i && X_i = a && X_[i+1] = b && X_[i+2] = c))
             */
            std::string handle_SubConst_WithPosition_array(
                    std::pair<std::string, int> a, // connected var
                    std::vector<std::pair<std::string, int>> elementNames,
                    std::string lhs_str, std::string rhs_str,
                    int constPos,
                    bool optimizing,
                    int pMax = PMAX) {
                SASSERT (elementNames[constPos].second < 0);
                bool unrollMode = pMax == PMAX;

                /* regex */
                std::string content = "";
                if (elementNames[constPos].second != REGEX_CODE)
                    content = elementNames[constPos].first;
                else
                    content = parse_regex_content(elementNames[constPos].first);

                std::string startPos = leng_prefix_lhs(a, elementNames, lhs_str, rhs_str, constPos, optimizing, unrollMode);
                std::string flatArrayName = generateFlatArray(a, lhs_str);

                std::vector<std::string> possibleCases;
                if (elementNames[constPos].second == REGEX_CODE) {
                    possibleCases.emplace_back(
                            handle_Regex_WithPosition_array(
                                    a, elementNames,
                                    lhs_str, rhs_str,
                                    constPos,
                                    optimizing,
                                    pMax));
                }
                else {
                    std::vector<std::string> components = {content};
                    if (isUnionStr(content))
                        components = collectAlternativeComponents(content);
                    std::string flatArrayRhs = generateFlatArray(elementNames[constPos], rhs_str);

                    for (const auto& v : components) {
                        if (elementNames[constPos].second % QCONSTMAX == -1) {
                            /* head of const */
                            std::vector<std::string> oneCase;
                            if (components.size() != 1)
                                for (int i = 1; i <= std::min(LOCALSPLITMAX, (int)v.length()); ++i) {
                                    std::vector<std::string> locationConstraint;
                                    /*length = i*/
                                    locationConstraint.emplace_back(
                                            createLessConstraint(
                                                    generateFlatSize(elementNames[constPos], rhs_str),
                                                    std::to_string(i)));
                                    unrollMode ?
                                    locationConstraint.emplace_back(
                                            createEqualConstraint(
                                                    createSelectConstraint(flatArrayName, createPlusOperator(std::to_string(i - 1), startPos)),
                                                    createSelectConstraint(flatArrayRhs, std::to_string(i - 1)))) /* arr value */
                                               :
                                    locationConstraint.emplace_back(
                                            createEqualConstraint(
                                                    createSelectConstraint(flatArrayName,
                                                                           createModOperator(
                                                                                   createPlusOperator(std::to_string(i - 1), startPos),
                                                                                   std::to_string(pMax))),
                                                    createSelectConstraint(flatArrayRhs, std::to_string(i - 1))));
                                    oneCase.emplace_back(orConstraint(locationConstraint));
                                }
                            else
                                for (int i = 1; i <= std::min(LOCALSPLITMAX, (int)v.length()); ++i) {
                                    std::vector<std::string> locationConstraint;
                                    /*length = i*/
                                    locationConstraint.emplace_back(
                                            createLessConstraint(generateFlatSize(elementNames[constPos], rhs_str),
                                                                 std::to_string(i)));
                                    unrollMode ?
                                    locationConstraint.emplace_back(
                                            createEqualConstraint(
                                                    createSelectConstraint(flatArrayName, createPlusOperator(std::to_string(i - 1), startPos)),
                                                    std::to_string(v[i - 1]))) /* direct value */
                                               :
                                    locationConstraint.emplace_back(
                                            createEqualConstraint(
                                                    createSelectConstraint(flatArrayName,
                                                                           createModOperator(
                                                                                   createPlusOperator(std::to_string(i - 1), startPos),
                                                                                   std::to_string(pMax))),
                                                    std::to_string(v[i - 1]))) /* direct value */;

                                    oneCase.emplace_back(orConstraint(locationConstraint));
                                }
                            possibleCases.emplace_back(andConstraint(oneCase));
                        }
                        else {
                            for (int i = 0; i <= std::min(LOCALSPLITMAX, (int)v.length()); ++i) {
                                /*length = i*/
                                std::string tmp = createEqualConstraint(generateFlatSize(elementNames[constPos], rhs_str),
                                                                        std::to_string(v.length() - i));
                                possibleCases.emplace_back(
                                        handle_Const_WithPosition_array(
                                                a, elementNames,
                                                lhs_str, rhs_str,
                                                constPos, v, i, v.length(),
                                                optimizing,
                                                pMax,
                                                tmp));
                            }
                        }
                    }
                }

                std::string result = orConstraint(possibleCases);
                return result;
            }

            /*
             *
             */
            std::string unrollConnectedVariable(
                    std::pair<std::string, int> a, /* connected variable */
                    std::vector<std::pair<std::string, int> > elementNames, /* contain const */
                    std::string lhs_str, std::string rhs_str,
                    std::map<std::string, int> connectedVariables,
                    bool optimizing,
                    int pMax = PMAX){
                STRACE("str", tout << __LINE__ <<  " ***" << __FUNCTION__ << "***" << std::endl;);
                /* (and ...) */
                std::vector<std::string> possibleCases;

                for (unsigned i = 0 ; i < elementNames.size(); ++i){
                    if (elementNames[i].second < 0){ /* const || regex */
                        /* |lhs| = 1 vs |rhs| = 1*/
                        if (elementNames.size() == 1 && QCONSTMAX > 1) {
//					__debugPrint(logFile, "%d case 1\n", __LINE__);
                            possibleCases.emplace_back(
                                    handle_SubConst_WithPosition_array(
                                            a, elementNames,
                                            lhs_str, rhs_str, i,
                                            optimizing,
                                            pMax));
                        }
                        else if (elementNames[i].second == REGEX_CODE) {
//					__debugPrint(logFile, "%d case 2\n", __LINE__);
                            possibleCases.emplace_back(handle_SubConst_WithPosition_array(
                                    a, elementNames,
                                    lhs_str, rhs_str, i,
                                    optimizing,
                                    pMax));
                        }
                            /* tail of string, head of elements*/
                        else if (i == 0 && elementNames[i].second % QCONSTMAX == 0 && QCONSTMAX > 1) {
//					__debugPrint(logFile, "%d case 3\n", __LINE__);
                            possibleCases.emplace_back(handle_SubConst_WithPosition_array(
                                    a, elementNames,
                                    lhs_str, rhs_str, i,
                                    optimizing,
                                    pMax));
                        }
                            /* head of string, tail of elements */
                        else if (i == elementNames.size() - 1 && elementNames[i].second % QCONSTMAX == -1 && QCONSTMAX > 1)  {
//					__debugPrint(logFile, "%d case 4\n", __LINE__);
                            possibleCases.emplace_back(handle_SubConst_WithPosition_array(
                                    a, elementNames,
                                    lhs_str, rhs_str, i,
                                    optimizing,
                                    pMax));
                        }
                            /* only care about first element */
                        else if (elementNames[i].second % QCONSTMAX == -1)  {
//					__debugPrint(logFile, "%d case 5\n", __LINE__);
                            possibleCases.emplace_back(
                                    handle_Const_WithPosition_array(
                                            a, elementNames,
                                            lhs_str, rhs_str, i, elementNames[i].first, 0,
                                            elementNames[i].first.length(),
                                            optimizing,
                                            pMax));
                        }
                    }
                    else if (elementNames[i].second >= 0 &&
                             connectedVariables.find(elementNames[i].first) != connectedVariables.end()){
                        STRACE("str", tout << __LINE__ <<  " case 6" << std::endl;);
                        if (elementNames[i].second % QMAX == 1 && i > 0)
                            continue;

                        possibleCases.emplace_back(
                                handle_connected_connected_array(
                                        a, elementNames, lhs_str, rhs_str, i,
                                        connectedVariables[elementNames[i].first],
                                        optimizing,
                                        pMax));

                    }
                }
                return andConstraint(possibleCases);
            }

            /*
             *
             * Flat = empty
             */

            std::string generateConstraint00(
                    std::pair<std::string, int> a,
                    std::string l_r_hs){

                return createEqualConstraint(ZERO, generateFlatSize(a, l_r_hs));
            }

            /*
             * Flat = Flat
             * size = size && it = it  ||
             * size = size && it = 1
             */
            std::string generateConstraint01(
                    std::string lhs_str, std::string rhs_str,
                    std::pair<std::string, int> a, std::pair<std::string, int> b,
                    int pMax,
                    std::map<std::string, int> connectedVariables,
                    bool optimizing){
                bool isConstA = a.second < 0;
                bool isConstB = b.second < 0;

                std::string nameA = "";
                std::string nameB = "";
                if (optimizing){
                    nameA = generateVarSize(a, lhs_str);
                    nameB = generateVarSize(b, rhs_str);
                }
                else {
                    nameA = generateFlatSize(a, lhs_str);
                    nameB = generateFlatSize(b, rhs_str);
                }

                /* do not need AND */
                std::string result = createEqualConstraint(nameA, nameB);
                result += createEqualConstraint(generateFlatIter(a), generateFlatIter(b));

                if (!isConstA && !isConstB) {
                    /* size = size && it = it */

                    if (connectedVariables.find(b.first) != connectedVariables.end() &&
                        connectedVariables.find(a.first) != connectedVariables.end()){

                        if (!optimizing) {
                            STRACE("str", tout << __LINE__ <<  " generateConstraint01: connectedVar " <<  a.first << " == connectedVar " << b.first << std::endl;);
                            result = result + " " + unrollConnectedVariable(b, {a}, rhs_str, lhs_str, connectedVariables, optimizing, pMax);
                        }
                        else {
                            std::string tmp = "";
                            std::string arrA = generateFlatArray(a, "");
                            std::string arrB = generateFlatArray(b, "");
                            for (int i = 0; i < std::max(connectedVariables[b.first], connectedVariables[a.first]); ++i) {
                                tmp = tmp + "(or " + createEqualConstraint(createSelectConstraint(arrA, std::to_string(i)), createSelectConstraint(arrB, std::to_string(i)))
                                      + createLessConstraint(nameA, std::to_string(i + 1)) + ")";
                            }
                            result = result + "(and " + tmp + ")";
                        }
                    }
                }
                else if (isConstA && isConstB) {
                    if ((QCONSTMAX == 1 || optimizing) && a.first.compare(b.first) != 0) /* const = const */
                        return "";
                    std::vector<std::string> possibleCases;

                    if (a.second == REGEX_CODE && b.second % QMAX == -1){
                        std::string regexContent = parse_regex_full_content(a.first);
                        RegEx re;
                        re.Compile(regexContent);
                        unsigned length = 0;
                        if (regexContent[regexContent.length() - 1] == '+')
                            length = 1;
                        while (length <= b.first.length()) {
                            std::string regexValue = b.first.substr(0, length);
                            if (re.MatchAll(regexValue) == true) {
                                possibleCases.emplace_back(createEqualConstraint(nameA, std::to_string(length)));
                            }
                            else
                                break;
                            length++;
                            STRACE("str", tout << __LINE__ <<  " accept: " <<  regexValue << std::endl;);
                        }
                    }
                    else if (a.second == REGEX_CODE && b.second % QMAX == 0){
                        std::string regexContent = parse_regex_full_content(a.first);
                        RegEx re;
                        re.Compile(regexContent);
                        unsigned length = 0;
                        if (regexContent[regexContent.length() - 1] == '+')
                            length = 1;
                        while (length <= b.first.length()) {
                            std::string regexValue = b.first.substr(b.first.length() - length, length);
                            if (re.MatchAll(regexValue) == true) {
                                possibleCases.emplace_back(createEqualConstraint(nameA, std::to_string(length)));
                            }
                            else
                                break;
                            length++;
                            STRACE("str", tout << __LINE__ <<  " accept: " <<  regexValue << std::endl;);
                        }
                    }
                    else if (b.second == REGEX_CODE && a.second % QMAX == -1){
                        std::string regexContent = parse_regex_full_content(b.first);
                        RegEx re;
                        re.Compile(regexContent);
                        unsigned length = 0;
                        if (regexContent[regexContent.length() - 1] == '+')
                            length = 1;
                        while (length <= a.first.length()) {
                            std::string regexValue = a.first.substr(0, length);
                            if (re.MatchAll(regexValue) == true) {
                                possibleCases.emplace_back(createEqualConstraint(nameA, std::to_string(length)));
                            }
                            else
                                break;
                            length++;

                            STRACE("str", tout << __LINE__ <<  " accept: " <<  regexValue << std::endl;);
                        }
                    }
                    else if (b.second == REGEX_CODE && a.second % QMAX == 0){
                        std::string regexContent = parse_regex_full_content(b.first);
                        RegEx re;
                        re.Compile(regexContent);
                        unsigned length = 0;
                        if (regexContent[regexContent.length() - 1] == '+')
                            length = 1;
                        while (length <= a.first.length()) {
                            std::string regexValue = a.first.substr(a.first.length() - length, length);
                            if (re.MatchAll(regexValue) == true) {
                                possibleCases.emplace_back(createEqualConstraint(nameA, std::to_string(length)));
                            }
                            else
                                break;
                            length++;
                            STRACE("str", tout << __LINE__ <<  " accept: " <<  regexValue << std::endl;);
                        }
                    }
                    else if (a.second == REGEX_CODE && b.second == REGEX_CODE) {
                        STRACE("str", tout << __LINE__ <<  " might get error here " <<  std::endl;);
                        std::string content01 = parse_regex_content(b.first);
                        std::string content02 = parse_regex_content(a.first);
                        unsigned int lcdLength = lcd(content01.length(), content02.length());

                        std::string data01 = "";
                        std::string data02 = "";
                        while (data01.length() != lcdLength)
                            data01 = data01 + content01;
                        while (data02.length() != lcdLength)
                            data02 = data02 + content02;
                        if (data01.compare(data02) == 0) {
                            possibleCases.emplace_back(createEqualConstraint(ZERO, createModOperator(nameA, std::to_string(lcdLength))));
                        }
                        else {
                            possibleCases.emplace_back(createEqualConstraint(nameA, ZERO));
                        }
                    }
                    else if (!optimizing) {
                        if (a.second % QMAX == -1 && b.second % QMAX  == -1) /* head vs head */ {
                            for (int i = std::min(a.first.length(), b.first.length()); i >= 0; --i) {
                                if (a.first.substr(0, i).compare(b.first.substr(0, i)) == 0) {
                                    /* size can be from 0..i */
                                    result += createLessEqualConstraint(nameA, std::to_string(i));
                                    return result;
                                }
                            }
                        }
                        else if (a.second  % QMAX == -1 && b.second % QMAX == 0) /* head vs tail */ {
                            for (int i = std::min(a.first.length(), b.first.length()); i >= 0; --i) {
                                if (a.first.substr(0, i).compare(b.first.substr(b.first.length() - i)) == 0) {
                                    /* size can be i */
                                    possibleCases.emplace_back(createEqualConstraint(nameA, std::to_string(i)));
                                }
                            }
                        }
                        else if (a.second % QMAX == 0 && b.second % QMAX == -1) /* tail vs head */ {
                            for (int i = std::min(a.first.length(), b.first.length()); i >= 0; --i) {
                                if (b.first.substr(0, i).compare(a.first.substr(a.first.length() - i)) == 0) {
                                    /* size can be i */
                                    possibleCases.emplace_back(createEqualConstraint(nameA, std::to_string(i)));
                                }
                            }
                        }
                        else if (a.second % QMAX == 0 && b.second % QMAX == 0) /* tail vs tail */ {
                            for (int i = std::min(a.first.length(), b.first.length()); i >= 0; --i) {
                                if (a.first.substr(a.first.length() - i, i).compare(b.first.substr(b.first.length() - i, i)) == 0) {
                                    /* size can be i */
                                    result += createLessEqualConstraint(nameA, std::to_string(i));
                                    return result;
                                }
                            }
                        }
                    }
                    else {
                        SASSERT (optimizing);
                    }

                    /* create or constraint */
                    std::string tmp = orConstraint(possibleCases);
                    if (tmp.length() == 0)
                        return tmp;
                    else
                        result = result + " " + tmp;

                    return result;
                }

                else if (isConstA) {
                    /* size = size && it = 1*/
                    SASSERT(a.second != REGEX_CODE);
                    /* record characters for some special variables */
                    if (connectedVariables.find(b.first) != connectedVariables.end()){
                        std::vector<std::pair<std::string, int>> elements;
                        if (optimizing) {
                            elements.emplace_back(std::make_pair(a.first, -1));
                            elements.emplace_back(std::make_pair(a.first, -2));
                        }
                        else
                            elements.emplace_back(a);
                        result = result + " " + unrollConnectedVariable(b, elements, rhs_str, lhs_str, connectedVariables, optimizing);
                    }
                }

                else { /* isConstB */
                    /* size = size && it = 1*/
                    /* record characters for some special variables */
                    SASSERT(a.second != REGEX_CODE);
                    if (connectedVariables.find(a.first) != connectedVariables.end()){
                        std::vector<std::pair<std::string, int>> elements;
                        if (optimizing) {
                            elements.emplace_back(std::make_pair(b.first, -1));
                            elements.emplace_back(std::make_pair(b.first, -2));
                        }
                        else
                            elements.emplace_back(b);
                        result = result + " " + unrollConnectedVariable(a, elements, lhs_str, rhs_str, connectedVariables, optimizing);
                    }
                }

                return result;
            }

            /*
             *
             */
            std::string generateCase02Constraint02(
                    std::pair<std::string, int> a,
                    std::vector<std::pair<std::string, int>> elementNames,
                    std::string lhs_str, std::string rhs_str){
                return "";
            }

            /*
             * Flat = sum (flats)
             */
            std::string generateConstraint02(
                    std::pair<std::string, int> a,
                    std::vector<std::pair<std::string, int>> elementNames,
                    std::string lhs_str, std::string rhs_str,
                    int pMax,
                    std::map<std::string, int> connectedVariables,
                    bool optimizing){
//		__debugPrint(logFile, "%d %s: optimizing: %s\n", __LINE__, __FUNCTION__, optimizing? "true" : "false");
                std::string result = "";

                if (a.second < 0) { /* const string or regex */
                    /* check feasibility */

                    if (a.second != REGEX_CODE) {
                        int max_lhs = a.first.length();
                        int min_rhs = 0;
                        for (unsigned i = 0; i < elementNames.size(); ++i) {
                            if (elementNames[i].second % QCONSTMAX == -1) {
                                if (QCONSTMAX == 2 && i + 1 < elementNames.size() && elementNames[i + 1].second % QCONSTMAX == 0)
                                    min_rhs += elementNames[i].first.length();
                                else if (QCONSTMAX == 1)
                                    min_rhs += elementNames[i].first.length();
                            }
                            else if (elementNames[i].second == REGEX_CODE &&
                                     elementNames[i].first.find('+') != std::string::npos &&
                                     elementNames[i].first.find('|') == std::string::npos){
                                /* regex plus */
                                size_t endPos = elementNames[i].first.find(')');
                                SASSERT(endPos != std::string::npos);
                                min_rhs += endPos - 1;
                            }
                        }
                        if (max_lhs < min_rhs) {
                            return "";
                        }
                    }
                    else {
                        /* regex */
                        // TODO: to be completed
                    }

                    /* collect */
                    /* only handle the case of splitting const string into two parts*/
                    std::vector<std::string> addElements;
                    for (unsigned i = 0 ; i < elementNames.size(); ++i){
                        addElements.emplace_back(createMultiplyOperator(generateFlatSize(elementNames[i], rhs_str),
                                                                        generateFlatIter(elementNames[i])));
                    }

                    std::string len_lhs = "";
                    if (optimizing != NONE)
                        len_lhs = generateVarSize(a);
                    else
                        len_lhs = generateFlatSize(a, lhs_str);
                    result += createEqualConstraint(len_lhs, addConstraint_full(addElements));

                    int splitType = findSplitType(elementNames, connectedVariables);
                    STRACE("str", tout << __LINE__ <<  " const = sum(flats), splitType = " << splitType << std::endl;);

                    /*
                     * 0: No const, No connected var
                     * 1: const		No connected var
                     * 2: no const, connected var
                     * 3: have both
                     */
                    std::vector<std::vector<int>> allPossibleSplits;
                    std::set<std::string> strSplits;
                    switch (splitType) {
                        case SIMPLE_CASE:
                            break;
                        case CONNECTED_ONLY:
                            /* handle connected var */
                            result = result + " " + toConstraint_ConnectedVar(
                                    a, elementNames,
                                    lhs_str, rhs_str,
                                    connectedVariables,
                                    optimizing != NONE,
                                    pMax);
                            break;
                        case CONST_ONLY:
                            /* handle const */
                            allPossibleSplits = collectAllPossibleSplits(a, elementNames, optimizing != NONE);
                            for (unsigned i = 0; i < allPossibleSplits.size(); ++i) {
                                strSplits.emplace(toConstraint_NoConnectedVar(a, elementNames, allPossibleSplits[i], lhs_str, rhs_str, optimizing != NONE));
                            }

                            if (strSplits.size() > 0)
                                result = result + " " + orConstraint(strSplits);
                            else
                                result = "";
                            break;

                        case 3:
                            /* handle connected var */
                            /* handle const */
                            allPossibleSplits = collectAllPossibleSplits(a, elementNames, optimizing != NONE);
                            for (unsigned i = 0; i < allPossibleSplits.size(); ++i) {
                                /* check feasibility */
                                strSplits.emplace(
                                        toConstraint_havingConnectedVar_andConst(
                                                a,
                                                elementNames,
                                                allPossibleSplits[i], lhs_str, rhs_str,
                                                connectedVariables,
                                                optimizing != NONE,
                                                pMax));
                            }
                            if (strSplits.size() > 0)
                                result = result + " " + orConstraint(strSplits);
                            else
                                return "";
                            break;
                        default:
                        SASSERT (false);
                            break;
                    }
                }

                else {
                    /* do not need AND */
                    /* result = sum (length) */
                    if (optimizing)
                        result = result + "(= " + generateVarSize(a, lhs_str) + " (+ ";
                    else
                        result = result + "(= " + generateFlatSize(a, lhs_str) + " (+ ";
                    for (unsigned i = 0; i < elementNames.size(); ++i) {
                        result = result + createMultiplyOperator(generateFlatSize(elementNames[i], rhs_str),
                                                                 generateFlatIter(elementNames[i])) + " ";
                    }

                    if (elementNames.size() == 1)
                        result = result + " 0";

                    result = result + ")) ";

                    /* DO NOT care about empty flats or not*/

                    /* handle const for connected variables*/
                    if (connectedVariables.find(a.first) != connectedVariables.end())
                        result = result + unrollConnectedVariable(
                                a, elementNames,
                                lhs_str, rhs_str,
                                connectedVariables, optimizing);

                    /* case 2 */
                    std::string constraints01 = "(= " + generateFlatIter(a) + " (+ ";
                    std::string constraints02 = "";
                    for (const auto& s : elementNames){
                        constraints02 = constraints02 + createEqualConstraint(generateFlatSize(a, lhs_str), generateFlatSize(s, rhs_str)) + " "; /* size = size */
                        constraints01 = constraints01 + generateFlatIter(s) + " "; /* iter = sum iter*/
                    }
                    constraints01 = constraints01 + ")) ";
                    constraints01 = "(and " + constraints01 + " " + constraints02 + ")";

                    result = "(or (and " + result + + "))";
//			result = "(or (and " + result + + ") " + constraints01 + ")";
                }


                return result;
            }

            /*
             *
             */
            int canBeOptimized_LHS(
                    int i, int startPos, int j,
                    std::vector<std::pair<std::string, int>> lhs_elements,
                    std::vector<std::pair<std::string, int>> rhs_elements){
//		__debugPrint(logFile, "%d *** %s ***: %d: %d -> %d\n", __LINE__, __FUNCTION__, i, startPos, j);
                if (left_arr[i] == SUMFLAT && right_arr[j] == i){
                    /* check forward */
                    if (i < (int)left_arr.size() - 1 &&
                        lhs_elements[i + 1].first.compare(lhs_elements[i].first) == 0) {

                        if (left_arr[i + 1] == EMPTYFLAT){
                            return RIGHT_EMPTY;
                        }
                        else if (left_arr[i + 1] == SUMFLAT){
                            return RIGHT_SUM;
                        }
                        else if (j + 1 < (int)rhs_elements.size()){
                            if (left_arr[i + 1] == j + 1 &&
                                right_arr[j + 1] == i + 1){
                                return RIGHT_EQUAL;
                            }
                        }
                    }
                    /* check backward */
                    if (i > 0 &&
                        lhs_elements[i - 1].first.compare(lhs_elements[i].first) == 0) {
                        if (left_arr[i - 1] == EMPTYFLAT){
                            return LEFT_EMPTY;
                        }
                        else if (left_arr[i - 1] == SUMFLAT)
                            return LEFT_SUM;
                        else if (startPos > 0){
//					__debugPrint(logFile, "%d %d vs %d\n", __LINE__, left_arr[i - 1], right_arr[j - 1]);
                            if (left_arr[i - 1] == startPos - 1 &&
                                right_arr[startPos - 1] == i - 1 &&
                                lhs_elements[i - 1].first.compare(lhs_elements[i].first) == 0){
                                return LEFT_EQUAL;
                            }
                        }
                    }
                }
                else if (left_arr[i] == j && right_arr[j] == i){
                    /* check forward */
                    if (i < (int)left_arr.size() - 1 &&
                        left_arr[i + 1] != SUMFLAT &&
                        lhs_elements[i + 1].first.compare(lhs_elements[i].first) == 0) {
                        if (left_arr[i + 1] == EMPTYFLAT){
                            return RIGHT_EMPTY;
                        }
                        else if (j + 1 < (int)rhs_elements.size()){
                            if (left_arr[i + 1] == j + 1 &&
                                right_arr[j + 1] == i + 1 &&
                                rhs_elements[j + 1].first.compare(rhs_elements[j].first) == 0){
                                return RIGHT_EQUAL;
                            }
                        }
                    }
                    /* check backward */
                    if (i > 0 &&
                        left_arr[i - 1] != SUMFLAT &&
                        lhs_elements[i - 1].first.compare(lhs_elements[i].first) == 0) {
                        if (left_arr[i - 1] == EMPTYFLAT){
                            return LEFT_EMPTY;
                        }
                        else if (startPos > 0){
                            if (left_arr[i - 1] == startPos - 1 &&
                                right_arr[startPos - 1] == i - 1 &&
                                rhs_elements[startPos - 1].first.compare(rhs_elements[startPos].first) == 0){
                                return LEFT_EQUAL;
                            }
                        }
                    }
                }
                return NONE;
            }

            /*
             *
             */
            int canBeOptimized_RHS(
                    int i, int startPos, int j,
                    std::vector<std::pair<std::string, int>> lhs_elements,
                    std::vector<std::pair<std::string, int>> rhs_elements){
                if (right_arr[j] == SUMFLAT && left_arr[i] == j){
                    /* check forward */
                    if (j < (int)right_arr.size() - 1 &&
                        rhs_elements[j + 1].first.compare(rhs_elements[j].first) == 0) {
                        if (right_arr[j + 1] == EMPTYFLAT){
                            return RIGHT_EMPTY;
                        }
                        else if (right_arr[j + 1] == SUMFLAT)
                            return RIGHT_SUM;
                        else if (i + 1 < (int)lhs_elements.size()){
                            if (left_arr[i + 1] == j + 1 &&
                                right_arr[j + 1] == i + 1){
                                return NONE;
                            }
                        }
                    }
                    /* check backward */
                    if (j > 0 &&
                        rhs_elements[j - 1].first.compare(rhs_elements[j].first) == 0) {
                        if (right_arr[j - 1] == EMPTYFLAT){
                            return LEFT_EMPTY;
                        }
                        else if (right_arr[j - 1] == SUMFLAT)
                            return LEFT_SUM;
                        else if (startPos > 0){
                            if (left_arr[startPos - 1] == j - 1 &&
                                right_arr[j - 1] == startPos - 1){
                                return NONE;
                            }
                        }
                    }
                }
                else if (left_arr[i] == j && right_arr[j] == i){
                    /* check forward */
                    if (i < (int)left_arr.size() - 1 &&
                        left_arr[i + 1] != SUMFLAT &&
                        lhs_elements[i + 1].first.compare(lhs_elements[i].first) == 0) {
                        if (left_arr[i + 1] == EMPTYFLAT){
                            return RIGHT_EMPTY;
                        }
                        else if (i + 1 < (int)lhs_elements.size()){
                            if (left_arr[i + 1] == j + 1 &&
                                right_arr[j + 1] == i + 1 &&
                                rhs_elements[j + 1].first.compare(rhs_elements[j].first) == 0){
                                return RIGHT_EQUAL;
                            }
                        }
                    }
                    /* check backward */
                    if (i > 0 &&
                        left_arr[i - 1] != SUMFLAT &&
                        lhs_elements[i - 1].first.compare(lhs_elements[i].first) == 0) {
                        if (left_arr[i - 1] == EMPTYFLAT){
                            return LEFT_EMPTY;
                        }
                        else if (startPos > 0){
                            if (left_arr[i - 1] == startPos - 1 &&
                                right_arr[startPos - 1] == i - 1 &&
                                rhs_elements[startPos - 1].first.compare(rhs_elements[startPos].first) == 0){
                                return LEFT_EQUAL;
                            }
                        }
                    }
                }
                return NONE;
            }

            /*
             * a_1 + a_2 + b_1 + b_2 = c_1 + c_2 + d_1 + d_2 ---> SMT
             */
            std::string generateSMT(int p,
                                    std::string lhs_str, std::string rhs_str,
                                    std::vector<std::pair<std::string, int>> lhs_elements,
                                    std::vector<std::pair<std::string, int>> rhs_elements,
                                    std::map<std::string, int> connectedVariables){
                std::vector<std::string> result_element;

                bool checkLeft[lhs_elements.size()];
                bool checkRight[rhs_elements.size()];
                memset(checkLeft, 0, sizeof checkLeft);
                memset(checkRight, 0, sizeof checkRight);

                /* do the left */
                for (unsigned i = 0; i < left_arr.size(); ++i)
                    if (!checkLeft[i]) {
                        if (left_arr[i] == SUMFLAT) { /* a = bx + cy */
//					__debugPrint(logFile, "%d %s.%d: %d\n", __LINE__, lhs_elements[i].first.c_str(), lhs_elements[i].second, left_arr[i]);
                            checkLeft[i] = true;

                            std::vector<std::pair<std::string, int>> elements;
                            unsigned j = 0;
                            int startPos = -1;
                            for (j = 0; j < right_arr.size(); ++j)
                                if (right_arr[j] == (int)i) {
                                    if (startPos == -1)
                                        startPos = (int)j;
                                    elements.emplace_back(rhs_elements[j]);
                                    checkRight[j] = true;
                                }
                                else if (startPos >= 0)
                                    break;
                            j--;
                            /* select optimization mode */
                            int optimizing = canBeOptimized_LHS(i, startPos, j, lhs_elements, rhs_elements);

//					__debugPrint(logFile, "%d optimizing mode: %d\n", __LINE__, optimizing);
                            switch (optimizing) {
                                case NONE:
                                    break;
                                case LEFT_EMPTY:
                                    checkLeft[i - 1] = true;
                                    break;
                                case LEFT_EQUAL:
                                    checkLeft[i - 1] = true;
                                    checkRight[startPos - 1] = true;
                                    elements.insert(elements.begin(), rhs_elements[startPos - 1]);
                                    break;
                                case LEFT_SUM:
                                SASSERT (false);
                                    break;
                                case RIGHT_EMPTY:
                                    checkLeft[i + 1] = true;
                                    break;
                                case RIGHT_EQUAL:
                                    checkLeft[i + 1] = true;
                                    checkRight[j + 1] = true;
                                    elements.emplace_back(rhs_elements[j + 1]);
                                    break;
                                case RIGHT_SUM:
                                    checkLeft[i + 1] = true;
                                    for (unsigned k = j + 1; k < right_arr.size(); ++k)
                                        if (right_arr[k] == (int)i + 1) {
                                            elements.emplace_back(rhs_elements[k]);
                                            checkRight[k] = true;
                                        }
                                        else
                                            break;
                                    break;
                                default:
                                SASSERT (false);
                                    break;
                            }

                            std::string tmp = generateConstraint02(
                                    lhs_elements[i],
                                    elements,
                                    lhs_str, rhs_str,
                                    p,
                                    connectedVariables,
                                    optimizing != NONE);

                            if (tmp.length() == 0) { /* cannot happen due to const */
                                STRACE("str", tout << __LINE__ <<  " 02 because of lhs@i: " << i << std::endl;);
                                return "";
                            }
                            result_element.emplace_back(tmp);

                        }
                        else if (left_arr[i] == EMPTYFLAT) {

                            /* empty */
                            /* some first flats can be empty */
                            if (lhs_elements[i].second % QCONSTMAX == -1) /* head of const */ {
                                if (lhs_elements[i].first.length() <= 0 ||
                                    (QCONSTMAX == 2 &&
                                     i + 1 < lhs_elements.size() &&
                                     left_arr[i + 1] == EMPTYFLAT &&
                                     lhs_elements[i].first.length() > 0) ||
                                    (QCONSTMAX == 1 &&
                                     lhs_elements[i].first.length() > 0)) /* const string is empty */ {
                                    return "";
                                }
                            }
                            checkLeft[i] = true;
                            std::string tmp = generateConstraint00(lhs_elements[i], lhs_str);

                            if (tmp.length() == 0) {/* cannot happen due to const */
                                return "";
                            }
                            result_element.emplace_back(tmp);
                        }
                    }

                /* do the right */
                for (unsigned i = 0; i < right_arr.size(); ++i)
                    if (!checkRight[i]){
                        if (right_arr[i] == SUMFLAT) { /* a = bx + cy */
                            checkRight[i] = true;

                            std::vector<std::pair<std::string, int>> elements;
                            unsigned j = 0;
                            int startPos = -1;
                            for (j = 0; j < left_arr.size(); ++j)
                                if (left_arr[j] == (int)i) {
                                    if (startPos == -1)
                                        startPos = (int)j;
                                    elements.emplace_back(lhs_elements[j]);
                                    checkLeft[j] = true;
                                }
                                else if (startPos >= 0)
                                    break;
                            j--;
                            /* select optimization mode */
                            int optimizing = canBeOptimized_RHS(j, startPos, i, lhs_elements, rhs_elements);
                            switch (optimizing) {
                                case NONE:
                                    break;
                                case LEFT_EMPTY:
                                    checkRight[i - 1] = true;
                                    break;
                                case LEFT_EQUAL:
                                    checkRight[i - 1] = true;
                                    checkLeft[startPos - 1] = true;
                                    elements.insert(elements.begin(), lhs_elements[startPos - 1]);
                                    break;
                                case LEFT_SUM:
                                SASSERT (false);
                                    break;
                                case RIGHT_EMPTY:
                                    checkRight[i + 1] = true;
                                    break;
                                case RIGHT_EQUAL:
                                    checkRight[i + 1] = true;
                                    checkLeft[j + 1] = true;
                                    elements.emplace_back(lhs_elements[j + 1]);
                                    break;
                                case RIGHT_SUM:
                                    checkRight[i + 1] = true;
                                    for (unsigned k = j + 1; k < left_arr.size(); ++k)
                                        if (left_arr[k] == (int)i + 1) {
                                            elements.emplace_back(lhs_elements[k]);
                                            checkLeft[k] = true;
                                        }
                                    break;
                                default:
                                SASSERT (false);
                                    break;
                            }
//					__debugPrint(logFile, "%d optimizing mode: %d\n", __LINE__, optimizing);
                            std::string tmp = generateConstraint02(
                                    rhs_elements[i],
                                    elements,
                                    rhs_str, lhs_str,
                                    p,
                                    connectedVariables, optimizing != NONE);
                            if (tmp.length() == 0) { /* cannot happen due to const */
                                STRACE("str", tout << __LINE__ <<  " 02 because of rhs@i: " << i << std::endl;);
                                return "";
                            }
                            result_element.emplace_back(tmp);
                        }
                        else if (right_arr[i] == EMPTYFLAT) {
                            /* empty */
                            /* some first flats can be empty */
                            if (rhs_elements[i].second % QCONSTMAX == -1) /* head of const */ {
                                if (rhs_elements[i].first.length() <= SPLIT_LOWER_BOUND - 2 ||
                                    (QCONSTMAX == 2 &&
                                     i + 1 < rhs_elements.size() &&
                                     right_arr[i + 1] == EMPTYFLAT &&
                                     rhs_elements[i].first.length() > 0) ||
                                    (QCONSTMAX == 1 &&
                                     rhs_elements[i].first.length() > 0))/*const string is empty*/
                                    return "";
                            }
                            checkRight[i] = true;
                            std::string tmp = generateConstraint00(rhs_elements[i], rhs_str);
                            if (tmp.length() == 0) {/* cannot happen due to const */
                                return "";
                            }
                            result_element.emplace_back(tmp);
                        }
                    }

                /* do the rest */
                /* do not need AND */
                std::string constraint01 = "";
                for (unsigned int i = 0 ; i < lhs_elements.size(); ++i)
                    if (checkLeft[i] == false) {
                        checkLeft[i] = true;
                        checkRight[left_arr[i]] = true;

                        unsigned j = 0;
                        for (j = 0; j < right_arr.size(); ++j)
                            if (right_arr[j] == (int)i) {
                                checkRight[j] = true;
                                break;
                            }

                        /* select optimization mode */
                        int optimizing = canBeOptimized_LHS(i, -1, j, lhs_elements, rhs_elements);
                        switch (optimizing) {
                            case NONE:
                                break;
                            case LEFT_EMPTY:
                            SASSERT (false);
                                break;
                            case LEFT_EQUAL:
                            SASSERT (false);
                                break;
                            case LEFT_SUM:
                            SASSERT (false);
                                break;
                            case RIGHT_EMPTY:
                            SASSERT (false);
                                break;
                            case RIGHT_EQUAL:
                                checkLeft[i + 1] = true;
                                checkRight[j + 1] = true;
                                break;
                            case RIGHT_SUM:
                            SASSERT (false);
                                break;
                            default:
                            SASSERT (false);
                                break;
                        }
//				__debugPrint(logFile, "%d optimizing mode: %d\n", __LINE__, optimizing);
                        std::string tmp = generateConstraint01(
                                lhs_str, rhs_str,
                                lhs_elements[i],
                                (std::pair<std::string, int>)rhs_elements[left_arr[i]],
                                p,
                                connectedVariables,
                                optimizing != NONE);
                        if (tmp.length() == 0) { /* cannot happen due to const */
                            return "";
                        }
                        constraint01 = constraint01 + tmp + " ";
                    }

                if (constraint01.length() > 5) {
                    result_element.emplace_back(constraint01);
                }

                for (unsigned i = 0 ; i < rhs_elements.size(); ++i)
                    if (checkRight[i] == false) {
                        STRACE("str", tout << __LINE__ <<  " error rhs@i: " << i << std::endl;);
                        SASSERT (false);
                    }

                /* sum up */
                std::string result = "(and \n";
                for (unsigned i = 0 ; i < result_element.size(); ++i)
                    result = result + result_element[i] + "\n";
                result = result + ")";

                return result;
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
                std::vector<std::pair<std::string, int>> lhs_elements,
                std::vector<std::pair<std::string, int>> rhs_elements);

            /*
             * a_1 + a_2 + b_1 + b_2 = c_1 + c_2 + d_1 + d_2 ---> SMT
             */
            std::string generateSMT(int p,
                                            std::vector<int> left_arr,
                                            std::vector<int> right_arr,
                                            std::string lhs_str, std::string rhs_str,
                                            std::vector<std::pair<expr*, int>> lhs_elements,
                                            std::vector<std::pair<expr*, int>> rhs_elements,
                                            std::map<expr*, int> connectedVariables);
            /*
             * Flat = sum (flats)
             */
            std::string generateConstraint02(
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
