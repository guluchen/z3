#include <algorithm>
#include <functional>
#include <numeric>
#include "ast/ast_ll_pp.h"
#include "ast/ast_pp.h"
#include "ast/ast_smt2_pp.h"
#include "ast/ast_util.h"
#include "ast/rewriter/seq_rewriter.h"
#include "smt_kernel.h"
#include "smt/smt_context.h"
#include "smt/smt_model_generator.h"
#include "smt/theory_arith.h"
#include "smt/theory_array_base.h"
#include "smt/theory_array_full.h"
#include "smt/theory_array.h"
#include "smt/theory_seq_empty.h"
#include "smt/theory_str.h"
#include "smt/theory_lra.h"

/* TODO:
 *  1. better algorithm for checking solved form
 *  2. on-the-fly over-approximation
 *  3. better algorithm for computing state transform
 */

namespace smt {

    namespace str {

        using namespace std::placeholders;

        class seq_expr_solver : public expr_solver {
            kernel m_kernel;
        public:
            seq_expr_solver(ast_manager& m, smt_params& fp):
                    m_kernel(m, fp)
            {}

            lbool check_sat(expr* e) override {
                m_kernel.push();
                m_kernel.assert_expr(e);
                lbool r = m_kernel.check();
                m_kernel.pop(1);
                IF_VERBOSE(11, verbose_stream() << "is " << r << " " << mk_pp(e, m_kernel.m()) << "\n");
                return r;
            }
        };

        const element& element::null() {
            static const element e{element_t::NONE, ""};
            return e;
        }

        const bool element::operator==(const element& other) const {
            return other.m_type == m_type && other.m_value == m_value;
        }

        const bool element::operator<(const element& other) const {
            if (m_type < other.m_type) return true;
            if (m_type > other.m_type) return false;
            return m_value < other.m_value;
        }

        std::ostream& operator<<(std::ostream& os, const element& s) {
            os << s.value();
            return os;
        }

        const word_term& word_term::null() {
            static const word_term w{element::null()};
            return w;
        }

        word_term word_term::of_string(const std::string& literal) {
            word_term result;
            for (auto i = literal.length() - 2; i > 0; i--) {
                result.m_elements.push_front(element{element_t::CONST, literal.substr(i, 1)});
            }
            return result;
        }

        word_term word_term::of_variable(const std::string& name) {
            word_term result;
            result.m_elements.push_front(element{element_t::VAR, name});
            return result;
        }

        const bool
        word_term::prefix_mismatched_in_consts(const word_term& w1, const word_term& w2) {
            if (w1.empty() || w2.empty()) return false;

            auto it1 = w1.m_elements.begin();
            auto it2 = w2.m_elements.begin();
            while (*it1 == *it2) {
                if (++it1 == w1.m_elements.end() || ++it2 == w2.m_elements.end()) return false;
            }
            return it1->typed(element_t::CONST) && it2->typed(element_t::CONST) &&
                   it1->value() != it2->value();
        }

        const bool
        word_term::suffix_mismatched_in_consts(const word_term& w1, const word_term& w2) {
            if (w1.empty() || w2.empty()) return false;

            auto it1 = w1.m_elements.end();
            auto it2 = w2.m_elements.end();
            while (*it1 == *it2) {
                if (--it1 == w1.m_elements.begin() || --it2 == w2.m_elements.begin()) return false;
            }
            return it1->typed(element_t::CONST) && it2->typed(element_t::CONST) &&
                   it1->value() != it2->value();
        }

        const bool word_term::unequalable_no_empty_var(const word_term& w1, const word_term& w2) {
            return (!w1.has_variable() && w1.length() < w2.length()) ||
                   (!w2.has_variable() && w2.length() < w1.length()) ||
                   prefix_mismatched_in_consts(w1, w2) || suffix_mismatched_in_consts(w1, w2);
        }

        const bool word_term::unequalable(const word_term& w1, const word_term& w2) {
            return (!w1.has_variable() && w1.constant_count() < w2.constant_count()) ||
                   (!w2.has_variable() && w2.constant_count() < w1.constant_count()) ||
                   prefix_mismatched_in_consts(w1, w2) || suffix_mismatched_in_consts(w1, w2);
        }

        word_term::word_term(std::initializer_list<element> list) {
            m_elements.insert(m_elements.begin(), list.begin(), list.end());
        }

        const std::size_t word_term::constant_count() const {
            static const auto& is_const = std::bind(&element::typed, _1, element_t::CONST);
            return (std::size_t) std::count_if(m_elements.begin(), m_elements.end(), is_const);
        }

        const std::set<element> word_term::variables() const {
            std::set<element> result;
            for (const auto& e : m_elements) {
                if (e.typed(element_t::VAR)) {
                    result.insert(e);
                }
            }
            return result;
        }

        const bool word_term::has_constant() const {
            static const auto& is_const = std::bind(&element::typed, _1, element_t::CONST);
            return std::any_of(m_elements.begin(), m_elements.end(), is_const);
        }

        const bool word_term::has_variable() const {
            static const auto& is_var = std::bind(&element::typed, _1, element_t::VAR);
            return std::any_of(m_elements.begin(), m_elements.end(), is_var);
        }

        const bool word_term::check_head(const element_t& t) const {
            const element& h = head();
            return h && h.typed(t);
        }

        const element& word_term::head() const {
            return m_elements.empty() ? element::null() : m_elements.front();
        }

        void word_term::remove_head() {
            SASSERT(!m_elements.empty());

            m_elements.pop_front();
        }

        void word_term::concat(const word_term& other) {
            m_elements.insert(m_elements.end(), other.m_elements.begin(), other.m_elements.end());
        }

        void word_term::replace(const element& tgt, const word_term& subst) {
            auto fit = std::find(m_elements.begin(), m_elements.end(), tgt);
            while (fit != m_elements.end()) {
                m_elements.insert(fit, subst.m_elements.begin(), subst.m_elements.end());
                m_elements.erase(fit++);
                fit = std::find(fit, m_elements.end(), tgt);
            }
        }

        const bool word_term::operator==(const word_term& other) const {
            return !(*this < other) && !(other < *this);
        }

        const bool word_term::operator<(const word_term& other) const {
            if (m_elements.size() < other.m_elements.size()) return true;
            if (m_elements.size() > other.m_elements.size()) return false;
            // when having same length, do lexicographical compare
            return m_elements < other.m_elements;
        }

        std::ostream& operator<<(std::ostream& os, const word_term& w) {
            if (w.empty()) {
                return os << "\"\"" << std::flush;
            }

            bool in_consts = false;
            const element& head = w.m_elements.front();
            if (head.typed(element_t::CONST)) {
                in_consts = true;
                os << '"' << head;
            } else os << head;
            for (auto it = ++(w.m_elements.begin()); it != w.m_elements.end(); it++) {
                if (it->typed(element_t::CONST)) {
                    if (!in_consts) {
                        in_consts = true;
                        os << " \"" << *it;
                    } else os << *it;
                } else {
                    if (in_consts) {
                        in_consts = false;
                        os << "\" " << *it;
                    } else os << ' ' << *it;
                }
            }
            if (in_consts) os << '"';
            return os << std::flush;
        }

        const word_equation& word_equation::null() {
            static const word_equation we{word_term::null(), word_term::null()};
            return we;
        }

        word_equation::word_equation(const word_term& lhs, const word_term& rhs) {
            if (lhs < rhs) {
                m_lhs = lhs;
                m_rhs = rhs;
            } else {
                m_lhs = rhs;
                m_rhs = lhs;
            }
        }

        const std::set<element> word_equation::variables() const {
            std::set<element> result;
            for (const auto& v : m_lhs.variables()) {
                result.insert(v);
            }
            for (const auto& v : m_rhs.variables()) {
                result.insert(v);
            }
            return result;
        }

        const element& word_equation::definition_var() const {
            if (m_lhs.length() == 1 && m_lhs.check_head(element_t::VAR)) {
                return m_lhs.head();
            }
            if (m_rhs.length() == 1 && m_rhs.check_head(element_t::VAR)) {
                return m_rhs.head();
            }
            return element::null();
        }

        const word_term& word_equation::definition_body() const {
            if (m_lhs.length() == 1 && m_lhs.check_head(element_t::VAR)) {
                return m_rhs;
            }
            if (m_rhs.length() == 1 && m_rhs.check_head(element_t::VAR)) {
                return m_lhs;
            }
            return word_term::null();
        }

        const bool word_equation::unsolvable(const bool allow_empty_var) const {
            return allow_empty_var ? word_term::unequalable(m_lhs, m_rhs)
                                   : word_term::unequalable_no_empty_var(m_lhs, m_rhs);
        }

        const bool word_equation::in_definition_form() const {
            return (bool) definition_var();
        }

        const bool word_equation::check_heads(const element_t& lht, const element_t& rht) const {
            return m_lhs.check_head(lht) && m_rhs.check_head(rht);
        }

        word_equation word_equation::trim_prefix() const {
            word_equation result{*this};
            word_term& lhs = result.m_lhs;
            word_term& rhs = result.m_rhs;
            while (!lhs.empty() && !rhs.empty() && lhs.head() == rhs.head()) {
                lhs.remove_head();
                rhs.remove_head();
            }
            return result;
        }

        word_equation word_equation::replace(const element& tgt, const word_term& subst) const {
            word_equation result{*this};
            result.m_lhs.replace(tgt, subst);
            result.m_rhs.replace(tgt, subst);
            result.sort();
            return result;
        }

        word_equation word_equation::remove(const element& tgt) const {
            return replace(tgt, {});
        }

        word_equation word_equation::remove_all(const std::set<element>& tgt) const {
            word_equation result{*this};
            for (const auto& e : tgt) {
                result.m_lhs.replace(e, {});
                result.m_rhs.replace(e, {});
            }
            result.sort();
            return result;
        }

        const bool word_equation::operator==(const word_equation& other) const {
            return !(*this < other) && !(other < *this);
        }

        const bool word_equation::operator<(const word_equation& other) const {
            if (m_lhs < other.m_lhs) return true;
            if (other.m_lhs < m_lhs) return false;
            return m_rhs < other.m_rhs;
        }

        std::ostream& operator<<(std::ostream& os, const word_equation& we) {
            os << we.m_lhs << " = " << we.m_rhs;
            return os;
        }

        void word_equation::sort() {
            if (!(m_lhs < m_rhs)) {
                std::swap(m_lhs, m_rhs);
            }
        }

        state::transform::transform(const state& s, const word_equation& src, const bool by_wi)
                : m_state{s}, m_src{src}, m_src_should_fail{by_wi} {
        }

        const bool state::transform::src_vars_empty() const {
            return !m_src_should_fail && m_src.lhs().empty();
        }

        const bool state::transform::src_var_well_defined() const {
            if (m_src_should_fail) return false;

            const word_term& def_body = m_src.definition_body();
            return def_body && (def_body.length() == 1 || !def_body.has_variable());
        }

        const bool state::transform::src_two_var_unequal() const {
            if (m_src_should_fail) return false;

            const word_term& def_body = m_src.definition_body();
            return def_body && def_body.length() == 1;
        }

        void state::transform::transform_one_var() {
            const head_pair& hh = m_src.heads();
            SASSERT(hh.first && hh.second);

            const bool var_const_headed = hh.first.typed(element_t::VAR);
            const element& v = var_const_headed ? hh.first : hh.second;
            const element& c = var_const_headed ? hh.second : hh.first;
            m_result.push_back(m_state.replace(v, {c, v}));
            if (m_state.m_allow_empty_var) {
                m_result.push_back(m_state.remove(v));
            } else {
                m_result.push_back(m_state.replace(v, {c}));
            }
        }

        void state::transform::transform_two_var() {
            const head_pair& hh = m_src.heads();
            SASSERT(hh.first && hh.second);

            const element& x = hh.first;
            const element& y = hh.second;
            m_result.push_back(m_state.replace(x, {y, x}));
            m_result.push_back(m_state.replace(y, {x, y}));
            if (m_state.m_allow_empty_var) {
                m_result.push_back(m_state.remove(x));
                m_result.push_back(m_state.remove(y));
            } else {
                m_result.push_back(m_state.replace(x, {y}));
            }
        }

        std::list<state> state::transform::compute() {
            if (src_vars_empty()) {
                SASSERT(m_state.m_allow_empty_var && !m_src.rhs().has_constant());
                m_result.push_back(m_state.remove_all(m_src.rhs().variables()));
                return m_result;
            }
            if (src_var_well_defined()) {
                const element& var = m_src.definition_var();
                m_result.push_back(m_state.replace(var, m_src.definition_body()));
                return m_result;
            }
            if (m_src.check_heads(element_t::VAR, element_t::VAR)) {
                transform_two_var();
            } else {
                transform_one_var();
            }
            return m_result;
        }

        const std::set<element> state::variables() const {
            std::set<element> result;
            for (const auto& we : m_wes_to_satisfy) {
                for (const auto& v : we.variables()) {
                    result.insert(v);
                }
            }
            for (const auto& we : m_wes_to_fail) {
                for (const auto& v : we.variables()) {
                    result.insert(v);
                }
            }
            return result;
        }

        const word_equation& state::only_one_equation_left() const {
            return m_wes_to_satisfy.size() == 1 ? *m_wes_to_satisfy.begin()
                                                : word_equation::null();
        }

        const std::vector<std::vector<word_term>> state::equivalence_classes() const {
            std::map<word_term, std::size_t> word_class_tbl;
            std::vector<std::vector<word_term>> classes;
            for (const auto& we : m_wes_to_satisfy) {
                const word_term& w1 = we.lhs();
                const word_term& w2 = we.rhs();
                const auto& fit1 = word_class_tbl.find(w1);
                const auto& fit2 = word_class_tbl.find(w2);
                if (fit1 != word_class_tbl.end() && fit2 != word_class_tbl.end()) continue;
                if (fit1 == word_class_tbl.end() && fit2 == word_class_tbl.end()) {
                    classes.push_back({w1, w2});
                    const auto class_id = classes.size() - 1;
                    word_class_tbl[w1] = class_id;
                    word_class_tbl[w2] = class_id;
                    continue;
                }
                if (fit1 != word_class_tbl.end()) {
                    const auto class_id = fit1->second;
                    classes.at(class_id).push_back(w2);
                    word_class_tbl[w2] = class_id;
                } else {
                    const auto class_id = fit2->second;
                    classes.at(class_id).push_back(w1);
                    word_class_tbl[w1] = class_id;
                }
            }
            return classes;
        }

        const bool state::equivalence_classes_inconsistent() const {
            const auto& unequalable = m_allow_empty_var ? word_term::unequalable
                                                        : word_term::unequalable_no_empty_var;
            for (const auto& cls : equivalence_classes()) {
                if (cls.size() == 2) {
                    if (unequalable(cls.at(0), cls.at(1))) return true;
                    continue;
                }
                std::vector<bool> select(cls.size());
                std::fill(select.end() - 2, select.end(), true);
                do {
                    std::vector<word_term> selected;
                    selected.reserve(2);
                    for (std::size_t i = 0; i < cls.size(); i++) {
                        if (select.at(i)) {
                            selected.push_back(cls.at(i));
                        }
                    }
                    if (unequalable(selected.at(0), selected.at(1))) return true;
                } while (std::next_permutation(select.begin(), select.end()));
            }
            return false;
        }

        const bool state::disequalities_inconsistent() const {
            return !m_wes_to_fail.empty() && m_wes_to_fail.begin()->empty();
        }

        const bool state::unsolvable_by_check() const {
            const auto& unsolvable = std::bind(&word_equation::unsolvable, _1, m_allow_empty_var);
            return std::any_of(m_wes_to_satisfy.begin(), m_wes_to_satisfy.end(), unsolvable) ||
                   disequalities_inconsistent();
        }

        const bool state::unsolvable_by_inference() const {
            return disequalities_inconsistent() || equivalence_classes_inconsistent();
        }

        const bool state::in_definition_form() const {
            static const auto& in_def_form = std::mem_fn(&word_equation::in_definition_form);
            return std::all_of(m_wes_to_satisfy.begin(), m_wes_to_satisfy.end(), in_def_form);
        }

        const bool state::in_solved_form() const {
            return (in_definition_form() && definition_acyclic()) || m_wes_to_satisfy.empty();
        }

        void state::satisfy_constraint(const word_equation& we) {
            SASSERT(we);

            if (we.empty()) return;
            const word_equation& trimmed = we.trim_prefix();
            if (trimmed.empty()) return;
            m_wes_to_satisfy.insert(trimmed);
        }

        void state::fail_constraint(const word_equation& we) {
            SASSERT(we);

            const word_equation& trimmed = we.trim_prefix();
            if (trimmed.unsolvable(m_allow_empty_var)) return;
            m_wes_to_fail.insert(trimmed);
        }

        state state::replace(const element& tgt, const word_term& subst) const {
            state result{m_allow_empty_var};
            for (const auto& we : m_wes_to_satisfy) {
                result.satisfy_constraint(we.replace(tgt, subst));
            }
            for (const auto& we : m_wes_to_fail) {
                result.fail_constraint(we.replace(tgt, subst));
            }
            return result;
        }

        state state::remove(const element& tgt) const {
            return replace(tgt, {});
        }

        state state::remove_all(const std::set<element>& tgt) const {
            state result{m_allow_empty_var};
            for (const auto& we : m_wes_to_satisfy) {
                result.satisfy_constraint(we.remove_all(tgt));
            }
            for (const auto& we : m_wes_to_fail) {
                result.fail_constraint(we.remove_all(tgt));
            }
            return result;
        }

        const std::list<state> state::transform() const {
            SASSERT(!unsolvable_by_check() && !m_wes_to_satisfy.empty());
            const word_equation& curr_we = *m_wes_to_satisfy.begin();
            const head_pair& hh = curr_we.heads();

            std::list<state> result;
            if (m_allow_empty_var && curr_we.lhs().empty()) {
                SASSERT(!curr_we.rhs().has_constant());
                result.push_back(remove_all(curr_we.rhs().variables()));
                return result;
            }
            const word_term& def_body = curr_we.definition_body();
            if (def_body && (def_body.length() == 1 || !def_body.has_variable())) {
                result.push_back(replace(curr_we.definition_var(), def_body));
                return result;
            }

            if (curr_we.check_heads(element_t::VAR, element_t::VAR)) {
                transform_two_var(hh, result);
            } else {
                transform_one_var(hh, result);
            }
            return result;
        }

        const bool state::operator<(const state& other) const {
            if (m_allow_empty_var != other.m_allow_empty_var) return false;
            if (m_wes_to_satisfy.size() < other.m_wes_to_satisfy.size()) return true;
            if (m_wes_to_satisfy.size() > other.m_wes_to_satisfy.size()) return false;
            if (m_wes_to_fail.size() < other.m_wes_to_fail.size()) return true;
            if (m_wes_to_fail.size() > other.m_wes_to_fail.size()) return false;
            // when having same length, do lexicographical compare
            return m_wes_to_satisfy < other.m_wes_to_satisfy || m_wes_to_fail < other.m_wes_to_fail;
        }

        std::ostream& operator<<(std::ostream& os, const state& s) {
            for (const auto& we : s.m_wes_to_satisfy) {
                os << we << '\n';
            }
            for (const auto& we : s.m_wes_to_fail) {
                os << "not (" << we << ")\n";
            }
            return os << std::flush;
        }

        const bool state::dag_def_check_node(const def_graph& graph, const def_node& node,
                                             def_nodes& marked, def_nodes& checked) {
            if (checked.find(node) != checked.end()) return true;
            if (marked.find(node) != marked.end()) return false;

            marked.insert(node);
            const auto& dept_dests = graph.find(node);
            if (dept_dests != graph.end()) {
                for (const auto& next : dept_dests->second) {
                    if (!dag_def_check_node(graph, next, marked, checked)) return false;
                }
            }
            checked.insert(node);
            return true;
        }

        const bool state::definition_acyclic() const {
            SASSERT(in_definition_form());

            def_graph graph;
            def_nodes marked;
            def_nodes checked;
            for (const auto& we : m_wes_to_satisfy) {
                const def_node& node = we.definition_var();
                if (graph.find(node) != graph.end()) return false; // definition not unique
                graph[node] = we.definition_body().variables();
            }
            for (const auto& dept_dests : graph) {
                if (!dag_def_check_node(graph, dept_dests.first, marked, checked)) return false;
            }
            return true;
        }

        const state::trans_source state::transformation_source() const {
            SASSERT(!m_wes_to_satisfy.empty() || !m_wes_to_fail.empty());

            const word_equation& null = word_equation::null();
            if (m_wes_to_satisfy.empty()) {
                SASSERT(!m_wes_to_fail.begin()->empty());
                return {null, *m_wes_to_fail.begin()};
            }
            if (m_wes_to_fail.empty()) return {*m_wes_to_satisfy.begin(), null};
            SASSERT(!m_wes_to_fail.begin()->empty());
            const word_equation& we = *m_wes_to_satisfy.begin();
            const word_equation& wi = *m_wes_to_fail.begin();
            return we < wi ? trans_source{we, null} : trans_source{null, wi};
        }

        void state::transform_one_var(const head_pair& hh, std::list<state>& result) const {
            SASSERT(hh.first);
            SASSERT(hh.second);

            const bool var_const_headed = hh.first.typed(element_t::VAR);
            const element& v = var_const_headed ? hh.first : hh.second;
            const element& c = var_const_headed ? hh.second : hh.first;
            result.push_back(replace(v, {c, v}));
            result.push_back(replace(v, {c}));
            if (m_allow_empty_var) {
                result.push_back(remove(v));
            }
        }

        void state::transform_two_var(const head_pair& hh, std::list<state>& result) const {
            SASSERT(hh.first);
            SASSERT(hh.second);

            const element& x = hh.first;
            const element& y = hh.second;
            result.push_back(replace(x, {y, x}));
            result.push_back(replace(y, {x, y}));
            result.push_back(replace(x, {y}));
            if (m_allow_empty_var) {
                result.push_back(remove(x));
                result.push_back(remove(y));
            }
        }

        neilson_based_solver::neilson_based_solver(const state& root) : m_solution_found{false} {
            m_pending.push(root);
        }

        void neilson_based_solver::explore_var_empty_cases() {
            while (!m_pending.empty()) {
                const state curr_case{std::move(m_pending.top())};
                if (curr_case.in_solved_form()) {
                    m_solution_found = true;
                    return;
                }
                m_pending.pop();
                if (m_processed.find(curr_case) != m_processed.end()) continue;
                if (curr_case.unsolvable_by_check()) {
                    STRACE("str", tout << "failed:\n" << curr_case << std::endl;);
                    continue;
                }
                m_processed.insert(curr_case);
                STRACE("str", tout << "add:\n" << curr_case << std::endl;);
                for (const auto& var : curr_case.variables()) {
                    m_pending.push(curr_case.remove(var));
                }
            }
            std::set<state> processed;
            for (auto c : m_processed) {
                c.allow_empty_variable(false);
                processed.insert(c);
                m_pending.push(std::move(c));
            }
            m_processed = std::move(processed);
        }

        void neilson_based_solver::check_sat() {
            STRACE("str", tout << "[Check SAT]\n";);
            while (!m_pending.empty()) {
                state curr_s = m_pending.top();
                m_pending.pop();
                STRACE("str", tout << __LINE__ << "from:\n" << curr_s << std::endl;);
                for (const auto& next_s : curr_s.transform()) {
                    if (m_processed.find(next_s) != m_processed.end()) {
                        STRACE("str", tout << __LINE__ << " already visited:\n" << next_s << std::endl;);
                        continue;
                    }
                    m_processed.insert(next_s);
                    if (next_s.unsolvable_by_inference()) {
                        STRACE("str", tout << "failed:\n" << next_s << std::endl;);
                        continue;
                    }
                    if (next_s.in_solved_form()) {
                        STRACE("str", tout << "solved:\n" << next_s << std::endl;);
                        m_solution_found = true;
                        return;
                    }
                    const word_equation& last_we = next_s.only_one_equation_left();
                    if (last_we && last_we.in_definition_form()) {
                        // solved form check failed, the we in definition form must be recursive
                        const word_equation& last_we_recursive_def = last_we;
                        if (!last_we_recursive_def.definition_body().has_constant()) {
                            STRACE("str", tout << "solved:\n" << next_s << std::endl;);
                            m_solution_found = true;
                            return;
                        }
                        STRACE("str", tout << "failed:\n" << next_s << std::endl;);
                        continue;
                    }
                    STRACE("str", tout << "to:\n" << next_s << std::endl;);
                    m_pending.push(next_s);
                }
            }
        }

    }

    theory_str::theory_str(ast_manager& m, const theory_str_params& params)
            : theory(m.mk_family_id("seq")),
              m_params(params),
            /* Options */

              opt_DisableIntegerTheoryIntegration(false),

            /* Internal setup */
              search_started(false),
              opt_ConcatOverlapAvoid(true),
              m_autil(m),
              m_arrayUtil(m),
              m_scope_level(0),
              u(m),
              m_rewrite(m),
              m_seq_rewrite(m),
              m_trail(m),
              m_delayed_axiom_setup_terms(m),
              m_delayed_assertions_todo(m),
              m_persisted_axiom_todo(m),
              string_int_conversion_terms(m),
              contains_map(m),
              m_fresh_id(0),
              totalCacheAccessCount(0),
              m_find(*this),
              m_trail_stack(*this),
              m_mk_aut(m),
              m_res(m),
              uState(m),
              impliedFacts(m){
        str_int_bound = rational(0);
    }

    void theory_str::display(std::ostream& os) const {
        os << "theory_str display" << std::endl;
    }

    class seq_expr_solver : public expr_solver {
        kernel m_kernel;
    public:
        seq_expr_solver(ast_manager& m, smt_params& fp):
                m_kernel(m, fp)
        {}

        lbool check_sat(expr* e) override {
            m_kernel.push();
            m_kernel.assert_expr(e);
            lbool r = m_kernel.check();
            m_kernel.pop(1);
            return r;
        }
    };

    void theory_str::init(context *ctx) {
        theory::init(ctx);
    }

    bool theory_str::internalize_atom(app *const atom, const bool gate_ctx) {
        (void) gate_ctx;
        return internalize_term(atom);
    }

    bool theory_str::internalize_term(app *const term) {
        ast_manager& m = get_manager();
        context& ctx = get_context();
        SASSERT(term->get_family_id() == get_family_id());

        const unsigned num_args = term->get_num_args();
        for (unsigned i = 0; i < num_args; i++) {
            ctx.internalize(term->get_arg(i), false);
        }
        if (ctx.e_internalized(term)) {
            mk_var(ctx.get_enode(term));
            return true;
        }
        enode *const e = ctx.mk_enode(term, false, m.is_bool(term), true);
        if (m.is_bool(term)) {
            const bool_var& bv = ctx.mk_bool_var(term);
            ctx.set_var_theory(bv, get_id());
            ctx.set_enode_flag(bv, true);
        }
        for (unsigned i = 0; i < num_args; i++) {
            enode *arg = e->get_arg(i);
            const theory_var& v_arg = mk_var(arg);
            (void) v_arg;
        }

        const theory_var& v = mk_var(e);
        (void) v;
        return true;
    }

    theory_var theory_str::mk_var(enode *const n) {
        ast_manager & m = get_manager();
        if (!(m.get_sort(n->get_owner()) == u.str.mk_string_sort())) {
            return null_theory_var;
        }
        if (is_attached_to_var(n)) {
            return n->get_th_var(get_id());
        } else {
            theory_var v = theory::mk_var(n);
            m_find.mk_var();
            get_context().attach_th_var(n, this, v);
            get_context().mark_as_relevant(n);
            return v;
        }
    }

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
    app * theory_str::mk_value_helper(app * n, model_generator& mg) {
        if (u.str.is_string(n)) {
            return n;
        } else if (u.str.is_concat(n)) {
            // recursively call this function on each argument
            SASSERT(n->get_num_args() == 2);
            expr * a0 = n->get_arg(0);
            expr * a1 = n->get_arg(1);

            app * a0_conststr = mk_value_helper(to_app(a0), mg);
            app * a1_conststr = mk_value_helper(to_app(a1), mg);

            if (a0_conststr != nullptr && a1_conststr != nullptr) {
                zstring a0_s, a1_s;
                u.str.is_string(a0_conststr, a0_s);
                u.str.is_string(a1_conststr, a1_s);
                zstring result = a0_s + a1_s;
                return to_app(mk_string(result));
            }
        }

        // fallback path
        // try to find some constant string, anything, in the equivalence class of n
        bool hasEqc = false;
        expr * n_eqc = get_eqc_value(n, hasEqc);
        if (hasEqc) {
            return to_app(n_eqc);
        } else {
            return nullptr;
        }
    }



    template <class T>
    static T* get_th_arith(context& ctx, theory_id afid, expr* e) {
        theory* th = ctx.get_theory(afid);
        if (th && ctx.e_internalized(e)) {
            return dynamic_cast<T*>(th);
        }
        else {
            return nullptr;
        }
    }

    template <class T>
    static T* get_th_array(context& ctx, theory_id afid, expr* e) {
        theory* th = ctx.get_theory(afid);
        if (th && ctx.e_internalized(e)) {
            return dynamic_cast<T*>(th);
        }
        else {
            if (th) {
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": not NULL" << std::endl;);
            }
            else
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": NULL" << std::endl;);
            return nullptr;
        }
    }

    model_value_proc *theory_str::mk_value(enode *const n, model_generator& mg) {
        ast_manager& m = get_manager();
        context & ctx = get_context();
        app_ref owner{m};
        owner = n->get_owner();
        // if the owner is not internalized, it doesn't have an e-node associated.
        SASSERT(get_context().e_internalized(owner));

        rational vLen;
        if (get_len_value(n->get_owner(), vLen)) {
        }
        else {
            vLen.reset();
            ptr_vector<expr> leafNodes;
            if (u.str.is_concat(owner)) {
                get_nodes_in_concat(n->get_owner(), leafNodes);
            }
            else
                leafNodes.push_back(n->get_owner());

            for (int i = 0; i < leafNodes.size(); ++i) {
                STRACE("str", tout << __LINE__ << " get len value :  " << mk_pp(leafNodes[i], m) << std::endl;);
                zstring valueStr;
                if (u.str.is_string(leafNodes[i], valueStr)) {
                    vLen = vLen + valueStr.length();
                }
                else {
                    expr *value = query_theory_arith_core(mk_strlen(leafNodes[i]), mg);
                    if (value != nullptr) {
                        rational tmp;
                        if (m_autil.is_numeral(value, tmp))
                            vLen = vLen + tmp;
                        STRACE("str", tout << __LINE__ << " len value :  " << mk_pp(mk_strlen(leafNodes[i]), m) << ": "
                                           << mk_pp(value, m) << " --> " << vLen
                                           << std::endl;);
                    } else {
                        vLen = -1;
                        break;
                    }
                }
            }
        }

        if (vLen.get_int64() == 0)
            return alloc(expr_wrapper_proc, u.str.mk_string(zstring("")));

        app * val = mk_value_helper(owner, mg);
        if (val != nullptr) {
            return alloc(expr_wrapper_proc, val);
        } else {
            theory_var v       = n->get_th_var(get_id());
            SASSERT(v != null_theory_var);
            sort * s           = get_manager().get_sort(n->get_owner());
            string_value_proc * result = nullptr;

            expr* importantNode = nullptr;
            expr* regex = nullptr;
            is_regex_var(owner.get(), regex);
            expr* arr_var = getExprVarFlatArray(owner.get());
            if (is_important(owner.get()) && arr_var != nullptr) {
                STRACE("str", tout << __LINE__ << "mk_value for: " << mk_ismt2_pp(owner, m) << " (sort "
                                   << mk_ismt2_pp(m.get_sort(owner), m) << ")" << std::endl;);

                enode* arrNode = ctx.get_enode(getExprVarFlatArray(owner.get()));

                result = alloc(string_value_proc, *this, s, n->get_owner(), true, arrNode, regex, vLen.get_int64());
                importantNode = owner.get();
            }
            else {
                STRACE("str", tout << __LINE__ << "mk_value for: " << mk_ismt2_pp(owner, m) << " (sort "
                                   << mk_ismt2_pp(m.get_sort(owner), m) << ")" << std::endl;);
                bool found = false;
                expr_ref_vector eqSet(m);
                collect_eq_nodes(owner.get(), eqSet);
                expr* reg = nullptr;
                for (int i = 0; i < eqSet.size(); ++i) {
                    if ((is_important(eqSet[i].get()) && !u.str.is_concat(eqSet[i].get())) || isInternalRegexVar(eqSet[i].get(), reg)) {

                        enode* arrNode = ctx.get_enode(getExprVarFlatArray(eqSet[i].get()));
                        result = alloc(string_value_proc, *this, s, n->get_owner(), true,
                                       arrNode, regex, vLen.get_int64());
                        found = true;
                        importantNode = eqSet[i].get();
                        break;
                    }
                }

                if (!found) {
                    result = alloc(string_value_proc, *this, s, n->get_owner(), false, regex, vLen.get_int64());
                }
            }

            SASSERT(result != 0);
            STRACE("str", tout << __LINE__ << "mk_value for: " << mk_ismt2_pp(owner, m) << " (sort "
                               << mk_ismt2_pp(m.get_sort(owner), m) << ")" << std::endl;);
            std::set<expr*> dep = getDependency(owner);
            expr* reg = nullptr;
            if (importantNode != nullptr) {
                // add array
                result->add_entry(ctx.get_enode(getExprVarFlatArray(importantNode)));

                std::set<expr*> depImp = getDependency(importantNode);
                dep.insert(depImp.begin(), depImp.end());

                // add subvars
//                for (const auto& nn : dep)
//                    if (ctx.e_internalized(nn) && ctx.e_internalized(mk_strlen(nn))) {
//                        // add sublen
//                        result->add_entry(ctx.get_enode(mk_strlen(nn)));
//                    }

                // add its ancestors
                for (const auto& nn : backwardDep[owner]) {
                    result->add_entry(ctx.get_enode(nn));
                }
            }
            else if (isInternalRegexVar(owner.get(), reg)){
                // add array
                result->add_entry(ctx.get_enode(getExprVarFlatArray(owner.get())));

                // add its ancestors
                for (const auto& nn : backwardDep[owner]) {
                    result->add_entry(ctx.get_enode(nn));
                }
            }
            else {
                // normal node
                STRACE("str", tout << __LINE__ << "mk_value for: " << mk_ismt2_pp(owner, m) << " (sort "
                                   << mk_ismt2_pp(m.get_sort(owner), m) << ")" << std::endl;);
                // all all lens
                for (const auto& nn : dep)
                    if (ctx.e_internalized(nn)){
                        STRACE("str", tout << __LINE__ << " " << mk_pp(nn, m) << std::endl;);
                        if (is_important(nn) || is_regex_var(nn)) {
                            result->add_entry(ctx.get_enode(nn));
                        }
                        // add sublen
//                        if (ctx.e_internalized(mk_strlen(nn)))
//                            result->add_entry(ctx.get_enode(mk_strlen(nn)));
                    }

                // add its ancestors
                for (const auto& nn : backwardDep[owner])
                    if (ctx.e_internalized(nn)){
                        result->add_entry(ctx.get_enode(nn));
                    }

                if (linkers.find(owner) != linkers.end())
                    result->set_linker(linkers[owner]);
            }

            if (!u.str.is_concat(owner)) {
                if (ctx.e_internalized(mk_strlen(owner)))
                    result->add_entry(ctx.get_enode(mk_strlen(owner)));
            }

            return result;
        }
        return alloc(expr_wrapper_proc, owner);
    }

    bool theory_str::is_important(expr* n){
        expr_ref_vector eq(get_manager());
        collect_eq_nodes(n, eq);
        for (const auto& nn : uState.non_fresh_vars)
            if (eq.contains(nn.first))
                return true;
        return false;
    }

    bool theory_str::is_important(expr* n, int &val){
        for (const auto& nn : uState.non_fresh_vars)
            if (nn.first == n) {
                val = nn.second;
                if (val < 0)
                    val = connectingSize;
                return true;
            }
        return false;
    }

    bool theory_str::is_regex_var(expr* n, expr* &regexExpr){
        for (const auto& we: membership_memo) {
            if (we.first == n){
                regexExpr = we.second;
                return true;
            }
        }
        return false;
    }

    bool theory_str::is_regex_var(expr* n){
        for (const auto& we: membership_memo) {
            if (we.first == n){
                return true;
            }
        }
        return false;
    }

    bool theory_str::is_regex_concat(expr* n){
        ptr_vector<expr> argVec;
        get_nodes_in_concat(n, argVec);
        for (int i = 0; i < argVec.size(); ++i)
            if (!u.str.is_string(argVec[i]) && !is_regex_var(argVec[i])) {
                return false;
            }

        return true;
    }

    std::set<expr*> theory_str::getDependency(expr* n){
        std::set<expr*> ret;

        expr_ref_vector eq(get_manager());
        collect_eq_nodes(n, eq);

        if (u.str.is_concat(n)){
            ptr_vector<expr> argVec;
            get_all_nodes_in_concat(n, argVec);

            for (int i = 0; i < argVec.size(); ++i) {
                if (!eq.contains(argVec[i]))
                    ret.insert(argVec[i]);
                else {
                }
            }
        }

        for (int j = 0; j < eq.size(); ++j) {
            if (uState.eq_combination.find(eq[j].get()) != uState.eq_combination.end()) {
                for (const auto &nn : uState.eq_combination[eq[j].get()]) {
                    if (u.str.is_concat(nn)) {
                        ptr_vector<expr> argVec;
                        get_all_nodes_in_concat(nn, argVec);

                        for (int i = 0; i < argVec.size(); ++i) {
                            if (!eq.contains(argVec[i]))
                                ret.insert(argVec[i]);
                        }
                    } else {
                        if (!eq.contains(nn))
                            ret.insert(nn);
                    }
                }
            }
        }
        return ret;
    }

    void theory_str::add_theory_assumptions(expr_ref_vector& assumptions) {
        STRACE("str", tout << "add theory assumption for theory_str" << std::endl;);
    }

    lbool theory_str::validate_unsat_core(expr_ref_vector& unsat_core) {
        return l_undef;
    }

    void theory_str::new_eq_eh(theory_var x, theory_var y) {
        clock_t t = clock();
        ast_manager& m = get_manager();
        enode *const n1 = get_enode(x);
        enode *const n2 = get_enode(y);

        TRACE("str", tout << __FUNCTION__ << ":" << mk_ismt2_pp(n1->get_owner(), m) << " = "
                           << mk_ismt2_pp(n2->get_owner(), m) << "@lvl " << m_scope_level << std::endl;);

        handle_equality(get_enode(x)->get_owner(), get_enode(y)->get_owner());

        // merge eqc **AFTER** handle_equality
        m_find.merge(x, y);

        if (!is_trivial_eq_concat(n1->get_owner(), n2->get_owner())) {
            newConstraintTriggered = true;
            expr_ref tmp(createEqualOperator(n1->get_owner(), n2->get_owner()), m);
            ensure_enode(tmp);
            mful_scope_levels.push_back(tmp);

            const str::expr_pair we{expr_ref{n1->get_owner(), m}, expr_ref{n2->get_owner(), m}};
            m_we_expr_memo.push_back(we);
        }
        STRACE("str", tout << __LINE__ <<  " time: " << __FUNCTION__ << ":  " << ((float)(clock() - t))/CLOCKS_PER_SEC << std::endl;);
    }

    /*
     * x . "abc" = x . y && y = "abc"
     */
    bool theory_str::is_trivial_eq_concat(expr* x, expr* y){
        if (u.str.is_concat(x) && u.str.is_concat(y)) {
            expr* x0 = to_app(x)->get_arg(0);
            expr* x1 = to_app(x)->get_arg(1);
            expr* y0 = to_app(y)->get_arg(0);
            expr* y1 = to_app(y)->get_arg(1);
            if (are_equal_exprs(x0, y0) && are_equal_exprs(x1, y1)) {
                 return true;
            }
        }
        return false;
    }

    void theory_str::assert_cached_eq_state(){
        if (uState.reassertEQ) {
            return;
        }

        if (underapproximation_cached()) {
            need_change = true;
            uState.reassertEQ = true;
            newConstraintTriggered = true;
            int tmpz3State = get_actual_trau_lvl();
            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " z3_level " << tmpz3State << std::endl;);
            uState.eqLevel = tmpz3State;
        }

        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " impliedFacts size: " << impliedFacts.size() << std::endl;);
        if (impliedFacts.size() > 0){
            newConstraintTriggered = true;
            uState.reassertEQ = true;
            uState.eqLevel = get_actual_trau_lvl();
            for (const auto& e : impliedFacts) {
                assert_axiom(e);
            }
            if (uState.eqLevel == 0)
                impliedFacts.reset();
        }

    }

    void theory_str::handle_equality(expr * lhs, expr * rhs) {
        ast_manager & m = get_manager();
        context & ctx = get_context();
        // both terms must be of sort String
        sort * lhs_sort = m.get_sort(lhs);
        sort * rhs_sort = m.get_sort(rhs);
        sort * str_sort = u.str.mk_string_sort();

        if (lhs_sort != str_sort || rhs_sort != str_sort) {
            STRACE("str", tout << "skip equality: not String sort" << std::endl;);
            return;
        }

        /* // temporarily disabled, we are borrowing these testers for something else
           if (m_params.m_FiniteOverlapModels && !finite_model_test_varlists.empty()) {
           if (finite_model_test_varlists.contains(lhs)) {
           finite_model_test(lhs, rhs); return;
           } else if (finite_model_test_varlists.contains(rhs)) {
           finite_model_test(rhs, lhs); return;
           }
           }
        */

        if (u.str.is_concat(to_app(lhs)) && u.str.is_concat(to_app(rhs))) {
            bool nn1HasEqcValue = false;
            bool nn2HasEqcValue = false;
            get_eqc_value(lhs, nn1HasEqcValue);
            get_eqc_value(rhs, nn2HasEqcValue);

            expr * nn1_arg0 = to_app(lhs)->get_arg(0);
            expr * nn1_arg1 = to_app(lhs)->get_arg(1);
            expr * nn2_arg0 = to_app(rhs)->get_arg(0);
            expr * nn2_arg1 = to_app(rhs)->get_arg(1);
            if (nn1_arg0 == nn2_arg0 && in_same_eqc(nn1_arg1, nn2_arg1)) {
                STRACE("str", tout << "skip: lhs arg0 == rhs arg0" << std::endl;);
                return;
            }

            if (nn1_arg1 == nn2_arg1 && in_same_eqc(nn1_arg0, nn2_arg0)) {
                STRACE("str", tout << "skip: lhs arg1 == rhs arg1" << std::endl;);
                return;
            }
        }

        // newEqCheck() -- check consistency wrt. existing equivalence classes
        // TODO check all disequalities
        if (!new_eq_check(lhs, rhs)) {
            return;
        }

        expr* containKey;
        expr* simplifiedLhs = simplify_concat(lhs);
        expr* simplifiedRhs = simplify_concat(rhs);
        if (is_contain_equality(simplifiedLhs, containKey)) {
            zstring keyStr;
            expr_ref conclusion(mk_not(m, createEqualOperator(lhs, rhs)), m);
            expr_ref_vector premises(m);
            if (u.str.is_string(containKey, keyStr))
                if (new_eq_check_wrt_disequalities(rhs, premises, keyStr, conclusion)){
                    return;
                }
        }
        else if (is_contain_equality(simplifiedRhs, containKey)){
            zstring keyStr;
            expr_ref conclusion(mk_not(m, createEqualOperator(lhs, rhs)), m);
            expr_ref_vector premises(m);
            if (u.str.is_string(containKey, keyStr))
                if (new_eq_check_wrt_disequalities(lhs, premises, keyStr, conclusion)){
                    return;
                }
        }

        // BEGIN new_eq_handler() in strTheory

        // Check that a string's length can be 0 iff it is the empty string.
        check_eqc_empty_string(lhs, rhs);

        // (lhs == rhs) -> ( Length(lhs) == Length(rhs) )
        instantiate_str_eq_length_axiom(ctx.get_enode(lhs), ctx.get_enode(rhs));

        // group terms by equivalence class (groupNodeInEqc())

        std::set<expr*> eqc_concat_lhs;
        std::set<expr*> eqc_var_lhs;
        std::set<expr*> eqc_const_lhs;
        group_terms_by_eqc(lhs, eqc_concat_lhs, eqc_var_lhs, eqc_const_lhs);

        std::set<expr*> eqc_concat_rhs;
        std::set<expr*> eqc_var_rhs;
        std::set<expr*> eqc_const_rhs;
        group_terms_by_eqc(rhs, eqc_concat_rhs, eqc_var_rhs, eqc_const_rhs);

        TRACE("str",
              tout << "lhs eqc:" << std::endl;
                      tout << "Concats:" << std::endl;
                      for (std::set<expr*>::iterator it = eqc_concat_lhs.begin(); it != eqc_concat_lhs.end(); ++it) {
                          expr * ex = *it;
                          tout << mk_ismt2_pp(ex, get_manager()) << std::endl;
                      }
                      tout << "Variables:" << std::endl;
                      for (std::set<expr*>::iterator it = eqc_var_lhs.begin(); it != eqc_var_lhs.end(); ++it) {
                          expr * ex = *it;
                          tout << mk_ismt2_pp(ex, get_manager()) << std::endl;
                      }
                      tout << "Constants:" << std::endl;
                      for (std::set<expr*>::iterator it = eqc_const_lhs.begin(); it != eqc_const_lhs.end(); ++it) {
                          expr * ex = *it;
                          tout << mk_ismt2_pp(ex, get_manager()) << std::endl;
                      }

                      tout << "rhs eqc:" << std::endl;
                      tout << "Concats:" << std::endl;
                      for (std::set<expr*>::iterator it = eqc_concat_rhs.begin(); it != eqc_concat_rhs.end(); ++it) {
                          expr * ex = *it;
                          tout << mk_ismt2_pp(ex, get_manager()) << std::endl;
                      }
                      tout << "Variables:" << std::endl;
                      for (std::set<expr*>::iterator it = eqc_var_rhs.begin(); it != eqc_var_rhs.end(); ++it) {
                          expr * ex = *it;
                          tout << mk_ismt2_pp(ex, get_manager()) << std::endl;
                      }
                      tout << "Constants:" << std::endl;
                      for (std::set<expr*>::iterator it = eqc_const_rhs.begin(); it != eqc_const_rhs.end(); ++it) {
                          expr * ex = *it;
                          tout << mk_ismt2_pp(ex, get_manager()) << std::endl;
                      }
        );

        bool wrongStart, wrongEnd;
        if (is_inconsisten(eqc_concat_lhs, eqc_concat_rhs, eqc_const_lhs, eqc_const_rhs, wrongStart, wrongEnd)){
            STRACE("str", tout << __LINE__ << " is_inconsisten " << mk_pp(lhs, m) << " = " << mk_pp(rhs, m) << std::endl;);
            if (wrongStart || wrongEnd){
                negate_equality(lhs, rhs);
            } 

            return;
        }

        // step 1: Concat == Constant
        /*
         * Solve concatenations of the form:
         *   const == Concat(const, X)
         *   const == Concat(X, const)
         */
        if (eqc_const_lhs.size() != 0) {
            expr * conStr = *(eqc_const_lhs.begin());

            for (std::set<expr*>::iterator itor2 = eqc_concat_rhs.begin(); itor2 != eqc_concat_rhs.end(); itor2++) {
                solve_concat_eq_str(*itor2, conStr);
            }
        } else if (eqc_const_rhs.size() != 0) {
            expr* conStr = *(eqc_const_rhs.begin());

            for (std::set<expr*>::iterator itor1 = eqc_concat_lhs.begin(); itor1 != eqc_concat_lhs.end(); itor1++) {
                solve_concat_eq_str(*itor1, conStr);
            }
        }

        // n1 . n2 = n3 . n4 && n1 = n2 --> n3 = n4
        for (const auto c1 : eqc_concat_lhs){
            expr* n1 = to_app(c1)->get_arg(0);
            expr* n2 = to_app(c1)->get_arg(1);
            expr_ref_vector eqn1(m);
            collect_eq_nodes(n1, eqn1);

            expr_ref_vector eqn2(m);
            collect_eq_nodes(n2, eqn2);

            for (const auto c2 : eqc_concat_rhs)
                if (c1 != c2) {
                    expr *n3 = to_app(c2)->get_arg(0);
                    expr *n4 = to_app(c2)->get_arg(1);
                    if (eqn1.contains(n3) && n2 != n4) {
                        expr_ref_vector litems(m);
                        if (lhs != rhs)
                            litems.push_back(ctx.mk_eq_atom(lhs, rhs));
                        if (n1 != n3)
                            litems.push_back(ctx.mk_eq_atom(n1, n3));

                        expr_ref implyL(mk_and(litems), m);
                        assert_implication(implyL, ctx.mk_eq_atom(n2, n4));
                    }

                    if (eqn2.contains(n4) && n1 != n3) {
                        expr_ref_vector litems(m);
                        if (lhs != rhs)
                            litems.push_back(ctx.mk_eq_atom(lhs, rhs));
                        if (n2 != n4)
                            litems.push_back(ctx.mk_eq_atom(n2, n4));

                        expr_ref implyL(mk_and(litems), m);
                        assert_implication(implyL, ctx.mk_eq_atom(n1, n3));
                    }

                }
        }

        // n1 . "const" . n2 = n3 . "const" . n4 --> guess n1 = n3
//        for (const auto c1 : eqc_concat_lhs){
//            expr* n1 = to_app(c1)->get_arg(0);
//            expr_ref_vector eqn1(m);
//            collect_eq_nodes(n1, eqn1);
//
//            for (const auto& nn1 : eqn1)
//                if (u.str.is_concat(nn1)){
//                    ptr_vector<expr> elements_nn1;
//                    get_nodes_in_concat(nn1, elements_nn1);
//                    if (elements_nn1.size() == 2){
//
//                        for (const auto c2 : eqc_concat_rhs){
//                            expr* n2 = to_app(c2)->get_arg(0);
//                            expr_ref_vector eqn2(m);
//                            collect_eq_nodes(n2, eqn2);
//                            for (const auto& nn2 : eqn2)
//                                if (u.str.is_concat(nn2)){
//                                    ptr_vector<expr> elements_nn2;
//                                    get_nodes_in_concat(nn2, elements_nn2);
//                                    if (elements_nn2.size() == 2 &&
//                                            are_equal_exprs(elements_nn1[elements_nn1.size() - 1], elements_nn2[elements_nn2.size() - 1])){
//                                        expr* tmp = createEqualOperator(n1, n2);
//                                        ctx.force_phase(ctx.get_literal(tmp));
//                                        TRACE("str", tout << __LINE__ << " tryout eq " << __FUNCTION__ << ": "<< mk_pp(tmp, m) << std::endl;);
//                                    }
//                                }
//                        }
//                    }
//                }
//
//
//
//            n1 = to_app(c1)->get_arg(1);
//            eqn1.reset();
//            collect_eq_nodes(n1, eqn1);
//
//            for (const auto& nn1 : eqn1)
//                if (u.str.is_concat(nn1)){
//                    ptr_vector<expr> elements_nn1;
//                    get_nodes_in_concat(nn1, elements_nn1);
//                    if (elements_nn1.size() == 2){
//
//                        for (const auto c2 : eqc_concat_rhs){
//                            expr* n2 = to_app(c2)->get_arg(1);
//                            expr_ref_vector eqn2(m);
//                            collect_eq_nodes(n2, eqn2);
//                            for (const auto& nn2 : eqn2)
//                                if (u.str.is_concat(nn2)){
//                                    ptr_vector<expr> elements_nn2;
//                                    get_nodes_in_concat(nn2, elements_nn2);
//                                    if (elements_nn2.size() == 2 &&
//                                        are_equal_exprs(elements_nn1[0], elements_nn2[0])){
//                                        expr* tmp = createEqualOperator(n1, n2);
//                                        ctx.force_phase(ctx.get_literal(tmp));
//                                        TRACE("str", tout << __LINE__ << "  tryout eq " << __FUNCTION__ << ": "<< mk_pp(tmp, m) << std::endl;);
//                                    }
//                                }
//                        }
//                    }
//                }
//        }

        special_assertion_for_contain_vs_substr(lhs, rhs);
        special_assertion_for_contain_vs_substr(rhs, lhs);
    }

    bool theory_str::new_eq_check_wrt_disequalities(expr* n, expr_ref_vector premises, zstring containKey, expr_ref conclusion){
        ast_manager & m = get_manager();
        TRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": "<< mk_pp(n, m) << std::endl;);

        expr_ref_vector eqs(m);
        collect_eq_nodes(n, eqs);
        for (expr_ref_vector::iterator itor = eqs.begin(); itor != eqs.end(); itor++) {
            for (const auto& nn : m_wi_expr_memo) {
                expr* key;
                if (*itor == nn.second.get() && is_contain_equality(nn.first.get(), key)){ // itor not contain key
                    zstring keyStr;
                    if (u.str.is_string(key, keyStr) && containKey.contains(keyStr)){ // containKey contains key
                        expr* ineq = mk_not(m, createEqualOperator(nn.first.get(), nn.second.get()));
                        premises.push_back(ineq);
                        if (*itor != n)
                            premises.push_back(createEqualOperator(n, *itor));

                        assert_implication(createAndOperator(premises), conclusion.get());

                        return false;
                    }
                }
                else if (*itor == nn.first.get() && is_contain_equality(nn.second.get(), key)){
                    zstring keyStr;
                    if (u.str.is_string(key, keyStr) && containKey.contains(keyStr)){
                        expr* ineq = mk_not(m, createEqualOperator(nn.first.get(), nn.second.get()));
                        premises.push_back(ineq);
                        if (*itor != n)
                            premises.push_back(createEqualOperator(n, *itor));

                        assert_implication(createAndOperator(premises), conclusion.get());

                        return false;
                    }
                }
            }

            // upward propagation
            for (const auto & it : concat_astNode_map)
                if (!eqs.contains(it.get_value())){ // this to break the case: "" . x = x
                    expr *ts0 = it.get_key1();
                    expr *ts1 = it.get_key2();


                    // propagate
                    if (ts0 == *itor || ts1 == *itor) {
                        if (*itor != n)
                            premises.push_back(createEqualOperator(n, *itor));
                        // check if it is feasible or not
                        if (!new_eq_check_wrt_disequalities(it.get_value(), premises, containKey, conclusion))
                            return false;

                        if (*itor != n)
                            premises.pop_back();
                    }
                }
        }
        return true;
    }

    void theory_str::special_assertion_for_contain_vs_substr(expr* lhs, expr* rhs){
        ast_manager & m = get_manager();
        // (str.++ replace1!tmp0 (str.++ "A" replace2!tmp1)) == (str.substr url 0 (+ 1 (str.indexof url "A" 0)))
        expr* contain = nullptr;
        if (is_contain_equality(lhs, contain)) {
            if (u.str.is_extract(rhs)) {
                expr* arg1 = to_app(rhs)->get_arg(1);
                expr* arg2 = to_app(rhs)->get_arg(2);
                rational value;
                if (m_autil.is_numeral(arg1, value) && value.get_int64() == 0) {
                    // check 3rd arg
                    if (u.str.is_index(arg2)) {
                        app* indexApp = to_app(arg2);
                        expr* arg1_index = indexApp->get_arg(1);
                        expr* arg2_index = indexApp->get_arg(2);
                        if (arg1_index == contain && arg2_index == arg1){
                            assert_axiom(mk_not(m, createEqualOperator(lhs, rhs)));
                        }
                    }
                    else {
                        for (int i = 0; i < to_app(arg2)->get_num_args(); ++i)
                            if (u.str.is_index(to_app(arg2)->get_arg(i))){
                                app* indexApp = to_app(to_app(arg2)->get_arg(i));
                                expr* arg1_index = indexApp->get_arg(1);
                                expr* arg2_index = indexApp->get_arg(2);
                                if (arg1_index == contain && arg2_index == arg1) {
                                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " end of " << mk_pp(lhs, m) << " = " << mk_pp(rhs, m) << std::endl;);
                                    // same containKey, same pos
                                    // get all str in lhs, take the last one
                                    ptr_vector<expr> exprVector;
                                    get_nodes_in_concat(lhs, exprVector);
                                    SASSERT(exprVector.size() == 3);

                                    // len3rd = arg2 - index - 1
                                    expr* len3rd = createMinusOperator(arg2, createAddOperator(to_app(arg2)->get_arg(i), mk_int(1)));
                                    expr* cause = createEqualOperator(lhs, rhs);
                                    assert_implication(cause, createEqualOperator(mk_strlen(exprVector[2]), len3rd));
                                    return;
                                }
                            }
                    }
                }
            }
        }
    }

    expr_ref_vector theory_str::collect_all_empty_start(expr* lhs, expr* rhs){
        ast_manager & m = get_manager();
        expr_ref_vector ret(m);
        expr_ref_vector eqLhs(m);
        collect_eq_nodes(lhs, eqLhs);

        expr_ref_vector eqRhs(m);
        collect_eq_nodes(rhs, eqRhs);

        // combine two lists
        eqLhs.append(eqRhs);

        // collect all zero starts
        for (const auto& e : eqLhs){
            ptr_vector<expr> v;
            get_nodes_in_concat(e, v);
            for (int i = 0; i < v.size(); ++i){
                rational len;
                if (get_len_value(v[i], len)){
                    if (len.get_int64() == 0){
                        ret.push_back(createEqualOperator(mk_strlen(v[i]), mk_int(0)));
                    }
                    else if (u.str.is_string(v[i]) && lhs != e){
                        ret.push_back(createEqualOperator(lhs, e));
                    }
                    else
                        break;
                }
                else break;
            }
        }

        if (ret.size() == 0){
            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " cannot find zero start"  << std::endl;);
            return negate_equality(lhs, rhs);
        }

        for (const auto& e : ret){
            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(e, m) << std::endl;);
        }
        return ret;
    }

    expr_ref_vector theory_str::collect_all_empty_end(expr* lhs, expr* rhs){
        ast_manager & m = get_manager();
        expr_ref_vector ret(m);
        expr_ref_vector eqLhs(m);
        collect_eq_nodes(lhs, eqLhs);

        expr_ref_vector eqRhs(m);
        collect_eq_nodes(rhs, eqRhs);

        // combine two lists
        eqLhs.append(eqRhs);

        // collect all zero ends
        for (const auto& e : eqLhs){
            ptr_vector<expr> v;
            get_nodes_in_concat(e, v);
            for (int i = v.size() - 1; i >= 0; --i){
                rational len;
                if (get_len_value(v[i], len)){
                    if (len.get_int64() == 0){
                        ret.push_back(createEqualOperator(mk_strlen(v[i]), mk_int(0)));
                    }
                    else if (u.str.is_string(v[i]) && lhs != e){
                        ret.push_back(createEqualOperator(lhs, e));
                    }
                    else
                        break;
                }
                else break;
            }
        }

        if (ret.size() == 0){
            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " cannot find zero start"  << std::endl;);
            return negate_equality(lhs, rhs);
        }

        for (const auto& e : ret){
            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(e, m) << std::endl;);
        }
        return ret;
    }

    expr_ref_vector theory_str::negate_equality(expr* lhs, expr* rhs){
        ast_manager & m = get_manager();
        expr_ref_vector ret(m);
        expr_ref_vector eqLhs(m);
        collect_eq_nodes(lhs, eqLhs);

        expr_ref_vector eqRhs(m);
        collect_eq_nodes(rhs, eqRhs);

        for (int i = 0; i < eqLhs.size(); ++i)
            if (lhs != eqLhs[i].get())
                ret.push_back(createEqualOperator(lhs, eqLhs[i].get()));

        for (int i = 0; i < eqRhs.size(); ++i)
            if (rhs != eqRhs[i].get())
                ret.push_back(createEqualOperator(rhs, eqRhs[i].get()));

        ret.push_back(createEqualOperator(lhs, rhs));
        return ret;
    }

    bool theory_str::is_inconsisten(
            std::set<expr*> concat_lhs,
            std::set<expr*> concat_rhs,
            std::set<expr*> const_lhs,
            std::set<expr*> const_rhs,
            bool &wrongStart, bool &wrongEnd){
        wrongStart = false;
        wrongEnd = false;
        concat_lhs.insert(concat_rhs.begin(), concat_rhs.end());
        const_lhs.insert(const_rhs.begin(), const_rhs.end());

        // copy from const vectors
        std::vector<zstring> starts, ends;
        for (const auto& s: const_lhs){
            zstring value;
            u.str.is_string(s, value);
            starts.push_back(value);
        }
        ends = starts;

        // collect all starting, ending
        for (const auto& c : concat_lhs){
            ptr_vector<expr> exprVector;
            get_nodes_in_concat(c, exprVector);
            zstring value;
            if (u.str.is_string(exprVector[0], value)){
                starts.push_back(value);
            }

            if (u.str.is_string(exprVector[exprVector.size() - 1], value)){
                ends.push_back(value);
            }
        }

        // all issues

        // check all starts
        for (int i = 0; i < starts.size(); ++i)
            for (int j = i + 1; j < starts.size(); ++j)
                if (starts[j].prefixof(starts[i]) || starts[i].prefixof(starts[j])) {

                }
                else {
                    wrongStart = true;
                    break;
                }

        // check all starts
        for (int i = 0; i < ends.size(); ++i)
            for (int j = i + 1; j < ends.size(); ++j)
                if (ends[j].suffixof(ends[i]) || ends[i].suffixof(ends[j])) {

                }
                else {
                    wrongEnd = true;
                    break;
                }

        return wrongEnd || wrongStart;
    }

    /*
     * strArgmt::solve_concat_eq_str()
     * Solve concatenations of the form:
     *   const == Concat(const, X)
     *   const == Concat(X, const)
     */
    void theory_str::solve_concat_eq_str(expr * concat, expr * str) {
        ast_manager &m = get_manager();
        context &ctx = get_context();

        TRACE("str", tout << mk_ismt2_pp(concat, m) << " == " << mk_ismt2_pp(str, m) << std::endl;);

        zstring const_str;
        if (u.str.is_concat(to_app(concat)) && u.str.is_string(to_app(str), const_str)) {
            app *a_concat = to_app(concat);
            SASSERT(a_concat->get_num_args() == 2);
            expr *a1 = a_concat->get_arg(0);
            expr *a2 = a_concat->get_arg(1);

            if (const_str.empty()) {
                TRACE("str", tout << "quick path: concat == \"\"" << std::endl;);
                // assert the following axiom:
                // ( (Concat a1 a2) == "" ) -> ( (a1 == "") AND (a2 == "") )


                expr_ref premise(ctx.mk_eq_atom(concat, str), m);
                expr_ref c1(ctx.mk_eq_atom(a1, str), m);
                expr_ref c2(ctx.mk_eq_atom(a2, str), m);
                expr_ref conclusion(m.mk_and(c1, c2), m);
                assert_implication(premise, conclusion);

                return;
            }
            bool arg1_has_eqc_value = false;
            bool arg2_has_eqc_value = false;
            expr *arg1 = get_eqc_value(a1, arg1_has_eqc_value);
            expr *arg2 = get_eqc_value(a2, arg2_has_eqc_value);
            expr_ref newConcat(m);
            if (arg1 != a1 || arg2 != a2) {
                TRACE("str", tout << "resolved concat argument(s) to eqc string constants" << std::endl;);
                int iPos = 0;
                expr_ref_vector item1(m);
                if (a1 != arg1) {
                    item1.push_back(ctx.mk_eq_atom(a1, arg1));
                    iPos += 1;
                }
                if (a2 != arg2) {
                    item1.push_back(ctx.mk_eq_atom(a2, arg2));
                    iPos += 1;
                }
                expr_ref implyL1(mk_and(item1), m);
                newConcat = mk_concat(arg1, arg2);
                if (newConcat != str) {
                    expr_ref implyR1(ctx.mk_eq_atom(concat, newConcat), m);
                    assert_implication(implyL1, implyR1);
                }
            } else {
                newConcat = concat;
            }
            if (newConcat == str) {
                return;
            }
            if (!u.str.is_concat(to_app(newConcat))) {
                return;
            }
            if (arg1_has_eqc_value && arg2_has_eqc_value) {
                // Case 1: Concat(const, const) == const
                TRACE("str", tout << "Case 1: Concat(const, const) == const" << std::endl;);
                zstring arg1_str, arg2_str;
                u.str.is_string(arg1, arg1_str);
                u.str.is_string(arg2, arg2_str);

                zstring result_str = arg1_str + arg2_str;
                if (result_str != const_str) {
                    // Inconsistency
                    TRACE("str", tout << "inconsistency detected: \""
                                      << arg1_str << "\" + \"" << arg2_str <<
                                      "\" != \"" << const_str << "\"" << "\n";);
                    expr_ref equality(ctx.mk_eq_atom(concat, str), m);
                    expr_ref diseq(mk_not(m, equality), m);
                    assert_axiom(diseq);
                    return;
                }
            } else if (!arg1_has_eqc_value && arg2_has_eqc_value) {
                // Case 2: Concat(var, const) == const
                TRACE("str", tout << "Case 2: Concat(var, const) == const" << std::endl;);
                zstring arg2_str;
                u.str.is_string(arg2, arg2_str);
                unsigned int resultStrLen = const_str.length();
                unsigned int arg2StrLen = arg2_str.length();
                if (resultStrLen < arg2StrLen) {
                    // Inconsistency
                    TRACE("str", tout << "inconsistency detected: \""
                                      << arg2_str <<
                                      "\" is longer than \"" << const_str << "\","
                                      << " so cannot be concatenated with anything to form it" << "\n";);
                    expr_ref equality(ctx.mk_eq_atom(newConcat, str), m);
                    expr_ref diseq(mk_not(m, equality), m);
                    assert_axiom(diseq);
                    return;
                } else {
                    int varStrLen = resultStrLen - arg2StrLen;
                    zstring firstPart = const_str.extract(0, varStrLen);
                    zstring secondPart = const_str.extract(varStrLen, arg2StrLen);
                    if (arg2_str != secondPart) {
                        // Inconsistency
                        TRACE("str", tout << "inconsistency detected: "
                                          << "suffix of concatenation result expected \"" << secondPart << "\", "
                                          << "actually \"" << arg2_str << "\""
                                          << "\n";);
                        expr_ref equality(ctx.mk_eq_atom(newConcat, str), m);
                        expr_ref diseq(mk_not(m, equality), m);
                        assert_axiom(diseq);
                        return;
                    } else {
                        expr_ref tmpStrConst(mk_string(firstPart), m);
                        expr_ref premise(ctx.mk_eq_atom(newConcat, str), m);
                        expr_ref conclusion(ctx.mk_eq_atom(arg1, tmpStrConst), m);
                        assert_implication(premise, conclusion);
                        return;
                    }
                }
            } else if (arg1_has_eqc_value && !arg2_has_eqc_value) {
                // Case 3: Concat(const, var) == const
                TRACE("str", tout << "Case 3: Concat(const, var) == const" << std::endl;);
                zstring arg1_str;
                u.str.is_string(arg1, arg1_str);
                unsigned int resultStrLen = const_str.length();
                unsigned int arg1StrLen = arg1_str.length();
                if (resultStrLen < arg1StrLen) {
                    // Inconsistency
                    TRACE("str", tout << "inconsistency detected: \""
                                      << arg1_str <<
                                      "\" is longer than \"" << const_str << "\","
                                      << " so cannot be concatenated with anything to form it" << "\n";);
                    expr_ref equality(ctx.mk_eq_atom(newConcat, str), m);
                    expr_ref diseq(m.mk_not(equality), m);
                    assert_axiom(diseq);
                    return;
                } else {
                    int varStrLen = resultStrLen - arg1StrLen;
                    zstring firstPart = const_str.extract(0, arg1StrLen);
                    zstring secondPart = const_str.extract(arg1StrLen, varStrLen);
                    if (arg1_str != firstPart) {
                        // Inconsistency
                        TRACE("str", tout << "inconsistency detected: "
                                          << "prefix of concatenation result expected \"" << secondPart << "\", "
                                          << "actually \"" << arg1_str << "\""
                                          << "\n";);
                        expr_ref equality(ctx.mk_eq_atom(newConcat, str), m);
                        expr_ref diseq(m.mk_not(equality), m);
                        assert_axiom(diseq);
                        return;
                    } else {
                        expr_ref tmpStrConst(mk_string(secondPart), m);
                        expr_ref premise(ctx.mk_eq_atom(newConcat, str), m);
                        expr_ref conclusion(ctx.mk_eq_atom(arg2, tmpStrConst), m);
                        assert_implication(premise, conclusion);
                        return;
                    }
                }
            } else {
                // Case 4: Concat(var, var) == const
                TRACE("str", tout << "Case 4: Concat(var, var) == const" << std::endl;);
                if (eval_concat(arg1, arg2) == nullptr) {
                    rational arg1Len, arg2Len;
                    bool arg1Len_exists = get_len_value(arg1, arg1Len);
                    bool arg2Len_exists = get_len_value(arg2, arg2Len);
                    rational concatStrLen((unsigned) const_str.length());
                    if (arg1Len_exists || arg2Len_exists) {
                        expr_ref ax_l1(ctx.mk_eq_atom(concat, str), m);
                        expr_ref ax_l2(m);
                        zstring prefixStr, suffixStr;
                        if (arg1Len_exists) {
                            if (arg1Len.is_neg()) {
                                TRACE("str", tout << "length conflict: arg1Len = " << arg1Len << ", concatStrLen = "
                                                  << concatStrLen << std::endl;);
                                expr_ref toAssert(m_autil.mk_ge(mk_strlen(arg1), mk_int(0)), m);
                                assert_axiom(toAssert);
                                return;
                            } else if (arg1Len > concatStrLen) {
                                TRACE("str", tout << "length conflict: arg1Len = " << arg1Len << ", concatStrLen = "
                                                  << concatStrLen << std::endl;);
                                expr_ref ax_r1(m_autil.mk_le(mk_strlen(arg1), mk_int(concatStrLen)), m);
                                assert_implication(ax_l1, ax_r1);
                                return;
                            }

                            prefixStr = const_str.extract(0, arg1Len.get_unsigned());
                            rational concat_minus_arg1 = concatStrLen - arg1Len;
                            suffixStr = const_str.extract(arg1Len.get_unsigned(), concat_minus_arg1.get_unsigned());
                            ax_l2 = ctx.mk_eq_atom(mk_strlen(arg1), mk_int(arg1Len));
                        } else {
                            // arg2's length is available
                            if (arg2Len.is_neg()) {
                                TRACE("str", tout << "length conflict: arg2Len = " << arg2Len << ", concatStrLen = "
                                                  << concatStrLen << std::endl;);
                                expr_ref toAssert(m_autil.mk_ge(mk_strlen(arg2), mk_int(0)), m);
                                assert_axiom(toAssert);
                                return;
                            } else if (arg2Len > concatStrLen) {
                                TRACE("str", tout << "length conflict: arg2Len = " << arg2Len << ", concatStrLen = "
                                                  << concatStrLen << std::endl;);
                                expr_ref ax_r1(m_autil.mk_le(mk_strlen(arg2), mk_int(concatStrLen)), m);
                                assert_implication(ax_l1, ax_r1);
                                return;
                            }

                            rational concat_minus_arg2 = concatStrLen - arg2Len;
                            prefixStr = const_str.extract(0, concat_minus_arg2.get_unsigned());
                            suffixStr = const_str.extract(concat_minus_arg2.get_unsigned(), arg2Len.get_unsigned());
                            ax_l2 = ctx.mk_eq_atom(mk_strlen(arg2), mk_int(arg2Len));
                        }
                        // consistency check
                        if (u.str.is_concat(to_app(arg1)) && !can_concat_eq_str(arg1, prefixStr)) {
                            expr_ref ax_r(m.mk_not(ax_l2), m);
                            assert_implication(ax_l1, ax_r);
                            return;
                        }
                        if (u.str.is_concat(to_app(arg2)) && !can_concat_eq_str(arg2, suffixStr)) {
                            expr_ref ax_r(m.mk_not(ax_l2), m);
                            assert_implication(ax_l1, ax_r);
                            return;
                        }

                        expr_ref_vector r_items(m);
                        r_items.push_back(ctx.mk_eq_atom(arg1, mk_string(prefixStr)));
                        r_items.push_back(ctx.mk_eq_atom(arg2, mk_string(suffixStr)));
                        if (!arg1Len_exists) {
                            r_items.push_back(ctx.mk_eq_atom(mk_strlen(arg1), mk_int(prefixStr.length())));
                        }
                        if (!arg2Len_exists) {
                            r_items.push_back(ctx.mk_eq_atom(mk_strlen(arg2), mk_int(suffixStr.length())));
                        }
                        expr_ref lhs(m.mk_and(ax_l1, ax_l2), m);
                        expr_ref rhs(mk_and(r_items), m);
                        assert_implication(lhs, rhs);


                    } else {
                    } /* (arg1Len != 1 || arg2Len != 1) */
                } /* if (Concat(arg1, arg2) == NULL) */
            }
        }
    }

    // previously Concat() in strTheory.cpp
    // Evaluates the concatenation (n1 . n2) with respect to
    // the current equivalence classes of n1 and n2.
    // Returns a constant string expression representing this concatenation
    // if one can be determined, or NULL if this is not possible.
    expr * theory_str::eval_concat(expr * n1, expr * n2) {
        bool n1HasEqcValue = false;
        bool n2HasEqcValue = false;
        expr * v1 = get_eqc_value(n1, n1HasEqcValue);
        expr * v2 = get_eqc_value(n2, n2HasEqcValue);
        if (n1HasEqcValue && n2HasEqcValue) {
            zstring n1_str, n2_str;
            u.str.is_string(v1, n1_str);
            u.str.is_string(v2, n2_str);
            zstring result = n1_str + n2_str;
            return mk_string(result);
        } else if (n1HasEqcValue && !n2HasEqcValue) {
            zstring v1_str;
            u.str.is_string(v1, v1_str);
            if (v1_str.empty()) {
                return n2;
            }
        } else if (n2HasEqcValue && !n1HasEqcValue) {
            zstring v2_str;
            u.str.is_string(v2, v2_str);
            if (v2_str.empty()) {
                return n1;
            }
        }
        // give up
        return nullptr;
    }

    void theory_str::group_terms_by_eqc(expr * n, std::set<expr*> & concats, std::set<expr*> & vars, std::set<expr*> & consts) {
        expr * eqcNode = n;
        do {
            app * ast = to_app(eqcNode);
            if (u.str.is_concat(ast)) {
                expr * simConcat = simplify_concat(ast);
                if (simConcat != ast) {
                    if (u.str.is_concat(to_app(simConcat))) {
                        concats.insert(simConcat);
                    } else {
                        if (u.str.is_string(simConcat)) {
                            consts.insert(simConcat);
                        } else {
                            vars.insert(simConcat);
                        }
                    }
                } else {
                    concats.insert(simConcat);
                }
            } else if (u.str.is_string(ast)) {
                consts.insert(ast);
            } else {
                vars.insert(ast);
            }
            eqcNode = get_eqc_next(eqcNode);
        } while (eqcNode != n);
    }

    /*
     * Create a new constraint where all variables are replaced by their values if possible
     * */
    expr * theory_str::simplify_concat(expr * node) {
        ast_manager & m = get_manager();
        context & ctx = get_context();
        std::map<expr*, expr*> resolvedMap;
        ptr_vector<expr> argVec;
        get_nodes_in_concat(node, argVec);

        for (unsigned i = 0; i < argVec.size(); ++i) {
            bool vArgHasEqcValue = false;
            expr * vArg = get_eqc_value(argVec[i], vArgHasEqcValue);
            if (vArg != argVec[i]) {
                resolvedMap[argVec[i]] = vArg;
            }
        }

        if (resolvedMap.size() == 0) {
            // no simplification possible
            return node;
        } else {
            expr * resultAst = mk_string("");
            for (int i = argVec.size() - 1; i >= 0; --i) {
                bool vArgHasEqcValue = false;
                expr * vArg = get_eqc_value(argVec[i], vArgHasEqcValue);
                resultAst = mk_concat(vArg, resultAst);
            }

            if (in_same_eqc(node, resultAst)) {
            } else if (u.str.is_string(resultAst)){
                expr_ref_vector items(m);
                int pos = 0;
                for (auto itor : resolvedMap) {
                    items.push_back(ctx.mk_eq_atom(itor.first, itor.second));
                    pos += 1;
                }
                expr_ref premise(mk_and(items), m);
                expr_ref conclusion(ctx.mk_eq_atom(node, resultAst), m);
                assert_implication(premise, conclusion);
            }
            return resultAst;
        }

    }

    /*
     * Add an axiom of the form:
     * (lhs == rhs) -> ( Length(lhs) == Length(rhs) )
     */
    void theory_str::instantiate_str_eq_length_axiom(enode * lhs, enode * rhs) {
        context & ctx = get_context();
        ast_manager & m = get_manager();

        app * a_lhs = lhs->get_owner();
        app * a_rhs = rhs->get_owner();

        // build premise: (lhs == rhs)
        expr_ref premise(ctx.mk_eq_atom(a_lhs, a_rhs), m);

        // build conclusion: ( Length(lhs) == Length(rhs) )
        zstring lhsValue, rhsValue;
        expr_ref len_lhs(mk_strlen(a_lhs), m);
        if (u.str.is_string(a_lhs, lhsValue)) {
            len_lhs = m_autil.mk_int(lhsValue.length());
        }
        SASSERT(len_lhs);
        expr_ref len_rhs(mk_strlen(a_rhs), m);
        if (u.str.is_string(a_rhs, rhsValue)) {
            len_rhs = m_autil.mk_int(rhsValue.length());
        }
        SASSERT(len_rhs);
        expr_ref conclusion(ctx.mk_eq_atom(len_lhs, len_rhs), m);

        expr* empty = mk_string("");
        if (a_lhs == empty || a_rhs == empty)
            assert_axiom(createEqualOperator(premise.get(), conclusion.get()));
        else
            assert_implication(premise, conclusion);
    };

    /*
     * Check that a string's length can be 0 iff it is the empty string.
     */
    void theory_str::check_eqc_empty_string(expr * lhs, expr * rhs) {
        context & ctx = get_context();
        ast_manager & m = get_manager();

        rational nn1Len, nn2Len;
        bool nn1Len_exists = get_len_value(lhs, nn1Len);
        bool nn2Len_exists = get_len_value(rhs, nn2Len);
        expr_ref emptyStr(mk_string(""), m);

        if (nn1Len_exists && nn1Len.is_zero()) {
            if (!in_same_eqc(lhs, emptyStr) && rhs != emptyStr) {
                expr_ref eql(ctx.mk_eq_atom(mk_strlen(lhs), mk_int(0)), m);
                expr_ref eqr(ctx.mk_eq_atom(lhs, emptyStr), m);
                expr_ref toAssert(ctx.mk_eq_atom(eql, eqr), m);
                assert_axiom(toAssert);
            }
        }

        if (nn2Len_exists && nn2Len.is_zero()) {
            if (!in_same_eqc(rhs, emptyStr) && lhs != emptyStr) {
                expr_ref eql(ctx.mk_eq_atom(mk_strlen(rhs), mk_int(0)), m);
                expr_ref eqr(ctx.mk_eq_atom(rhs, emptyStr), m);
                expr_ref toAssert(ctx.mk_eq_atom(eql, eqr), m);
                assert_axiom(toAssert);
            }
        }
    }

    /*
     * Check whether n1 and n2 could be equal.
     * Returns true if n1 could equal n2 (maybe),
     * and false if n1 is definitely not equal to n2 (no).
     */
    bool theory_str:: can_two_nodes_eq(expr * n1, expr * n2) {
        app * n1_curr = to_app(n1);
        app * n2_curr = to_app(n2);

        // case 0: n1_curr is const string, n2_curr is const string
        zstring n1_curr_str, n2_curr_str;
        if (u.str.is_string(n1_curr, n1_curr_str) && u.str.is_string(n2_curr, n2_curr_str)) {
            TRACE("str", tout << "checking string constants: n1=" << n1_curr_str << ", n2=" << n2_curr_str << std::endl;);
            if (n1_curr_str == n2_curr_str) {
                return true;
            } else {
                return false;
            }
        }

        // case 1: n1_curr is concat, n2_curr is const string
        /*
         * Check if str has the same prefix, suffix and contains const strings which appear in concat
         */
        else if (u.str.is_concat(n1_curr) && u.str.is_string(n2_curr)) {
            zstring n2_curr_str;
            u.str.is_string(n2_curr, n2_curr_str);
            if (!can_concat_eq_str(n1_curr, n2_curr_str)) {
                return false;
            }
        }

        // case 2: n2_curr is concat, n1_curr is const string
        /*
         * Check if str has the same prefix, suffix and contains const strings which appear in concat
         */
        else if (u.str.is_concat(n2_curr) && u.str.is_string(n1_curr)) {
            zstring n1_curr_str;
            u.str.is_string(n1_curr, n1_curr_str);
            if (!can_concat_eq_str(n2_curr, n1_curr_str)) {
                return false;
            }
        }

        // case 3: both are concats
        /*
         * Suppose concat1 = (Concat X Y) and concat2 = (Concat M N).
         *      if both X and M are constant strings, check whether they have the same prefix
         *      if both Y and N are constant strings, check whether they have the same suffix
         */
        else if (u.str.is_concat(n1_curr) && u.str.is_concat(n2_curr)) {
            if (!can_concat_eq_concat(n1_curr, n2_curr)) {
                return false;
            }
        }

        return true;
    }

    /*
     * Check if str has the same prefix, suffix and contains const strings which appear in concat
     */
    bool theory_str::can_concat_eq_str(expr * concat, zstring& str) {
        unsigned int strLen = str.length();
        if (u.str.is_concat(to_app(concat))) {
            ptr_vector<expr> args;
            get_nodes_in_concat(concat, args);
            expr * ml_node = args[0];
            expr * mr_node = args[args.size() - 1];

            zstring ml_str;
            if (u.str.is_string(ml_node, ml_str)) {
                unsigned int ml_len = ml_str.length();
                if (ml_len > strLen) {
                    return false;
                }
                unsigned int cLen = ml_len;
                if (ml_str != str.extract(0, cLen)) {
                    return false;
                }
            }

            zstring mr_str;
            if (u.str.is_string(mr_node, mr_str)) {
                unsigned int mr_len = mr_str.length();
                if (mr_len > strLen) {
                    return false;
                }
                unsigned int cLen = mr_len;
                if (mr_str != str.extract(strLen - cLen, cLen)) {
                    return false;
                }
            }

            unsigned int sumLen = 0;
            for (unsigned int i = 0 ; i < args.size() ; i++) {
                expr * oneArg = args[i];
                zstring arg_str;
                if (u.str.is_string(oneArg, arg_str)) {
                    if (!str.contains(arg_str)) {
                        return false;
                    }
                    sumLen += arg_str.length();
                }
            }

            if (sumLen > strLen) {
                return false;
            }
        }
        return true;
    }

    /*
     * Suppose concat1 = (Concat X Y) and concat2 = (Concat M N).
     *      if both X and M are constant strings, check whether they have the same prefix
     *      if both Y and N are constant strings, check whether they have the same suffix
     */
    bool theory_str::can_concat_eq_concat(expr * concat1, expr * concat2) {
        if (u.str.is_concat(to_app(concat1)) && u.str.is_concat(to_app(concat2))) {
            {
                // Suppose concat1 = (Concat X Y) and concat2 = (Concat M N).
                expr * concat1_mostL = getMostLeftNodeInConcat(concat1);
                expr * concat2_mostL = getMostLeftNodeInConcat(concat2);
                // if both X and M are constant strings, check whether they have the same prefix
                zstring concat1_mostL_str, concat2_mostL_str;
                if (u.str.is_string(concat1_mostL, concat1_mostL_str) && u.str.is_string(concat2_mostL, concat2_mostL_str)) {
                    unsigned int cLen = std::min(concat1_mostL_str.length(), concat2_mostL_str.length());
                    if (concat1_mostL_str.extract(0, cLen) != concat2_mostL_str.extract(0, cLen)) {
                        return false;
                    }
                }
            }

            {
                // Similarly, if both Y and N are constant strings, check whether they have the same suffix
                expr * concat1_mostR = getMostRightNodeInConcat(concat1);
                expr * concat2_mostR = getMostRightNodeInConcat(concat2);
                zstring concat1_mostR_str, concat2_mostR_str;
                if (u.str.is_string(concat1_mostR, concat1_mostR_str) && u.str.is_string(concat2_mostR, concat2_mostR_str)) {
                    unsigned int cLen = std::min(concat1_mostR_str.length(), concat2_mostR_str.length());
                    if (concat1_mostR_str.extract(concat1_mostR_str.length() - cLen, cLen) !=
                        concat2_mostR_str.extract(concat2_mostR_str.length() - cLen, cLen)) {
                        return false;
                    }
                }
            }
        }
        return true;
    }

    inline expr * theory_str::getMostLeftNodeInConcat(expr * node) {
        app * aNode = to_app(node);
        if (!u.str.is_concat(aNode)) {
            return node;
        } else {
            expr * concatArgL = aNode->get_arg(0);
            return getMostLeftNodeInConcat(concatArgL);
        }
    }

    inline expr * theory_str::getMostRightNodeInConcat(expr * node) {
        app * aNode = to_app(node);
        if (!u.str.is_concat(aNode)) {
            return node;
        } else {
            expr * concatArgR = aNode->get_arg(1);
            return getMostRightNodeInConcat(concatArgR);
        }
    }

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
    bool theory_str::new_eq_check(expr * lhs, expr * rhs) {
        clock_t t = clock();
        context & ctx = get_context();
        ast_manager & m = get_manager();
        TRACE("str", tout << __FUNCTION__ << ": " << mk_ismt2_pp(lhs, m) << " == " << mk_ismt2_pp(rhs, m) << std::endl;);

        // Now we iterate over all pairs of terms across both EQCs
        // and check whether we can show that any pair of distinct terms
        // cannot possibly be equal.
        // If that's the case, we assert an axiom to that effect and stop.

        expr * eqc_nn1 = lhs;
        do {
            expr * eqc_nn2 = rhs;
            do {
                // inconsistency check: value
                if (!can_two_nodes_eq(eqc_nn1, eqc_nn2)) {
                    STRACE("str", tout << "inconsistency detected: " << mk_pp(eqc_nn1, m) << " cannot be equal to " << mk_pp(eqc_nn2, m) << std::endl;);
                    expr_ref to_assert(mk_not(m, ctx.mk_eq_atom(eqc_nn1, eqc_nn2)), m);

                    expr_ref_vector litems(m);
                    if (lhs != eqc_nn1)
                        litems.push_back(ctx.mk_eq_atom(lhs, eqc_nn1));
                    if (rhs != eqc_nn2)
                        litems.push_back(ctx.mk_eq_atom(rhs, eqc_nn2));

                    litems.push_back(collect_empty_node_in_concat(lhs));
                    litems.push_back(collect_empty_node_in_concat(rhs));
                    expr_ref implyL(mk_and(litems), m);
                    assert_implication(implyL, mk_not(m, ctx.mk_eq_atom(lhs, rhs)));
                    // this shouldn't use the integer theory at all, so we don't allow the option of quick-return
                    return false;
                }
                eqc_nn2 = get_eqc_next(eqc_nn2);
            } while (eqc_nn2 != rhs);
            eqc_nn1 = get_eqc_next(eqc_nn1);
        } while (eqc_nn1 != lhs);

        if (!contains_map.empty()) {
            propagate_contain_in_new_eq(lhs, rhs);
        }

        if (!regex_in_bool_map.empty()) {
            check_regex_in(lhs, rhs);
        }

        zstring str;
        if (u.str.is_string(lhs, str)) {
            if (str.length() > 0)
                propagate_const_str(lhs, rhs, str);
        }
        else if (u.str.is_string(rhs, str)) {
            if (str.length() > 0)
                propagate_const_str(rhs, lhs, str);
        }
        // okay, all checks here passed
        STRACE("str", tout << __LINE__ <<  " time: " << __FUNCTION__ << ":  " << ((float)(clock() - t))/CLOCKS_PER_SEC << std::endl;);
        return true;
    }

    expr* theory_str::collect_empty_node_in_concat(expr* n){
        ptr_vector <expr> nodes;
        get_nodes_in_concat(n, nodes);
        rational ra;
        expr_ref_vector ands(get_manager());
        for (const auto& nn : nodes) {
            if (get_len_value(nn, ra) && ra.get_int64() == 0){
                ands.push_back(createEqualOperator(mk_strlen(nn), mk_int(0)));
            }
        }

        return createAndOperator(ands);
    }

    void theory_str::propagate_const_str(expr * lhs, expr * rhs, zstring value){
        context & ctx = get_context();
        ast_manager & m = get_manager();

        TRACE("str", tout << __FUNCTION__ << ": "<< mk_pp(lhs, m) << " = " << mk_pp(rhs, m) << std::endl;);

        expr_ref_vector eqRhsList(m);
        collect_eq_nodes(rhs, eqRhsList);

        for (const auto & it : concat_astNode_map){
            expr* ts0 = it.get_key1();
            expr* ts1 = it.get_key2();
            expr* concat = it.get_value();

           if (eqRhsList.contains(ts0)){
               // x . y where x is const, then: lhs = rhs ==> concat = const
               TRACE("str", tout << __FUNCTION__ << ": "<< mk_pp(concat, m) << std::endl;);
               zstring value01;
               // if y is const also
               if (u.str.is_string(ts1, value01)) {
                   // list of constraints
                   expr_ref_vector litems(m);
                   litems.push_back(ctx.mk_eq_atom(lhs, rhs));
                   if (rhs != ts0)
                       litems.push_back(ctx.mk_eq_atom(rhs, ts0));

                   expr * sumValue = u.str.mk_string(value + value01);
                   m_trail.push_back(sumValue);

                   expr_ref implyL(mk_and(litems), m);
                   assert_implication(implyL, ctx.mk_eq_atom(concat, sumValue));

                   // TODO continue propagation?
               }

               // if y is equal to a const, then: lhs = rhs && y = const ==> concat = const
               else {
                   expr_ref_vector tmpEqNodeSet(m);
                   expr *childValue = collect_eq_nodes(ts1, tmpEqNodeSet);
                   if (childValue != nullptr) {
                       expr_ref_vector litems(m);

                       litems.push_back(ctx.mk_eq_atom(lhs, rhs));
                       if (rhs != ts0)
                           litems.push_back(ctx.mk_eq_atom(rhs, ts0));
                       litems.push_back(ctx.mk_eq_atom(ts1, childValue));

                       zstring str;
                       u.str.is_string(childValue, str);
                       expr * sumValue = u.str.mk_string(value + str);
                       m_trail.push_back(sumValue);
                       expr_ref implyL(mk_and(litems), m);
                       assert_implication(implyL, ctx.mk_eq_atom(concat, sumValue));

                       // TODO continue propagation?
                   }

                   // if y is not either const or equal to a const, then if concat = var \in regex ==> check the feasibility
                   else {
                       expr_ref_vector litems(m);
                       litems.push_back(ctx.mk_eq_atom(lhs, rhs));
                       if (rhs != ts0)
                           litems.push_back(ctx.mk_eq_atom(rhs, ts0));
                        expr * new_concat = u.str.mk_concat(lhs, ts1);
                       m_trail.push_back(new_concat);

                       // check if it is feasible or not
                       propagate_non_const(litems, concat, new_concat);
                   }
               }
           }

            if (eqRhsList.contains(ts1)){
                // x . y where x is const, then: lhs = rhs ==> concat = const
                TRACE("str", tout << __FUNCTION__ << ": "<< mk_pp(concat, m) << std::endl;);
                zstring value01;
                // if y is const also
                if (u.str.is_string(ts0, value01)) {
                    // list of constraints
                    expr_ref_vector litems(m);
                    litems.push_back(ctx.mk_eq_atom(lhs, rhs));
                    if (rhs != ts1)
                        litems.push_back(ctx.mk_eq_atom(rhs, ts1));

                    expr * sumValue = u.str.mk_string(value01 + value);
                    m_trail.push_back(sumValue);

                    expr_ref implyL(mk_and(litems), m);
                    assert_implication(implyL, ctx.mk_eq_atom(concat, sumValue));

                    // TODO continue propagation?
                }

                // if y is equal to a const, then: lhs = rhs && y = const ==> concat = const
                else {
                    expr_ref_vector tmpEqNodeSet(m);
                    expr *childValue = collect_eq_nodes(ts0, tmpEqNodeSet);
                    if (childValue != nullptr) {
                        expr_ref_vector litems(m);

                        litems.push_back(ctx.mk_eq_atom(lhs, rhs));
                        if (rhs != ts1)
                            litems.push_back(ctx.mk_eq_atom(rhs, ts1));
                        litems.push_back(ctx.mk_eq_atom(ts1, childValue));

                        zstring str;
                        u.str.is_string(childValue, str);
                        expr * sumValue = u.str.mk_string(str + value);
                        m_trail.push_back(sumValue);
                        expr_ref implyL(mk_and(litems), m);
                        assert_implication(implyL, ctx.mk_eq_atom(concat, sumValue));

                        // TODO continue propagation?
                    }

                    // if y is not either const or equal to a const, then if concat = var \in regex ==> check the feasibility
                    else {
                        expr_ref_vector litems(m);
                        litems.push_back(ctx.mk_eq_atom(lhs, rhs));
                        if (rhs != ts1)
                            litems.push_back(ctx.mk_eq_atom(rhs, ts1));
                        expr * new_concat = u.str.mk_concat(ts0, lhs);
                        m_trail.push_back(new_concat);

                        // check if it is feasible or not
                        propagate_non_const(litems, concat, new_concat);
                    }
                }
            }
        }
    }

    void theory_str::propagate_non_const(expr_ref_vector litems, expr * concat, expr* new_concat){
        context & ctx = get_context();
        ast_manager & m = get_manager();
        TRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": "<< mk_pp(concat, m) << " --- " << mk_pp(new_concat, m) << std::endl;);

        expr_ref_vector eqConcatList(m);
        expr *value = collect_eq_nodes(concat, eqConcatList);
        if (value != nullptr){
            // get the value
            zstring sumValue;
            u.str.is_string(value, sumValue);

            app* appConcat = to_app(new_concat);
            expr* ts00 = appConcat->get_arg(0);
            expr* ts01 = appConcat->get_arg(1);

            zstring ts0Value;
            zstring ts1Value;
            if (u.str.is_string(ts00, ts0Value)){
                zstring verifingValue = sumValue.extract(0, ts0Value.length());
                if (verifingValue == ts0Value) {
                    ts1Value = sumValue.extract(ts0Value.length(), sumValue.length() - ts0Value.length());
                    litems.push_back(ctx.mk_eq_atom(concat, value));
                    expr *ts1exprValue = u.str.mk_string(ts1Value);
                    m_trail.push_back(ts1exprValue);

                    expr_ref implyL(mk_and(litems), m);
                    assert_implication(implyL, ctx.mk_eq_atom(ts01, ts1exprValue));
                }
                else {
                    expr* conclusion = mk_not(m, createEqualOperator(concat, value));
                    expr_ref implyL(mk_and(litems), m);
                    assert_implication(implyL, conclusion);
                }
            }

            else if (u.str.is_string(ts01, ts1Value)){
                zstring verifingValue = sumValue.extract(sumValue.length() - ts1Value.length(), ts1Value.length());
                if (verifingValue == ts1Value) {
                    ts0Value = sumValue.extract(0, sumValue.length() - ts1Value.length());
                    litems.push_back(ctx.mk_eq_atom(concat, value));
                    expr *ts0exprValue = u.str.mk_string(ts0Value);
                    m_trail.push_back(ts0exprValue);

                    expr_ref implyL(mk_and(litems), m);
                    assert_implication(implyL, ctx.mk_eq_atom(ts00, ts0exprValue));
                }
                else {
                    expr* conclusion = mk_not(m, createEqualOperator(concat, value));
                    expr_ref implyL(mk_and(litems), m);
                    assert_implication(implyL, conclusion);
                }
            }

        }
        else {

            expr_ref_vector litems_lhs(m);
            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": " << mk_ismt2_pp(new_concat, m) << std::endl;);
            expr* lhs = construct_overapprox(new_concat, litems_lhs);
            if (lhs == nullptr)
                return;
            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": " << mk_ismt2_pp(new_concat, m) << " == " << mk_ismt2_pp(lhs, m) << std::endl;);
            for (expr_ref_vector::iterator itor = eqConcatList.begin(); itor != eqConcatList.end(); itor++) {
                expr_ref_vector litems_rhs(m);

                expr* rhs = construct_overapprox(*itor, litems_rhs);
                if (rhs == nullptr)
                    return;
                bool matchRes = matchRegex(rhs, lhs);
                STRACE("str", tout << __LINE__ << " " << mk_ismt2_pp(new_concat, m) << " = " << mk_ismt2_pp(rhs, m) << " : "
                                   << (matchRes ? "yes: " : "no: ") << std::endl;);
                if (!matchRes) {
                    if (*itor != concat)
                        litems_lhs.push_back(ctx.mk_eq_atom(concat, *itor));

                    for (int i = 0; i < litems_lhs.size(); ++i)
                        litems_rhs.push_back(litems_lhs[i].get());

                    for (int i = 0; i < litems.size(); ++i)
                        litems_rhs.push_back(litems[i].get());
                    expr_ref implyL(mk_and(litems_rhs), m);
                    assert_implication(implyL, mk_not(m, ctx.mk_eq_atom(concat, new_concat)));
                }

                // upward propagation
                for (const auto & it : concat_astNode_map)
                    if (!eqConcatList.contains(it.get_value())){ // this to break the case: "" . x = x
                        expr *ts0 = it.get_key1();
                        expr *ts1 = it.get_key2();
                        expr *cc = it.get_value();

                        expr *new_ts0 = ts0;
                        expr *new_ts1 = ts1;
                        bool updated = false;
                        expr_ref_vector new_litems(m);
                        new_litems.append(litems);

                        // change first arg
                        if (ts0 == *itor) {
                            new_ts0 = new_concat;
                            if (*itor != concat)
                                new_litems.push_back(ctx.mk_eq_atom(concat, *itor));
                            updated = true;
                        }

                        // change 2nd arg
                        if (ts1 == *itor) {
                            new_ts1 = new_concat;
                            if (*itor != concat)
                                new_litems.push_back(ctx.mk_eq_atom(concat, *itor));
                            updated = true;
                        }

                        // propagate
                        if (updated) {
                            expr *newer_concat = u.str.mk_concat(new_ts0, new_ts1);
                            m_trail.push_back(newer_concat);
                            // check if it is feasible or not
                            propagate_non_const(litems, cc, newer_concat);
                        }
                    }
            }
        }
    }

    void theory_str::check_regex_in(expr * nn1, expr * nn2) {
        context & ctx = get_context();
        ast_manager & m = get_manager();
        TRACE("str", tout << __FUNCTION__ << ": " << mk_ismt2_pp(nn1, m) << " == " << mk_ismt2_pp(nn2, m) << std::endl;);

        // how to get regex_sort?
        sort * regex_sort = nullptr;
        if (regex_in_bool_map.size() > 0){
            expr *tmp = regex_in_bool_map.begin()->second;
            app *a_regexIn = to_app(tmp);
            expr *regexTerm = a_regexIn->get_arg(1);
            regex_sort = m.get_sort(regexTerm);
        }

        if (regex_sort == nullptr)
            return;

        expr_ref_vector eqNodeSet(m);

        expr * constStr_1 = collect_eq_nodes(nn1, eqNodeSet);
        expr * constStr_2 = collect_eq_nodes(nn2, eqNodeSet);
        expr * constStr = (constStr_1 != nullptr) ? constStr_1 : constStr_2;

        if (constStr == nullptr) {
            check_regex_in_lhs_rhs(nn1, nn2);
        } else {
            STRACE("str", tout << __LINE__ << __FUNCTION__ << ": " << mk_pp(nn1, m)  << std::endl;);
            // check string vs regex
            expr* lhs = u.re.mk_to_re(constStr);
            for (expr_ref_vector::iterator itor = eqNodeSet.begin(); itor != eqNodeSet.end(); itor++) {
                if (regex_in_var_reg_str_map.contains(*itor)) {
                    expr_ref_vector litems(m);
                    expr* rhs = construct_overapprox(*itor, litems);
                    STRACE("str", tout << __LINE__ << __FUNCTION__ << ": " << mk_pp(rhs, m)  << std::endl;);
                    if (rhs == nullptr)
                        return;
                    bool matchRes = matchRegex(rhs, lhs);
                    expr_ref implyL(ctx.mk_eq_atom(*itor, constStr), m);
                    if (!matchRes) {
                        assert_implication(mk_and(litems), mk_not(implyL));
                    }
                }
            }
        }
    }

    void theory_str::check_regex_in_lhs_rhs(expr * nn1, expr * nn2) {
        context &ctx = get_context();
        ast_manager &m = get_manager();
        TRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": " << mk_ismt2_pp(nn1, m) << " == " << mk_ismt2_pp(nn2, m) << std::endl;);

        // how to get regex_sort?
        sort *regex_sort = nullptr;
        if (regex_in_bool_map.size() > 0) {
            expr *tmp = regex_in_bool_map.begin()->second;
            app *a_regexIn = to_app(tmp);
            expr *regexTerm = a_regexIn->get_arg(1);
            regex_sort = m.get_sort(regexTerm);
        }

        if (regex_sort == nullptr)
            return;

        // check concat vs regex: x . "abc" --> regexAll . "abc"
        expr_ref_vector eqNodeSet01(m);
        collect_eq_nodes(nn1, eqNodeSet01);

        expr_ref_vector eqNodeSet02(m);
        collect_eq_nodes(nn2, eqNodeSet02);

        // check all LHS concat vs RHS regex
        for (expr_ref_vector::iterator itor01 = eqNodeSet01.begin(); itor01 != eqNodeSet01.end(); itor01++) {
            // check if concat has any const/regex
            expr_ref_vector litems(m);
            expr* lhs = construct_overapprox(*itor01, litems);
            if (lhs == nullptr)
                return;
            TRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": " << mk_ismt2_pp(lhs, m) << std::endl;);
            for (expr_ref_vector::iterator itor02 = eqNodeSet02.begin(); itor02 != eqNodeSet02.end(); itor02++)
                if (regex_in_var_reg_str_map.contains(*itor02)) {
                    expr_ref_vector litems_rhs(m);
                    expr* rhs_over = construct_overapprox(*itor02, litems_rhs);
                    if (rhs_over == nullptr)
                        return;
                    bool matchRes = matchRegex(rhs_over, lhs);
                    if (!matchRes) {
                        if (*itor01 != nn1)
                            litems_rhs.push_back(ctx.mk_eq_atom(nn1, *itor01));

                        for (int i = 0; i < litems.size(); ++i)
                            litems_rhs.push_back(litems[i].get());

                        expr_ref implyL(mk_and(litems_rhs), m);
                        assert_implication(implyL, mk_not(m, ctx.mk_eq_atom(nn1, nn2)));
                    }
                }
        }
    }

    expr* theory_str::construct_overapprox(expr* nn, expr_ref_vector & litems){
        context &ctx = get_context();
        ast_manager &m = get_manager();

        // how to get regex_sort?
        sort *regex_sort = nullptr;
        if (regex_in_bool_map.size() > 0) {
            expr *tmp = regex_in_bool_map.begin()->second;
            app *a_regexIn = to_app(tmp);
            expr *regexTerm = a_regexIn->get_arg(1);
            regex_sort = m.get_sort(regexTerm);
        }
        if (regex_sort == nullptr)
            regex_sort = u.re.mk_re(m.get_sort(nn));

        if (regex_sort == nullptr)
            return nullptr;

        ptr_vector<expr> childrenVector;
        get_nodes_in_concat(nn, childrenVector);
        zstring emptyConst("");
        app *lhs = u.re.mk_to_re(u.str.mk_string(emptyConst));
        m_trail.push_back(lhs);

        // list of constraints
        bool lastIsSigmaStar = false;
        for (auto el : childrenVector) {
            zstring constStrValue;
            if (u.str.is_string(el, constStrValue)) {
                if (constStrValue.length() > 0) {
                    lhs = u.re.mk_concat(lhs, u.re.mk_to_re(el));
                    ensure_enode(lhs);
                    m_trail.push_back(lhs);
                    lastIsSigmaStar = false;
                }
            } else {
                // if it is equal to const
                expr_ref_vector tmpEqNodeSet(m);
                expr *childValue = collect_eq_nodes(el, tmpEqNodeSet);
                if (childValue != nullptr) {
                    litems.push_back(ctx.mk_eq_atom(childValue, el));
                    u.str.is_string(childValue, constStrValue);
                    if (constStrValue.length() > 0) {
                        lhs = u.re.mk_concat(lhs, u.re.mk_to_re(childValue));
                        m_trail.push_back(lhs);
                        lastIsSigmaStar = false;
                    }

                } else {
                    // if it has languages, take the 1st one
                    if (regex_in_var_reg_str_map.contains(el)) {
                        expr* tmp = nullptr;
                        expr_ref_vector tmpList(m);
                        for (const auto& we: membership_memo) {
                            if (we.first.get() == el) {
                                tmp = tmp == nullptr ? we.second.get() : u.re.mk_inter(we.second.get(), tmp);
                                tmpList.push_back(u.re.mk_in_re(we.first.get(), we.second.get()));
                                STRACE("str", tout << __LINE__ << ": " << mk_ismt2_pp(tmp, m) << std::endl;);
                            }
                        }

                        for (const auto& we: non_membership_memo) {
                            if (we.first.get() == el) {
                                STRACE("str", tout << __LINE__ << ": " << mk_ismt2_pp(we.first, m) << std::endl;);
                                tmp = tmp == nullptr ? u.re.mk_complement(we.second.get()) : u.re.mk_inter( u.re.mk_complement(we.second.get()), tmp);
                                tmpList.push_back(mk_not(m, u.re.mk_in_re(we.first.get(), we.second.get())));
                                STRACE("str", tout << __LINE__ << ": " << mk_ismt2_pp(tmp, m) << std::endl;);
                            }
                        }
                        STRACE("str", tout << __LINE__ << " " << mk_ismt2_pp(nn, m) << " empty " << std::endl;);
                        eautomaton *au01 = get_automaton(tmp);
                        bool empty = au01->is_empty();

                        if (empty) {
                            expr_ref implyL(mk_and(tmpList), m);
                            assert_implication(implyL, m.mk_false());
                            return nullptr;
                        }
                        else {
                            for (int i = 0; i < tmpList.size(); ++i)
                                litems.push_back(tmpList[i].get());
                            lhs = u.re.mk_concat(lhs, tmp);
                            STRACE("str", tout << __FUNCTION__ << ": " << mk_ismt2_pp(lhs, m) << std::endl;);
                            m_trail.push_back(lhs);
                            lastIsSigmaStar = false;
                        }
                    } else {
                        if (!lastIsSigmaStar) {
                            lhs = u.re.mk_concat(lhs, u.re.mk_full_seq(regex_sort));
                            m_trail.push_back(lhs);
                        }
                        lastIsSigmaStar = true;
                    }
                }
            }
        }

        STRACE("str", tout << __FUNCTION__ << ": " << mk_ismt2_pp(nn, m) << " --> " << mk_ismt2_pp(lhs, m) << std::endl;);

        return lhs;
    }

    void theory_str::propagate_contain_in_new_eq(expr * n1, expr * n2) {
        if (contains_map.empty()) {
            return;
        }

        ast_manager & m = get_manager();
        TRACE("str", tout << __FUNCTION__ << ": "<< mk_pp(n1, m) << " and " << mk_pp(n2, m) << std::endl;);

        expr_ref_vector willEqClass(m);
        expr * constStrAst_1 = collect_eq_nodes(n1, willEqClass);
        expr * constStrAst_2 = collect_eq_nodes(n2, willEqClass);
        expr * constStrAst = (constStrAst_1 != nullptr) ? constStrAst_1 : constStrAst_2;

        // step 1: we may have constant values for Contains checks now
        if (constStrAst != nullptr) {
            for (auto a : willEqClass) {
                if (a == constStrAst) {
                    continue;
                }
                check_contain_by_eqc_val(a, constStrAst);
            }
        } else {
            // no concrete value to be put in eqc, solely based on context
            // Check here is used to detected the facts as follows:
            //   * known: contains(Z, Y) /\ Z = "abcdefg" /\ Y = M
            //   * new fact: M = concat(..., "jio", ...)
            // Note that in this branch, either M or concat(..., "jio", ...) has a constant value
            // So, only need to check
            //   * "EQC(M) U EQC(concat(..., "jio", ...))" as substr and
            //   * If strAst registered has an eqc constant in the context
            // -------------------------------------------------------------
            for (auto a : willEqClass) {
                check_contain_by_substr(a, willEqClass);
            }
        }

        // ------------------------------------------
        // step 2: check for b1 = contains(x, m), b2 = contains(y, n)
        //         (1) x = y /\ m = n  ==>  b1 = b2
        //         (2) x = y /\ Contains(const(m), const(n))  ==>  (b1 -> b2)
        //         (3) x = y /\ Contains(const(n), const(m))  ==>  (b2 -> b1)
        //         (4) x = y /\ containPairBoolMap[<eqc(m), eqc(n)>]  ==>  (b1 -> b2)
        //         (5) x = y /\ containPairBoolMap[<eqc(n), eqc(m)>]  ==>  (b2 -> b1)
        //         (6) Contains(const(x), const(y)) /\ m = n  ==>  (b2 -> b1)
        //         (7) Contains(const(y), const(x)) /\ m = n  ==>  (b1 -> b2)
        //         (8) containPairBoolMap[<eqc(x), eqc(y)>] /\ m = n  ==>  (b2 -> b1)
        //         (9) containPairBoolMap[<eqc(y), eqc(x)>] /\ m = n  ==>  (b1 -> b2)
        // ------------------------------------------

        for (auto varAst1 : willEqClass) {
            for (auto varAst2 : willEqClass) {
                check_contain_by_eq_nodes(varAst1, varAst2);
            }
        }
    }

    /*
     *
     */
    void theory_str::check_contain_by_eqc_val(expr * varNode, expr * constNode) {
        context & ctx = get_context();
        ast_manager & m = get_manager();

        TRACE("str", tout << "varNode = " << mk_pp(varNode, m) << ", constNode = " << mk_pp(constNode, m) << std::endl;);

        expr_ref_vector litems(m);

        if (contain_pair_idx_map.contains(varNode)) {
            for (auto entry : contain_pair_idx_map[varNode]) {
                expr * strAst = entry.first;
                expr * substrAst = entry.second;

                expr * boolVar = nullptr;
                if (!contain_pair_bool_map.find(strAst, substrAst, boolVar)) {
                    TRACE("str", tout << "warning: no entry for boolVar in contain_pair_bool_map" << std::endl;);
                }

                // we only want to inspect the Contains terms where either of strAst or substrAst
                // are equal to varNode.

                TRACE("t_str_detail", tout << "considering Contains with strAst = " << mk_pp(strAst, m) << ", substrAst = " << mk_pp(substrAst, m) << "..." << std::endl;);

                if (varNode != strAst && varNode != substrAst) {
                    TRACE("str", tout << "varNode not equal to strAst or substrAst, skip" << std::endl;);
                    continue;
                }
                TRACE("str", tout << "varNode matched one of strAst or substrAst. Continuing" << std::endl;);

                // varEqcNode is str
                if (strAst == varNode) {
                    expr_ref implyR(m);
                    litems.reset();

                    if (strAst != constNode) {
                        litems.push_back(ctx.mk_eq_atom(strAst, constNode));
                    }
                    zstring strConst;
                    u.str.is_string(constNode, strConst);
                    bool subStrHasEqcValue = false;
                    expr * substrValue = get_eqc_value(substrAst, subStrHasEqcValue);
                    if (substrValue != substrAst) {
                        litems.push_back(ctx.mk_eq_atom(substrAst, substrValue));
                    }

                    if (subStrHasEqcValue) {
                        // subStr has an eqc constant value
                        zstring subStrConst;
                        u.str.is_string(substrValue, subStrConst);

                        TRACE("t_str_detail", tout << "strConst = " << strConst << ", subStrConst = " << subStrConst << "\n";);

                        if (strConst.contains(subStrConst)) {
                            //implyR = ctx.mk_eq(ctx, boolVar, Z3_mk_true(ctx));
                            implyR = boolVar;
                        } else {
                            //implyR = Z3_mk_eq(ctx, boolVar, Z3_mk_false(ctx));
                            implyR = mk_not(m, boolVar);
                        }
                    } else {
                        // ------------------------------------------------------------------------------------------------
                        // subStr doesn't have an eqc constant value
                        // however, subStr equals to some concat(arg_1, arg_2, ..., arg_n)
                        // if arg_j is a constant and is not a part of the strConst, it's sure that the contains is false
                        // ** This check is needed here because the "strConst" and "strAst" may not be in a same eqc yet
                        // ------------------------------------------------------------------------------------------------
                        // collect eqc concat
                        std::set<expr*> eqcConcats;
                        get_concats_in_eqc(substrAst, eqcConcats);
                        for (expr * aConcat : eqcConcats) {
                            expr_ref_vector constList(m);
                            bool counterEgFound = false;
                            get_const_str_asts_in_node(aConcat, constList);
                            for (auto const& cst : constList) {
                                zstring pieceStr;
                                u.str.is_string(cst, pieceStr);
                                if (!strConst.contains(pieceStr)) {
                                    counterEgFound = true;
                                    if (aConcat != substrAst) {
                                        litems.push_back(ctx.mk_eq_atom(substrAst, aConcat));
                                    }
                                    implyR = mk_not(m, boolVar);
                                    break;
                                }
                            }
                            if (counterEgFound) {
                                TRACE("str", tout << "Inconsistency found!" << std::endl;);
                                break;
                            }
                        }
                    }
                    // add assertion
                    if (implyR) {
                        expr_ref implyLHS(mk_and(litems), m);
                        assert_implication(implyLHS, implyR);
                    }
                }
                    // varEqcNode is subStr
                else if (substrAst == varNode) {
                    expr_ref implyR(m);
                    litems.reset();

                    if (substrAst != constNode) {
                        litems.push_back(ctx.mk_eq_atom(substrAst, constNode));
                    }
                    bool strHasEqcValue = false;
                    expr * strValue = get_eqc_value(strAst, strHasEqcValue);
                    if (strValue != strAst) {
                        litems.push_back(ctx.mk_eq_atom(strAst, strValue));
                    }

                    if (strHasEqcValue) {
                        zstring strConst, subStrConst;
                        u.str.is_string(strValue, strConst);
                        u.str.is_string(constNode, subStrConst);
                        if (strConst.contains(subStrConst)) {
                            //implyR = Z3_mk_eq(ctx, boolVar, Z3_mk_true(ctx));
                            implyR = boolVar;
                        } else {
                            // implyR = Z3_mk_eq(ctx, boolVar, Z3_mk_false(ctx));
                            implyR = mk_not(m, boolVar);
                        }
                    }

                    // add assertion
                    if (implyR) {
                        expr_ref implyLHS(mk_and(litems), m);
                        assert_implication(implyLHS, implyR);
                    }
                }
            } // for (itor1 : contains_map)
        } // if varNode in contain_pair_idx_map
    }

    void theory_str::check_contain_by_substr(expr * varNode, expr_ref_vector & willEqClass) {
        context & ctx = get_context();
        ast_manager & m = get_manager();
        expr_ref_vector litems(m);

        if (contain_pair_idx_map.contains(varNode)) {
            for (auto entry : contain_pair_idx_map[varNode]) {
                expr * strAst = entry.first;
                expr * substrAst = entry.second;

                expr * boolVar = nullptr;
                if (!contain_pair_bool_map.find(strAst, substrAst, boolVar)) {
                    TRACE("str", tout << "warning: no entry for boolVar in contain_pair_bool_map" << std::endl;);
                }

                // we only want to inspect the Contains terms where either of strAst or substrAst
                // are equal to varNode.

                TRACE("t_str_detail", tout << "considering Contains with strAst = " << mk_pp(strAst, m) << ", substrAst = " << mk_pp(substrAst, m) << "..." << std::endl;);

                if (varNode != strAst && varNode != substrAst) {
                    TRACE("str", tout << "varNode not equal to strAst or substrAst, skip" << std::endl;);
                    continue;
                }
                TRACE("str", tout << "varNode matched one of strAst or substrAst. Continuing" << std::endl;);

                if (substrAst == varNode) {
                    bool strAstHasVal = false;
                    expr * strValue = get_eqc_value(strAst, strAstHasVal);
                    if (strAstHasVal) {
                        TRACE("str", tout << mk_pp(strAst, m) << " has constant eqc value " << mk_pp(strValue, m) << std::endl;);
                        if (strValue != strAst) {
                            litems.push_back(ctx.mk_eq_atom(strAst, strValue));
                        }
                        zstring strConst;
                        u.str.is_string(strValue, strConst);
                        // iterate eqc (also eqc-to-be) of substr
                        for (auto itAst : willEqClass) {
                            bool counterEgFound = false;
                            if (u.str.is_concat(to_app(itAst))) {
                                expr_ref_vector constList(m);
                                // get constant strings in concat
                                app * aConcat = to_app(itAst);
                                get_const_str_asts_in_node(aConcat, constList);
                                for (auto cst : constList) {
                                    zstring pieceStr;
                                    u.str.is_string(cst, pieceStr);
                                    if (!strConst.contains(pieceStr)) {
                                        TRACE("str", tout << "Inconsistency found!" << std::endl;);
                                        counterEgFound = true;
                                        if (aConcat != substrAst) {
                                            litems.push_back(ctx.mk_eq_atom(substrAst, aConcat));
                                        }
                                        expr_ref implyLHS(mk_and(litems), m);
                                        expr_ref implyR(mk_not(m, boolVar), m);
                                        assert_implication(implyLHS, implyR);
                                        break;
                                    }
                                }
                            }
                            if (counterEgFound) {
                                break;
                            }
                        }
                    }
                }
            }
        } // varNode in contain_pair_idx_map
    }

    bool theory_str::in_contain_idx_map(expr * n) {
        return contain_pair_idx_map.contains(n);
    }

    void theory_str::check_contain_by_eq_nodes(expr * n1, expr * n2) {
        context & ctx = get_context();
        ast_manager & m = get_manager();

        if (in_contain_idx_map(n1) && in_contain_idx_map(n2)) {
            for (auto const& key1 : contain_pair_idx_map[n1]) {
                // keysItor1 is on set {<.., n1>, ..., <n1, ...>, ...}
                //std::pair<expr*, expr*> key1 = *keysItor1;
                if (key1.first == n1 && key1.second == n2) {
                    expr_ref implyL(m);
                    expr_ref implyR(contain_pair_bool_map[key1], m);
                    if (n1 != n2) {
                        implyL = ctx.mk_eq_atom(n1, n2);
                        assert_implication(implyL, implyR);
                    } else {
                        assert_axiom(implyR);
                    }
                }

                //for (keysItor2 = contain_pair_idx_map[n2].begin(); keysItor2 != contain_pair_idx_map[n2].end(); keysItor2++) {
                for (auto const& key2 : contain_pair_idx_map[n2]) {
                    // keysItor2 is on set {<.., n2>, ..., <n2, ...>, ...}
                    //std::pair<expr*, expr*> key2 = *keysItor2;
                    // skip if the pair is eq
                    if (key1 == key2) {
                        continue;
                    }

                    // ***************************
                    // Case 1: Contains(m, ...) /\ Contains(n, ) /\ m = n
                    // ***************************
                    if (key1.first == n1 && key2.first == n2) {
                        expr * subAst1 = key1.second;
                        expr * subAst2 = key2.second;
                        bool subAst1HasValue = false;
                        bool subAst2HasValue = false;
                        expr * subValue1 = get_eqc_value(subAst1, subAst1HasValue);
                        expr * subValue2 = get_eqc_value(subAst2, subAst2HasValue);

//                        TRACE("str",
//                              tout << "(Contains " << mk_pp(n1, m) << " " << mk_pp(subAst1, m) << ")" << std::endl;
//                                      tout << "(Contains " << mk_pp(n2, m) << " " << mk_pp(subAst2, m) << ")" << std::endl;
//                                      if (subAst1 != subValue1) {
//                                          tout << mk_pp(subAst1, m) << " = " << mk_pp(subValue1, m) << std::endl;
//                                      }
//                                      if (subAst2 != subValue2) {
//                                          tout << mk_pp(subAst2, m) << " = " << mk_pp(subValue2, m) << std::endl;
//                                      }
//                        );

                        if (subAst1HasValue && subAst2HasValue) {
                            expr_ref_vector litems1(m);
                            if (n1 != n2) {
                                litems1.push_back(ctx.mk_eq_atom(n1, n2));
                            }
                            if (subValue1 != subAst1) {
                                litems1.push_back(ctx.mk_eq_atom(subAst1, subValue1));
                            }
                            if (subValue2 != subAst2) {
                                litems1.push_back(ctx.mk_eq_atom(subAst2, subValue2));
                            }

                            zstring subConst1, subConst2;
                            u.str.is_string(subValue1, subConst1);
                            u.str.is_string(subValue2, subConst2);
                            expr_ref implyR(m);
                            if (subConst1 == subConst2) {
                                // key1.first = key2.first /\ key1.second = key2.second
                                // ==> (containPairBoolMap[key1] = containPairBoolMap[key2])
                                implyR = ctx.mk_eq_atom(contain_pair_bool_map[key1], contain_pair_bool_map[key2]);
                            } else if (subConst1.contains(subConst2)) {
                                // key1.first = key2.first /\ Contains(key1.second, key2.second)
                                // ==> (containPairBoolMap[key1] --> containPairBoolMap[key2])
                                implyR = rewrite_implication(contain_pair_bool_map[key1], contain_pair_bool_map[key2]);
                            } else if (subConst2.contains(subConst1)) {
                                // key1.first = key2.first /\ Contains(key2.second, key1.second)
                                // ==> (containPairBoolMap[key2] --> containPairBoolMap[key1])
                                implyR = rewrite_implication(contain_pair_bool_map[key2], contain_pair_bool_map[key1]);
                            }

                            if (implyR) {
                                if (litems1.empty()) {
                                    assert_axiom(implyR);
                                } else {
                                    assert_implication(mk_and(litems1), implyR);
                                }
                            }
                        } else {
                            expr_ref_vector subAst1Eqc(m);
                            expr_ref_vector subAst2Eqc(m);
                            collect_eq_nodes(subAst1, subAst1Eqc);
                            collect_eq_nodes(subAst2, subAst2Eqc);

                            if (subAst1Eqc.contains(subAst2)) {
                                // -----------------------------------------------------------
                                // * key1.first = key2.first /\ key1.second = key2.second
                                //   -->  containPairBoolMap[key1] = containPairBoolMap[key2]
                                // -----------------------------------------------------------
                                expr_ref_vector litems2(m);
                                if (n1 != n2) {
                                    litems2.push_back(ctx.mk_eq_atom(n1, n2));
                                }
                                if (subAst1 != subAst2) {
                                    litems2.push_back(ctx.mk_eq_atom(subAst1, subAst2));
                                }
                                expr_ref implyR(ctx.mk_eq_atom(contain_pair_bool_map[key1], contain_pair_bool_map[key2]), m);
                                if (litems2.empty()) {
                                    assert_axiom(implyR);
                                } else {
                                    assert_implication(mk_and(litems2), implyR);
                                }
                            } else {
                                // -----------------------------------------------------------
                                // * key1.first = key2.first
                                //   check eqc(key1.second) and eqc(key2.second)
                                // -----------------------------------------------------------
                                //expr_ref_vector::iterator eqItorSub1 = subAst1Eqc.begin();
                                //for (; eqItorSub1 != subAst1Eqc.end(); eqItorSub1++) {
                                for (auto eqSubVar1 : subAst1Eqc) {
                                    //expr_ref_vector::iterator eqItorSub2 = subAst2Eqc.begin();
                                    //for (; eqItorSub2 != subAst2Eqc.end(); eqItorSub2++) {
                                    for (auto eqSubVar2 : subAst2Eqc) {
                                        // ------------
                                        // key1.first = key2.first /\ containPairBoolMap[<eqc(key1.second), eqc(key2.second)>]
                                        // ==>  (containPairBoolMap[key1] --> containPairBoolMap[key2])
                                        // ------------
                                        {
                                            expr_ref_vector litems3(m);
                                            if (n1 != n2) {
                                                litems3.push_back(ctx.mk_eq_atom(n1, n2));
                                            }

                                            if (eqSubVar1 != subAst1) {
                                                litems3.push_back(ctx.mk_eq_atom(subAst1, eqSubVar1));
                                            }

                                            if (eqSubVar2 != subAst2) {
                                                litems3.push_back(ctx.mk_eq_atom(subAst2, eqSubVar2));
                                            }
                                            std::pair<expr*, expr*> tryKey1 = std::make_pair(eqSubVar1, eqSubVar2);
                                            if (contain_pair_bool_map.contains(tryKey1)) {
                                                TRACE("str", tout << "(Contains " << mk_pp(eqSubVar1, m) << " " << mk_pp(eqSubVar2, m) << ")" << std::endl;);
                                                litems3.push_back(contain_pair_bool_map[tryKey1]);
                                                expr_ref implR(rewrite_implication(contain_pair_bool_map[key1], contain_pair_bool_map[key2]), m);
                                                assert_implication(mk_and(litems3), implR);
                                            }
                                        }
                                        // ------------
                                        // key1.first = key2.first /\ containPairBoolMap[<eqc(key2.second), eqc(key1.second)>]
                                        // ==>  (containPairBoolMap[key2] --> containPairBoolMap[key1])
                                        // ------------
                                        {
                                            expr_ref_vector litems4(m);
                                            if (n1 != n2) {
                                                litems4.push_back(ctx.mk_eq_atom(n1, n2));
                                            }

                                            if (eqSubVar1 != subAst1) {
                                                litems4.push_back(ctx.mk_eq_atom(subAst1, eqSubVar1));
                                            }

                                            if (eqSubVar2 != subAst2) {
                                                litems4.push_back(ctx.mk_eq_atom(subAst2, eqSubVar2));
                                            }
                                            std::pair<expr*, expr*> tryKey2 = std::make_pair(eqSubVar2, eqSubVar1);
                                            if (contain_pair_bool_map.contains(tryKey2)) {
                                                TRACE("str", tout << "(Contains " << mk_pp(eqSubVar2, m) << " " << mk_pp(eqSubVar1, m) << ")" << std::endl;);
                                                litems4.push_back(contain_pair_bool_map[tryKey2]);
                                                expr_ref implR(rewrite_implication(contain_pair_bool_map[key2], contain_pair_bool_map[key1]), m);
                                                assert_implication(mk_and(litems4), implR);
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                        // ***************************
                        // Case 2: Contains(..., m) /\ Contains(... , n) /\ m = n
                        // ***************************
                    else if (key1.second == n1 && key2.second == n2) {
                        expr * str1 = key1.first;
                        expr * str2 = key2.first;
                        bool str1HasValue = false;
                        bool str2HasValue = false;
                        expr * strVal1 = get_eqc_value(str1, str1HasValue);
                        expr * strVal2 = get_eqc_value(str2, str2HasValue);

                        TRACE("str",
                              tout << "(Contains " << mk_pp(str1, m) << " " << mk_pp(n1, m) << ")" << std::endl;
                                      tout << "(Contains " << mk_pp(str2, m) << " " << mk_pp(n2, m) << ")" << std::endl;
                                      if (str1 != strVal1) {
                                          tout << mk_pp(str1, m) << " = " << mk_pp(strVal1, m) << std::endl;
                                      }
                                      if (str2 != strVal2) {
                                          tout << mk_pp(str2, m) << " = " << mk_pp(strVal2, m) << std::endl;
                                      }
                        );

                        if (str1HasValue && str2HasValue) {
                            expr_ref_vector litems1(m);
                            if (n1 != n2) {
                                litems1.push_back(ctx.mk_eq_atom(n1, n2));
                            }
                            if (strVal1 != str1) {
                                litems1.push_back(ctx.mk_eq_atom(str1, strVal1));
                            }
                            if (strVal2 != str2) {
                                litems1.push_back(ctx.mk_eq_atom(str2, strVal2));
                            }

                            zstring const1, const2;
                            u.str.is_string(strVal1, const1);
                            u.str.is_string(strVal2, const2);
                            expr_ref implyR(m);

                            if (const1 == const2) {
                                // key1.second = key2.second /\ key1.first = key2.first
                                // ==> (containPairBoolMap[key1] = containPairBoolMap[key2])
                                implyR = ctx.mk_eq_atom(contain_pair_bool_map[key1], contain_pair_bool_map[key2]);
                            } else if (const1.contains(const2)) {
                                // key1.second = key2.second /\ Contains(key1.first, key2.first)
                                // ==> (containPairBoolMap[key2] --> containPairBoolMap[key1])
                                implyR = rewrite_implication(contain_pair_bool_map[key2], contain_pair_bool_map[key1]);
                            } else if (const2.contains(const1)) {
                                // key1.first = key2.first /\ Contains(key2.first, key1.first)
                                // ==> (containPairBoolMap[key1] --> containPairBoolMap[key2])
                                implyR = rewrite_implication(contain_pair_bool_map[key1], contain_pair_bool_map[key2]);
                            }

                            if (implyR) {
                                if (litems1.size() == 0) {
                                    assert_axiom(implyR);
                                } else {
                                    assert_implication(mk_and(litems1), implyR);
                                }
                            }
                        }

                        else {
                            expr_ref_vector str1Eqc(m);
                            expr_ref_vector str2Eqc(m);
                            collect_eq_nodes(str1, str1Eqc);
                            collect_eq_nodes(str2, str2Eqc);

                            if (str1Eqc.contains(str2)) {
                                // -----------------------------------------------------------
                                // * key1.first = key2.first /\ key1.second = key2.second
                                //   -->  containPairBoolMap[key1] = containPairBoolMap[key2]
                                // -----------------------------------------------------------
                                expr_ref_vector litems2(m);
                                if (n1 != n2) {
                                    litems2.push_back(ctx.mk_eq_atom(n1, n2));
                                }
                                if (str1 != str2) {
                                    litems2.push_back(ctx.mk_eq_atom(str1, str2));
                                }
                                expr_ref implyR(ctx.mk_eq_atom(contain_pair_bool_map[key1], contain_pair_bool_map[key2]), m);
                                if (litems2.empty()) {
                                    assert_axiom(implyR);
                                } else {
                                    assert_implication(mk_and(litems2), implyR);
                                }
                            } else {
                                // -----------------------------------------------------------
                                // * key1.second = key2.second
                                //   check eqc(key1.first) and eqc(key2.first)
                                // -----------------------------------------------------------
                                for (auto const& eqStrVar1 : str1Eqc) {
                                    for (auto const& eqStrVar2 : str2Eqc) {
                                        {
                                            expr_ref_vector litems3(m);
                                            if (n1 != n2) {
                                                litems3.push_back(ctx.mk_eq_atom(n1, n2));
                                            }

                                            if (eqStrVar1 != str1) {
                                                litems3.push_back(ctx.mk_eq_atom(str1, eqStrVar1));
                                            }

                                            if (eqStrVar2 != str2) {
                                                litems3.push_back(ctx.mk_eq_atom(str2, eqStrVar2));
                                            }
                                            std::pair<expr*, expr*> tryKey1 = std::make_pair(eqStrVar1, eqStrVar2);
                                            if (contain_pair_bool_map.contains(tryKey1)) {
                                                TRACE("str", tout << "(Contains " << mk_pp(eqStrVar1, m) << " " << mk_pp(eqStrVar2, m) << ")" << std::endl;);
                                                litems3.push_back(contain_pair_bool_map[tryKey1]);

                                                // ------------
                                                // key1.second = key2.second /\ containPairBoolMap[<eqc(key1.first), eqc(key2.first)>]
                                                // ==>  (containPairBoolMap[key2] --> containPairBoolMap[key1])
                                                // ------------
                                                expr_ref implR(rewrite_implication(contain_pair_bool_map[key2], contain_pair_bool_map[key1]), m);
                                                assert_implication(mk_and(litems3), implR);
                                            }
                                        }

                                        {
                                            expr_ref_vector litems4(m);
                                            if (n1 != n2) {
                                                litems4.push_back(ctx.mk_eq_atom(n1, n2));
                                            }
                                            if (eqStrVar1 != str1) {
                                                litems4.push_back(ctx.mk_eq_atom(str1, eqStrVar1));
                                            }
                                            if (eqStrVar2 != str2) {
                                                litems4.push_back(ctx.mk_eq_atom(str2, eqStrVar2));
                                            }
                                            std::pair<expr*, expr*> tryKey2 = std::make_pair(eqStrVar2, eqStrVar1);

                                            if (contain_pair_bool_map.contains(tryKey2)) {
                                                TRACE("str", tout << "(Contains " << mk_pp(eqStrVar2, m) << " " << mk_pp(eqStrVar1, m) << ")" << std::endl;);
                                                litems4.push_back(contain_pair_bool_map[tryKey2]);
                                                // ------------
                                                // key1.first = key2.first /\ containPairBoolMap[<eqc(key2.second), eqc(key1.second)>]
                                                // ==>  (containPairBoolMap[key1] --> containPairBoolMap[key2])
                                                // ------------
                                                expr_ref implR(rewrite_implication(contain_pair_bool_map[key1], contain_pair_bool_map[key2]), m);
                                                assert_implication(mk_and(litems4), implR);
                                            }
                                        }
                                    }
                                }
                            }
                        }

                    }
                }

                if (n1 == n2) {
                    break;
                }
            }
        } // (in_contain_idx_map(n1) && in_contain_idx_map(n2))
    }

    /*
    * Decide whether n1 and n2 are already in the same equivalence class.
    * This only checks whether the core considers them to be equal;
    * they may not actually be equal.
    */
    bool theory_str::in_same_eqc(expr * n1, expr * n2) {
        if (n1 == n2) return true;
        context & ctx = get_context();

        // similar to get_eqc_value(), make absolutely sure
        // that we've set this up properly for the context

        if (!ctx.e_internalized(n1)) {
            TRACE("str", tout << "WARNING: expression " << mk_ismt2_pp(n1, get_manager()) << " was not internalized" << std::endl;);
            ctx.internalize(n1, false);
        }
        if (!ctx.e_internalized(n2)) {
            TRACE("str", tout << "WARNING: expression " << mk_ismt2_pp(n2, get_manager()) << " was not internalized" << std::endl;);
            ctx.internalize(n2, false);
        }

        expr * curr = get_eqc_next(n1);
        while (curr != n1) {
            if (curr == n2)
                return true;
            curr = get_eqc_next(curr);
        }
        return false;
    }

    expr * theory_str::collect_eq_nodes(expr * n, expr_ref_vector & eqcSet) {
        expr * constStrNode = nullptr;

        expr * ex = n;
        do {
            if (u.str.is_string(to_app(ex))) {
                constStrNode = ex;
            }
            eqcSet.push_back(ex);

            ex = get_eqc_next(ex);
        } while (ex != n);
        return constStrNode;
    }


    void theory_str::new_diseq_eh(theory_var x, theory_var y) {
        ast_manager& m = get_manager();

        expr *const n1 = get_enode(x)->get_owner();
        expr *const n2 = get_enode(y)->get_owner();


        STRACE("str", tout << __FUNCTION__ << ": " << mk_ismt2_pp(n1, m) << " != "
                           << mk_ismt2_pp(n2, m) << " @ lvl " << m_scope_level << std::endl;);
        if (is_inconsistent_inequality(n1, n2)){
            return;
        }
        bool skip = false;
        {
            zstring value;
            if (u.str.is_string(n1, value)) {
                if (value.length() != 0 || m_scope_level == 0) {
                }
                else
                    skip = true;
            }
            else if (u.str.is_string(n2, value)) {
                if (value.length() != 0 || m_scope_level == 0) {
                }
                else
                    skip = true;
            }

            if (u.str.is_concat(n1)){
                if (n2 == to_app(n1)->get_arg(0) || n2 == to_app(n1)->get_arg(1))
                    skip = true;
            }

            if (u.str.is_concat(n2)){
                if (n1 == to_app(n2)->get_arg(0) || n1 == to_app(n2)->get_arg(1))
                    skip = true;
            }
        }

        instantiate_str_diseq_length_axiom(n1, n2, skip);

        if (!skip && is_not_added_diseq(expr_ref{n1, m}, expr_ref{n2, m})) {
            STRACE("str", tout << __FUNCTION__ << ": add to m_wi_expr_memo: " << mk_ismt2_pp(n1, m) << " != "
                               << mk_ismt2_pp(n2, m) << std::endl;);
            // skip all trivial diseq
            newConstraintTriggered = true;
            expr_ref tmp(mk_not(m, createEqualOperator(n1, n2)), m);
            ensure_enode(tmp);
            mful_scope_levels.push_back(tmp);

            const str::expr_pair wi{expr_ref{n1, m}, expr_ref{n2, m}};
            m_wi_expr_memo.push_back(wi);
        }
        else {
            newConstraintTriggered = true;
            STRACE("str", tout << __FUNCTION__ << ": not to m_wi_expr_memo: " << mk_ismt2_pp(n1, m) << " != "
                               << mk_ismt2_pp(n2, m) << std::endl;);
        }
    }

    /*
     * replace vs contain
     */
    bool theory_str::is_inconsistent_inequality(expr* lhs, expr* rhs){
        expr* str;
        expr* simplifiedLhs = simplify_concat(lhs);
        expr* simplifiedRhs = simplify_concat(rhs);
        if (is_contain_equality(simplifiedLhs, str)){
            zstring key;
            if (u.str.is_string(str, key)) {
                expr_ref_vector eqs(get_manager());
                collect_eq_nodes(rhs, eqs);
                for (const auto& eq : eqs) {
                    ptr_vector<expr> v;
                    get_all_nodes_in_concat(eq, v);
                    for (const auto &n : v) {

//                        expr * boolVar;
//                        if (contain_pair_bool_map.find(n, str, boolVar) && n != rhs){
//                            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " reach it "  << mk_pp(n, get_manager())<< std::endl;);
//                            expr_ref_vector premises(get_manager());
//                            premises.push_back(mk_not(get_manager(), createEqualOperator(lhs, rhs)));
//                            premises.push_back(createEqualOperator(rhs, eq));
//                            assert_implication(createAndOperator(premises), mk_not(get_manager(), boolVar));
//                        }

                        zstring tmp;
                        if (u.str.is_string(n, tmp)) {
                            if (tmp.contains(key)) {
                                expr *conclusion = createEqualOperator(lhs, rhs);
                                if (eq != rhs) {
                                    expr *premise = createEqualOperator(rhs, eq);
                                    assert_implication(premise, conclusion);
                                } else
                                    assert_axiom(conclusion);
                                return true;
                            }
                        }
//                        else if (u.str.is_concat(n)){
//                            expr* arg0 = to_app(n)->get_arg(0);
//                            expr* arg1 = to_app(n)->get_arg(1);
//                            if (contain_pair_bool_map.find(arg0, str, boolVar)){
//                                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " reach it " << std::endl;);
//                                expr_ref_vector premises(get_manager());
//                                premises.push_back(mk_not(get_manager(), createEqualOperator(lhs, rhs)));
//                                premises.push_back(createEqualOperator(rhs, eq));
//                                assert_implication(createAndOperator(premises), mk_not(get_manager(), boolVar));
//                            }
//
//                            if (contain_pair_bool_map.find(arg1, str, boolVar)){
//                                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " reach it " << std::endl;);
//                                expr_ref_vector premises(get_manager());
//                                premises.push_back(mk_not(get_manager(), createEqualOperator(lhs, rhs)));
//                                premises.push_back(createEqualOperator(rhs, eq));
//                                assert_implication(createAndOperator(premises), mk_not(get_manager(), boolVar));
//                            }
//
//                            ptr_vector<expr> v_arg;
//                            get_nodes_in_concat(arg0, v_arg);
//                            for (const auto& nn : v_arg){
//                                if (u.str.is_string(nn, tmp)) {
//                                    if (tmp.contains(key)) {
//                                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " reach it " << std::endl;);
//                                        expr_ref_vector premises(get_manager());
//                                        premises.push_back(createEqualOperator(rhs, eq));
//                                        premises.push_back(createEqualOperator(nn, arg0));
//                                        assert_implication(createAndOperator(premises), createEqualOperator(lhs, rhs));
//                                        return true;
//                                    }
//                                }
//                            }
//
//                            v_arg.clear();
//                            get_nodes_in_concat(arg1, v_arg);
//                            for (const auto& nn : v_arg){
//                                if (u.str.is_string(nn, tmp)) {
//                                    if (tmp.contains(key)) {
//                                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " reach it " << std::endl;);
//                                        expr_ref_vector premises(get_manager());
//                                        premises.push_back(createEqualOperator(rhs, eq));
//                                        premises.push_back(createEqualOperator(nn, arg1));
//                                        assert_implication(createAndOperator(premises), createEqualOperator(lhs, rhs));
//                                        return true;
//                                    }
//                                }
//                            }
//                        }
                    }
                }
            }
        }

        if (is_contain_equality(simplifiedRhs, str)){
            zstring key;
            if (u.str.is_string(str, key)) {
                expr_ref_vector eqs(get_manager());
                collect_eq_nodes(lhs, eqs);
                for (const auto& eq : eqs) {
                    ptr_vector<expr> v;
                    get_all_nodes_in_concat(eq, v);
                    for (const auto &n : v) {
                        expr * boolVar;
//                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " reach it "  << mk_pp(n, get_manager())<< std::endl;);
//                        if (contain_pair_bool_map.find(n, str, boolVar) && n != lhs){
//                            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " reach it "  << mk_pp(n, get_manager())<< std::endl;);
//                            expr_ref_vector premises(get_manager());
//                            premises.push_back(mk_not(get_manager(), createEqualOperator(lhs, rhs)));
//                            premises.push_back(createEqualOperator(lhs, eq));
//                            assert_implication(createAndOperator(premises), mk_not(get_manager(), boolVar));
//                        }

                        zstring tmp;
                        if (u.str.is_string(n, tmp)) {
                            if (tmp.contains(key)) {
                                expr *conclusion = createEqualOperator(lhs, rhs);
                                if (eq != rhs) {
                                    expr *premise = createEqualOperator(lhs, eq);
                                    assert_implication(premise, conclusion);
                                } else
                                    assert_axiom(conclusion);
                                return true;
                            }
                        }
//                        else if (u.str.is_concat(n)){
//                            expr* arg0 = to_app(n)->get_arg(0);
//                            expr* arg1 = to_app(n)->get_arg(1);
//                            if (contain_pair_bool_map.find(arg0, str, boolVar)){
//                                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " reach it " << std::endl;);
//                                expr_ref_vector premises(get_manager());
//                                premises.push_back(mk_not(get_manager(), createEqualOperator(lhs, rhs)));
//                                premises.push_back(createEqualOperator(lhs, eq));
//                                assert_implication(createAndOperator(premises), mk_not(get_manager(), boolVar));
//                            }
//
//                            if (contain_pair_bool_map.find(arg1, str, boolVar)){
//                                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " reach it " << std::endl;);
//                                expr_ref_vector premises(get_manager());
//                                premises.push_back(mk_not(get_manager(), createEqualOperator(lhs, rhs)));
//                                premises.push_back(createEqualOperator(lhs, eq));
//                                assert_implication(createAndOperator(premises), mk_not(get_manager(), boolVar));
//                            }
//
//                            ptr_vector<expr> v_arg;
//                            get_nodes_in_concat(arg0, v_arg);
//                            for (const auto& nn : v_arg){
//                                if (u.str.is_string(nn, tmp)) {
//                                    if (tmp.contains(key)) {
//                                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " reach it " << std::endl;);
//                                        expr_ref_vector premises(get_manager());
//                                        premises.push_back(createEqualOperator(lhs, eq));
//                                        premises.push_back(createEqualOperator(nn, arg0));
//                                        assert_implication(createAndOperator(premises), createEqualOperator(lhs, rhs));
//                                        return true;
//                                    }
//                                }
//                            }
//
//                            v_arg.clear();
//                            get_nodes_in_concat(arg1, v_arg);
//                            for (const auto& nn : v_arg){
//                                if (u.str.is_string(nn, tmp)) {
//                                    if (tmp.contains(key)) {
//                                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " reach it " << std::endl;);
//                                        expr_ref_vector premises(get_manager());
//                                        premises.push_back(createEqualOperator(lhs, eq));
//                                        premises.push_back(createEqualOperator(nn, arg1));
//                                        assert_implication(createAndOperator(premises), createEqualOperator(lhs, rhs));
//                                        return true;
//                                    }
//                                }
//                            }
//                        }
                    }
                }
            }
        }
        return false;
    }

    bool theory_str::is_not_added_diseq(expr_ref n1, expr_ref n2){
        const str::expr_pair w01 = std::make_pair(n1, n2);
        const str::expr_pair w02 = std::make_pair(n2, n1);
        for (int i = 0; i < m_wi_expr_memo.size(); ++i)
            if (m_wi_expr_memo[i] == w01 || m_wi_expr_memo[i] == w02){
                return false;
            }
        return true;
    }

    void theory_str::assert_cached_diseq_state(){

        if (uState.reassertDisEQ) {
            return;
        }
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << std::endl;);
        handle_diseq(true);
        uState.reassertDisEQ = true;
        uState.diseqLevel = get_actual_trau_lvl();

    }

    void theory_str::breakdown_cached_diseq(expr* n1, expr* n2){
        ast_manager & m = get_manager();
        const str::word_term &lhs = get_word_term(n1);
        const str::word_term &rhs = get_word_term(n2);
        if (uState.currState.m_wes_to_fail.find(str::word_equation{rhs, lhs}) == uState.currState.m_wes_to_fail.end()) {
            STRACE("str", tout << __LINE__ <<  " not cached  " << mk_pp(n1, m) << " != " << mk_pp(n2, m) << std::endl;);
        }
        else {
            handle_NOTEqual(n1, n2);
            handle_NOTContain(n1, n2);
        }
    }

    /*
     * Add an axiom of the form:
     * len lhs != len rhs -> lhs != rhs
     * len lhs == 0 == len rhs --> lhs == rhs
     */
    void theory_str::instantiate_str_diseq_length_axiom(expr * lhs, expr * rhs, bool &skip) {
        context & ctx = get_context();
        ast_manager & m = get_manager();

        rational lenLhs, lenRhs;
        if (get_len_value(lhs, lenLhs) && get_len_value(rhs, lenRhs))
            if (lenLhs != lenRhs) {
                skip = true;
                return;
            }

        rational lowerBound_lhs, upperBound_lhs, lowerBound_rhs, upperBound_rhs;
        if (lower_bound(lhs, lowerBound_lhs))
            if (upper_bound(rhs, upperBound_rhs))
                if (lowerBound_lhs > upperBound_rhs) {
                    skip = true;
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << lowerBound_lhs << " > "  << upperBound_rhs << std::endl;);
                    return;
                }

        if (upper_bound(lhs, upperBound_lhs))
            if (lower_bound(rhs, lowerBound_rhs))
                if (upperBound_lhs < lowerBound_rhs) {
                    skip = true;
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << upperBound_lhs << " < "  << lowerBound_rhs << std::endl;);
                    return;
                }

        expr* emptystr = mk_string("");
        if (lhs == emptystr || rhs == emptystr){
            skip = true;
            return;
        }

        // build conclusion: not (lhs == rhs)
        expr_ref conclusion01(mk_not(m, ctx.mk_eq_atom(lhs, rhs)), m);

        // build premise: not ( Length(lhs) == Length(rhs) )
        expr_ref len_lhs(mk_strlen(lhs), m);
        zstring valueLhs;
        if (u.str.is_string(lhs, valueLhs))
            len_lhs = mk_int(valueLhs.length());

        expr_ref len_rhs(mk_strlen(rhs), m);
        zstring valueRhs;
        if (u.str.is_string(rhs, valueRhs))
            len_rhs = mk_int(valueRhs.length());

        expr_ref premise01(mk_not(m, ctx.mk_eq_atom(len_lhs, len_rhs)), m);

        expr* empty = mk_string("");
        if (lhs == empty || rhs == empty)
            assert_axiom(createEqualOperator(premise01, conclusion01));
        else
            assert_implication(premise01, conclusion01);

        // check all combinations
        zstring value;
        if (u.str.is_string(lhs, value)) {
            expr* extraAssert = handle_trivial_diseq(rhs, value);
            if (extraAssert != nullptr) {
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(extraAssert, m) << std::endl;);
                assert_axiom(createEqualOperator(conclusion01, extraAssert));
                skip = true;
            }
        }
        else if (u.str.is_string(rhs, value)) {
            expr* extraAssert = handle_trivial_diseq(lhs, value);
            if (extraAssert != nullptr) {
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(extraAssert, m) << std::endl;);
                assert_axiom(createEqualOperator(conclusion01, extraAssert));
                skip = true;
            }
        }


    }

    expr* theory_str::handle_trivial_diseq(expr * e, zstring value){
        ast_manager & m = get_manager();
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(e, m) << std::endl;);
        std::set<zstring> constPart = extract_const(e);

        for (const auto& s : constPart)
            if (s.length() > value.length() || (s.length() == value.length() && s != value)) {
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << s << std::endl;);
                return createGreaterEqOperator(mk_strlen(e), mk_int(s.length()));
            }
            else if (s == value) {
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << s << std::endl;);
                return createGreaterEqOperator(mk_strlen(e), mk_int(value.length() + 1));
            }
        return nullptr;
    }

    std::set<zstring> theory_str::extract_const(expr* e, int lvl){
        if (lvl >= 5)
            return {};

        ast_manager & m = get_manager();

        expr_ref_vector eq(m);
        expr* constValue = collect_eq_nodes(e, eq);
        if (constValue != nullptr){
            zstring constValueStr;
            u.str.is_string(constValue, constValueStr);
            return {constValueStr};
        }
        else {
            std::set<zstring> ret;
            for (int i = 0; i < eq.size(); ++i)
                if (u.str.is_concat(eq[i].get())) {
                    std::set<zstring> const00 = extract_const(to_app(eq[i].get())->get_arg(0), lvl + 1);
                    std::set<zstring> const01 = extract_const(to_app(eq[i].get())->get_arg(1), lvl + 1);
                    if (const00.size() == 0)
                        if (const01.size() > 0)
                            ret.insert(const01.begin(), const01.end());

                    if (const01.size() == 0)
                        if (const00.size() > 0)
                            ret.insert(const00.begin(), const00.end());

                    if (const00.size() > 0 && const01.size() > 0){
                        for (const auto& s0 : const00)
                            for (const auto& s1 : const01)
                                ret.insert(s0 + s1);
                    }
                }
            return ret;
        }
    }

    enode* theory_str::ensure_enode(expr* e) {
        context& ctx = get_context();
        if (!ctx.e_internalized(e)) {
            ctx.internalize(e, false);
        }
        enode* n = ctx.get_enode(e);
        ctx.mark_as_relevant(n);
        return n;
    }

    void theory_str::set_up_axioms(expr * ex) {
        ast_manager &m = get_manager();
        context &ctx = get_context();

        sort *ex_sort = m.get_sort(ex);
        sort *str_sort = u.str.mk_string_sort();
        sort *bool_sort = m.mk_bool_sort();

        family_id m_arith_fid = m.mk_family_id("arith");
        sort *int_sort = m.mk_sort(m_arith_fid, INT_SORT);

        create_pq();

        if (ex_sort == str_sort) {
            // set up basic string axioms
            enode *n = ctx.get_enode(ex);
            SASSERT(n);
            m_basicstr_axiom_todo.push_back(n);


            if (is_app(ex)) {
                app *ap = to_app(ex);
                if (u.str.is_concat(ap)) {
                    // if ex is a concat, set up concat axioms later
                    m_concat_axiom_todo.push_back(n);
                    // we also want to check whether we can eval this concat,
                    // in case the rewriter did not totally finish with this term
                    m_concat_eval_todo.push_back(n);
                } else if (u.str.is_length(ap)) {
                    // if the argument is a variable,
                    // keep track of this for later, we'll need it during model gen
                    expr *var = ap->get_arg(0);
                    app *aVar = to_app(var);
                    if (aVar->get_num_args() == 0 && !u.str.is_string(aVar)) {
                        input_var_in_len.insert(var);
                    }
                } else if (u.str.is_at(ap) || u.str.is_extract(ap) || u.str.is_replace(ap)) {
                    m_library_aware_axiom_todo.push_back(n);
                } else if (u.str.is_itos(ap)) {
                    TRACE("str", tout << __LINE__ << " found string-integer conversion term: " << mk_pp(ex, m) << std::endl;);
                    string_int_conversion_terms.push_back(ap);
                    m_library_aware_axiom_todo.push_back(n);
                    if (str_int_bound_expr == nullptr)
                        str_int_bound_expr = mk_int_var("StrIntBound");
                } else if (ap->get_num_args() == 0 && !u.str.is_string(ap)) {
                    // if ex is a variable, add it to our list of variables
                    variable_set.insert(ex);
                    ctx.mark_as_relevant(ex);
                    // this might help??
                    theory_var v = mk_var(n);
                    (void) v;
                }
            }
        } else if (ex_sort == bool_sort && !is_quantifier(ex)) {
            // set up axioms for boolean terms

            ensure_enode(ex);
            if (ctx.e_internalized(ex)) {
                enode *n = ctx.get_enode(ex);
                SASSERT(n);

                if (is_app(ex)) {
                    app *ap = to_app(ex);
                    if (u.str.is_prefix(ap) || u.str.is_suffix(ap) || u.str.is_contains(ap) || u.str.is_in_re(ap)) {
                        m_library_aware_axiom_todo.push_back(n);
                    }
                }
            } else {
                ENSURE(!search_started); // infinite loop prevention
                m_delayed_axiom_setup_terms.push_back(ex);
                return;
            }
        } else if (ex_sort == int_sort) {
            // set up axioms for integer terms
            enode *n = ensure_enode(ex);
            SASSERT(n);

            if (is_app(ex)) {
                app *ap = to_app(ex);
                if (u.str.is_index(ap)) {
                    m_library_aware_axiom_todo.push_back(n);
                } else if (u.str.is_stoi(ap)) {
                    string_int_conversion_terms.push_back(ap);
                    m_library_aware_axiom_todo.push_back(n);
                    if (str_int_bound_expr == nullptr)
                        str_int_bound_expr = mk_int_var("StrIntBound");
                }
            }
        }
        else if (is_app(ex)){
            app *ap = to_app(ex);
            if (u.re.is_star(ap)
                || u.re.is_plus(ap)
                || u.re.is_concat(ap)
                || u.re.is_union(ap)
                || u.re.is_complement(ap)
                || u.re.is_empty(ap)
                || u.re.is_full_char(ap)
                || u.re.is_intersection(ap)
                || u.re.is_range(ap)
                || u.re.is_to_re(ap)) {
            }
            else {
            }
        }
        else {
        }

        // if expr is an application, recursively inspect all arguments
        if (is_app(ex)) {
            app *term = to_app(ex);
            unsigned num_args = term->get_num_args();
            for (unsigned i = 0; i < num_args; i++) {
                set_up_axioms(term->get_arg(i));
            }
        }
    }

    void theory_str::create_pq(){
        if (p_bound_expr == nullptr)
            p_bound_expr = mk_int_var("PBound");
        if (q_bound_expr == nullptr)
            q_bound_expr = mk_int_var("QBound");
    }

    void theory_str::init_search_eh() {
        context & ctx = get_context();
        m_re2aut.reset();
        m_automata.reset();
        m_res.reset();
        startClock = clock();

        /*
         * Recursive descent through all asserted formulas to set up axioms.
         * Note that this is just the input structure and not necessarily things
         * that we know to be true or false. We're just doing this to see
         * which terms are explicitly mentioned.
         */
        unsigned nFormulas = ctx.get_num_asserted_formulas();
        for (unsigned i = 0; i < nFormulas; ++i) {
            expr * ex = ctx.get_asserted_formula(i);
            set_up_axioms(ex);
        }

        // this might be cheating but we need to make sure that certain maps are populated
        // before the first call to new_eq_eh()
        propagate();

        STRACE("str", tout << "search started" << std::endl;);
        search_started = true;
    }

    void theory_str::relevant_eh(app *const n) {
        (void) n;
    }

    void theory_str::assign_eh(bool_var v, const bool is_true) {
        // YFC: membership constraint goes here
        (void) v;
        (void) is_true;
        TRACE("str", tout << __FUNCTION__ << " assign: v" << v << " #" << get_context().bool_var2expr(v)->get_id()
                                          << " is_true: " << is_true << std::endl;);
        ast_manager &m = get_manager();
        context& ctx = get_context();
        expr* var =  ctx.bool_var2expr(v);
        if (u.str.is_prefix(var)){
            STRACE("str", tout << __FUNCTION__ << " prefix " << mk_pp(var, m) << " is_true: " << is_true << std::endl;);
        }
        else if (u.str.is_suffix(var)){
            STRACE("str", tout << __FUNCTION__ << " suffix " << mk_pp(var, m) << " is_true: " << is_true << std::endl;);
        }
        else if (u.str.is_in_re(var)){
            STRACE("str", tout << __FUNCTION__ << " regex in " << mk_pp(var, m) << " is_true: " << is_true << std::endl;);
            expr* n1 = to_app(var)->get_arg(0);
            expr* n2 = to_app(var)->get_arg(1);
            const str::expr_pair wi{expr_ref{n1, m}, expr_ref{n2, m}};
            if (is_true)
                membership_memo.push_back(wi);
            else
                non_membership_memo.push_back(wi);
        }
    }

    void theory_str::push_scope_eh() {
        STRACE("str", tout << __FUNCTION__ << ": at level " << m_scope_level << "/ eqLevel = " << uState.eqLevel << "; diseqLevel = " << uState.diseqLevel << std::endl;);
        STRACE("str", tout << __LINE__ <<  " current time used: " << ":  " << ((float)(clock() - startClock))/CLOCKS_PER_SEC << std::endl;);
        m_scope_level += 1;
        mful_scope_levels.push_scope();
        m_we_expr_memo.push_scope();
        m_wi_expr_memo.push_scope();
        membership_memo.push_scope();
        non_membership_memo.push_scope();
        m_trail_stack.push_scope();
        theory::push_scope_eh();
    }

    void theory_str::pop_scope_eh(const unsigned num_scopes) {
        STRACE("str", tout << __FUNCTION__ << ": at level " << m_scope_level << "/ eqLevel = " << uState.eqLevel << "; diseqLevel = " << uState.diseqLevel << std::endl;);
        m_scope_level -= num_scopes;

        if (m_scope_level < uState.eqLevel) {
            uState.reset_eq();
        }

        if (m_scope_level < uState.diseqLevel) {
            uState.reset_diseq();
        }
        context& ctx = get_context();
        for (int i = 0; i < ctx.get_unsat_core_size(); ++i) {
            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " unsat core " << i << mk_pp(ctx.get_unsat_core_expr(i), get_manager()) << std::endl;);
        }

//        if (mful_scope_levels.size() > 0) {
//            context& ctx = get_context();
//            expr_ref lastAssign = mful_scope_levels[(int)mful_scope_levels.size() - 1];
//
//            if (!ctx.e_internalized(lastAssign)) // it can be not internalized because its scope was pop.
//                uState.reset();
//            else {
//                literal l = ctx.get_literal(lastAssign);
//                STRACE("str", tout << __FUNCTION__ << " before get_assign_level  " << std::endl;);
//                int lastLevel = ctx.get_assign_level(l);
//                STRACE("str", tout << __FUNCTION__ << " after get_assign_level  " << lastLevel << std::endl;);
//                if (lastLevel < uState.z3_level) {
//                    STRACE("str", tout << __FUNCTION__ << " " << lastLevel << " vs " << uState.z3_level
//                                       << std::endl;);
//                    uState.reset();
//                }
//            }
//        }

        mful_scope_levels.pop_scope(num_scopes);
        m_we_expr_memo.pop_scope(num_scopes);
        m_wi_expr_memo.pop_scope(num_scopes);
        membership_memo.pop_scope(num_scopes);
        non_membership_memo.pop_scope(num_scopes);

        ptr_vector<enode> new_m_basicstr;
        for (ptr_vector<enode>::iterator it = m_basicstr_axiom_todo.begin(); it != m_basicstr_axiom_todo.end(); ++it) {
            enode * e = *it;
            TRACE("str", tout << "consider deleting " << mk_pp(e->get_owner(), get_manager())
                              << ", enode scope level is " << e->get_iscope_lvl()
                              << std::endl;);
            if (e->get_iscope_lvl() <= (unsigned)m_scope_level) {
                new_m_basicstr.push_back(e);
            }
        }
        m_basicstr_axiom_todo.reset();
        m_basicstr_axiom_todo = new_m_basicstr;

        m_trail_stack.pop_scope(num_scopes);
        STRACE("str", tout << "pop m_trail_stack " << num_scopes << " to " << m_scope_level << std::endl;);
        theory::pop_scope_eh(num_scopes);
    }

    void theory_str::reset_eh() {
        TRACE("str", tout << __FUNCTION__ << std::endl;);
        m_trail_stack.reset();
        m_basicstr_axiom_todo.reset();
        m_str_eq_todo.reset();
        m_concat_axiom_todo.reset();
        pop_scope_eh(get_context().get_scope_level());
    }

    final_check_status theory_str::final_check_eh() {
        TRACE("str", tout << __FUNCTION__ << ": at level " << m_scope_level << "/ eqLevel = " << uState.eqLevel << "; bound = " << uState.str_int_bound << std::endl;);
        ast_manager &m = get_manager();

        if (m_we_expr_memo.empty() && m_wi_expr_memo.empty()) {
            STRACE("str", tout << __LINE__ << " DONE" << std::endl;);
            return FC_DONE;
        }

//        if (propagate_concat()) {
//            TRACE("str", tout << "Resuming search due to axioms added by length propagation." << std::endl;);
//            newConstraintTriggered = true;
//            return FC_CONTINUE;
//        }

        if (!newConstraintTriggered && uState.reassertDisEQ && uState.reassertEQ) {
            STRACE("str", tout << __LINE__ << " DONE" << std::endl;);
            return FC_DONE;
        }
        else
            newConstraintTriggered = false;


        bool addAxiom;
        if (is_completed_branch(addAxiom)){
            if (addAxiom)
                return FC_CONTINUE;
            else
                return FC_DONE;
        }

        dump_assignments();

        if (eval_str_int()) {
            TRACE("str", tout << "Resuming search due to axioms added by eval_str_int." << std::endl;);
            newConstraintTriggered = true;
            return FC_CONTINUE;
        }

        std::set<std::pair<expr *, int>> non_fresh_vars;
        std::map<expr *, std::set<expr *>> eq_combination;
        init_final_check(non_fresh_vars, eq_combination);

        if (!review_starting_ending_combination(eq_combination)){
            negate_context();
            return FC_CONTINUE;
        }

        if (!is_notContain_consistent(eq_combination)) {
            TRACE("str", tout << "Resuming search due to axioms added by is_notContain_consistent check." << std::endl;);
            update_state();
            return FC_CONTINUE;
        }

        print_eq_combination(eq_combination);

//        if (implies_empty_str_from_notContain(eq_combination)) {
//            TRACE("str", tout << "Resuming search due to axioms added by implies_empty_str_from_notContain." << std::endl;);
//            newConstraintTriggered = true;
//            update_state();
//            return FC_CONTINUE;
//        }

        if (!parikh_image_check(eq_combination)){
            negate_context();
            return FC_CONTINUE;
        }


        if (handle_contain_family(eq_combination)){
            TRACE("str", tout << "Resuming search due to axioms added by handle_contain_family propagation." << std::endl;);
            update_state();
            return FC_CONTINUE;
        }

        if (handle_charAt_family(eq_combination)) {
            TRACE("str", tout << "Resuming search due to axioms added by handle_charAt_family propagation." << std::endl;);
            update_state();
            return FC_CONTINUE;
        }

        // enhancement: propagation of value/length information
        if (propagate_eq_combination(eq_combination)) {
            TRACE("str", tout << "Resuming search due to axioms added by eq_combination propagation." << std::endl;);
            update_state();
            return FC_CONTINUE;
        }

        refined_init_final_check(non_fresh_vars, eq_combination);

        if (underapproximation(eq_combination, non_fresh_vars)) {
            update_state();
            return FC_CONTINUE;
        }

        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " DONE." << std::endl;);
        return FC_DONE;
    }

    bool theory_str::eval_str_int(){
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << std::endl;);
        bool addedAxioms = false;
        for (unsigned i = 0; i < string_int_conversion_terms.size(); ++i) {
            app * ex = to_app(string_int_conversion_terms[i].get());
            if (u.str.is_stoi(ex)) {
                if (eval_str2int(ex)) {
                    addedAxioms = true;
                }
            } else if (u.str.is_itos(ex)) {
                if (eval_int2str(ex)) {
                    addedAxioms = true;
                }
            } else {
                UNREACHABLE();
            }
        }

        if (string_int_conversion_terms.size() > 0 && str_int_bound == rational(0)) {
            str_int_bound = rational(10);
            assert_axiom(createEqualOperator(get_bound_str_int_control_var(), mk_int(str_int_bound)));
            if (str_int_bound >= max_str_int_bound)
                impliedFacts.push_back(createEqualOperator(get_bound_str_int_control_var(), mk_int(str_int_bound)));
            addedAxioms = true;
            need_change = false;
            newConstraintTriggered = true;
        }
        else if (string_int_conversion_terms.size() > 0 && need_change && str_int_bound < max_str_int_bound){
            str_int_bound = str_int_bound * rational(2);
            assert_axiom(createEqualOperator(get_bound_str_int_control_var(), mk_int(str_int_bound)));
            if (str_int_bound >= max_str_int_bound)
                impliedFacts.push_back(createEqualOperator(get_bound_str_int_control_var(), mk_int(str_int_bound)));
            addedAxioms = true;
            need_change = false;
            newConstraintTriggered = true;
        }
        return addedAxioms;
    }

    /*
     * Check agreement between integer and string theories for the term a = (str.to-int S).
     * Returns true if axioms were added, and false otherwise.
     */
    bool theory_str::eval_str2int(app * a) {
        SASSERT(u.str.is_stoi(a));
        bool axiomAdd = false;
        context & ctx = get_context();
        ast_manager & m = get_manager();
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " " << mk_pp(a, m) << std::endl;);
        expr * S = a->get_arg(0);

        // check integer theory
        rational Ival;
        bool Ival_exists = get_arith_value(a, Ival);
        if (Ival_exists) {
            STRACE("str", tout << __LINE__ << "integer theory assigns " << mk_pp(a, m) << " = " << Ival.to_string() << std::endl;);
            // if that value is not -1, we can assert (str.to.int S) = Ival --> S = "Ival"
            if (!Ival.is_minus_one()) {
//                zstring Ival_str(Ival.to_string().c_str());
//                expr_ref premise(ctx.mk_eq_atom(a, m_autil.mk_numeral(Ival, true)), m);
//
//                expr_ref conclusion(ctx.mk_eq_atom(S, mk_string(Ival_str)), m);
//                expr_ref axiom(rewrite_implication(conclusion, premise), m);
//                if (!string_int_axioms.contains(axiom)) {
//                    string_int_axioms.insert(axiom);
//                    assert_axiom(axiom);
//                    m_trail_stack.push(insert_obj_trail<theory_str, expr>(string_int_axioms, axiom));
//                    axiomAdd = true;
//                }
            }
        } else {
            STRACE("str", tout << "integer theory has no assignment for " << mk_pp(a, m) << std::endl;);
        }

        bool S_hasEqcValue;
        expr * S_str = get_eqc_value(S, S_hasEqcValue);
        if (S_hasEqcValue) {
            zstring str;
            u.str.is_string(S_str, str);
            bool valid = true;
            rational convertedRepresentation(0);
            rational ten(10);
            if (str.length() == 0) {
                valid = false;
            } else {
                for (unsigned i = 0; i < str.length(); ++i) {
                    if (!('0' <= str[i] && str[i] <= '9')) {
                        valid = false;
                        break;
                    } else {
                        // accumulate
                        char digit = (int)str[i];
                        std::string sDigit(1, digit);
                        int val = atoi(sDigit.c_str());
                        convertedRepresentation = (ten * convertedRepresentation) + rational(val);
                    }
                }
            }

            // TODO this duplicates code a bit, we can simplify the branch on "conclusion" only
            if (valid) {
                // return actuan value
                expr_ref premise(ctx.mk_eq_atom(S, mk_string(str)), m);
                expr_ref conclusion(ctx.mk_eq_atom(a, m_autil.mk_numeral(convertedRepresentation, true)), m);
                expr_ref axiom(rewrite_implication(premise, conclusion), m);
                if (!string_int_axioms.contains(axiom)) {
                    string_int_axioms.insert(axiom);
                    assert_axiom(axiom);
                    m_trail_stack.push(insert_obj_trail<theory_str, expr>(string_int_axioms, axiom));
                    axiomAdd = true;
                }
            }
            else {
                // return -1
                expr_ref premise(ctx.mk_eq_atom(S, mk_string(str)), m);
                expr_ref conclusion(ctx.mk_eq_atom(a, m_autil.mk_numeral(rational::minus_one(), true)), m);
                expr_ref axiom(rewrite_implication(premise, conclusion), m);
                if (!string_int_axioms.contains(axiom)) {
                    string_int_axioms.insert(axiom);
                    assert_axiom(axiom);
                    m_trail_stack.push(insert_obj_trail<theory_str, expr>(string_int_axioms, axiom));
                    axiomAdd = true;
                }
            }
        }
        else {
            expr* eq_node = nullptr;
            int val = eval_invalid_str2int(S, eq_node);
            if (val == -1) {
                expr_ref premise(ctx.mk_eq_atom(S, eq_node), m);
                expr_ref conclusion(ctx.mk_eq_atom(a, m_autil.mk_numeral(rational::minus_one(), true)), m);
                expr_ref axiom(rewrite_implication(premise, conclusion), m);
                if (!string_int_axioms.contains(axiom)) {
                    string_int_axioms.insert(axiom);
                    assert_axiom(axiom);
                    m_trail_stack.push(insert_obj_trail<theory_str, expr>(string_int_axioms, axiom));
                    axiomAdd = true;
                }
            }
        }

        return axiomAdd;
    }

    int theory_str::eval_invalid_str2int(expr* e, expr* &eq_node){
        ast_manager & m = get_manager();
        expr_ref_vector eqs(m);
        collect_eq_nodes(e, eqs);
        for (const auto& n : eqs){
            if (u.str.is_concat(n)) {
                ptr_vector<expr> nodes;
                get_nodes_in_concat(n, nodes);
                zstring val;
                for (const auto& nn : nodes)
                    if (u.str.is_string(nn, val)) {
                        for (int i = 0; i < val.length(); ++i)
                            if (val[i] < '0' || val[i] > '9') {
                                eq_node = n;
                                return -1;
                            }
                    }
            }
        }
        return 0;
    }

    bool theory_str::eval_int2str(app * a) {
        bool axiomAdd = false;
        context & ctx = get_context();
        ast_manager & m = get_manager();
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " " << mk_pp(a, m) << std::endl;);
        expr * N = a->get_arg(0);

        // check string theory
        bool Sval_expr_exists;
        expr * Sval_expr = get_eqc_value(a, Sval_expr_exists);
        if (Sval_expr_exists) {
            zstring Sval;
            u.str.is_string(Sval_expr, Sval);
            STRACE("str", tout << "string theory assigns \"" << mk_pp(a, m) << " = " << Sval << "\n";);
            // empty string --> integer value < 0
            if (Sval.empty()) {
                // ignore this. we should already assert the axiom for what happens when the string is ""
            } else {
                // nonempty string --> convert to correct integer value, or disallow it
                rational convertedRepresentation(0);
                rational ten(10);
                bool conversionOK = true;
                for (unsigned i = 0; i < Sval.length(); ++i) {
                    char digit = (int)Sval[i];
                    if (isdigit((int)digit)) {
                        std::string sDigit(1, digit);
                        int val = atoi(sDigit.c_str());
                        convertedRepresentation = (ten * convertedRepresentation) + rational(val);
                    } else {
                        // not a digit, invalid
                        TRACE("str", tout << "str.to-int argument contains non-digit character '" << digit << "'" << std::endl;);
                        conversionOK = false;
                        break;
                    }
                }

                if (conversionOK) {
                    expr_ref premise(ctx.mk_eq_atom(a, mk_string(Sval)), m);
                    expr_ref conclusion(ctx.mk_eq_atom(N, m_autil.mk_numeral(convertedRepresentation, true)), m);
                    expr_ref axiom(rewrite_implication(premise, conclusion), m);
                    if (!string_int_axioms.contains(axiom)) {
                        string_int_axioms.insert(axiom);
                        assert_axiom(axiom);
                        m_trail_stack.push(insert_obj_trail<theory_str, expr>(string_int_axioms, axiom));
                        axiomAdd = true;
                    }
                } else {
                    expr_ref axiom(m.mk_not(ctx.mk_eq_atom(a, mk_string(Sval))), m);
                    // always assert this axiom because this is a conflict clause
                    assert_axiom(axiom);
                    axiomAdd = true;
                }
            }
        } else {
            expr* eq_node = nullptr;
            int val = eval_invalid_str2int(a, eq_node);
            if (val == -1) {
                expr_ref premise(ctx.mk_eq_atom(a, eq_node), m);
                expr_ref conclusion(ctx.mk_eq_atom(a, m_autil.mk_numeral(rational::minus_one(), true)), m);
                expr_ref axiom(rewrite_implication(premise, conclusion), m);
                if (!string_int_axioms.contains(axiom)) {
                    string_int_axioms.insert(axiom);
                    assert_axiom(axiom);
                    m_trail_stack.push(insert_obj_trail<theory_str, expr>(string_int_axioms, axiom));
                    axiomAdd = true;
                }
            }
        }
        return axiomAdd;
    }

    /*
     * sigmaDomain: all letters appearing in concats
     * importantVar: variables in disequalities: x != y, x does not contain y
     * eq_combination: all equalities over variable
     */

    void theory_str::init_final_check(
            std::set<std::pair<expr *, int>> &non_fresh_vars,
            std::map<expr *, std::set<expr *>> &eq_combination){

        sigmaDomain = collect_char_domain_from_concat();
        non_fresh_vars = collect_important_vars();
        analyze_upper_bound_str_int();
        std::map<expr*, std::set<expr*>> _premises;
        std::set<expr*> subNodes;
        eq_combination = normalize_eq(_premises, subNodes, non_fresh_vars);
    }

    void theory_str::analyze_bound_str_int(){
        rational bound = str_int_bound;
        for (const auto& num : int_string_vars){
            rational ub, lb;
            if (upper_num_bound(num, ub)){
                rational log10 = log_10(ub);
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " upper_num_bound " << ub << " log10 " << log10 << std::endl;);
                if (log10 > bound)
                    bound = log10;
            }
            else {
                if (lower_num_bound(num, lb)){
                    rational log10 = log_10(lb);
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " lower_num_bound " << ub << " log10 " << log10 << std::endl;);
                    if (log10 > bound)
                        bound = log10;
                }
            }
        }
        str_int_bound = bound;
    }

    bool theory_str::analyze_upper_bound_str_int(){
        rational bound = str_int_bound;
        bool all_upper_bounds = true;
        for (const auto& num : int_string_vars){
            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " upper_num_bound " << mk_pp(num, get_manager()) << std::endl;);
            rational ub, lb;
            if (upper_num_bound(num, ub)){
                rational log10 = log_10(ub);
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " upper_num_bound " << ub << " log10 " << log10 << std::endl;);
                if (log10 > bound)
                    bound = log10;
            }
            else {
                all_upper_bounds = false;
                if (lower_num_bound(num, lb)){
                    rational log10 = log_10(lb);
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " lower_num_bound " << ub << " log10 " << log10 << std::endl;);
                    if (log10 > bound)
                        bound = log10;
                }
            }
        }
        return all_upper_bounds;
    }

    rational theory_str::log_10(rational n){
        rational num(1);
        rational one(1);
        rational ten(10);
        rational zero(0);
        if (n < zero){
            return num;
        }
        else {
            while (n > one){
                n = n / ten;
                num = num + 1;
            }
            return num;
        }
    }

    rational theory_str::ten_power(rational n){
        SASSERT(n >= rational(0));
        rational num(1);
        rational i(1);
        rational ten(10);
        for (; i <= n; i = i + 1){
            num = num * ten;
        }
        return num;
    }

    /*
     * sigmaDomain: all letters appearing in eq_combination
     * importantVar: variables in disequalities: x != y, x does not contain y
     * eq_combination: all equalities over variable
     */
    void theory_str::refined_init_final_check(
            std::set<std::pair<expr *, int>> &non_fresh_vars,
            std::map<expr *, std::set<expr *>> &eq_combination){
        sigmaDomain = collect_char_domain_from_eqmap(eq_combination);

        std::set<expr*> notImportant;
        refine_important_vars(non_fresh_vars, notImportant, eq_combination);
        print_eq_combination(eq_combination);

        std::map<expr*, std::set<expr*>> _premises;
        std::set<expr*> subNodes;
        eq_combination = normalize_eq(_premises, subNodes, non_fresh_vars);
        refine_not_contain_vars(non_fresh_vars, eq_combination);
    }

    void theory_str::refine_not_contain_vars(
            std::set<std::pair<expr *, int>> &non_fresh_vars,
            std::map<expr *, std::set<expr *>> eq_combination){
        TRACE("str", tout << __LINE__ << " " << __FUNCTION__ << std::endl;);
        ast_manager & m = get_manager();
        for (const auto& nn : non_fresh_vars)
            STRACE("str", tout << __LINE__ << "\t "<< mk_pp(nn.first, m) << ": " << nn.second << std::endl;);

        expr* contain = nullptr;
        std::set<expr *> not_imp;
        std::set<expr *> mustbe_imp;
        for (const auto &wi : m_wi_expr_memo) {
            if (!u.str.is_empty(wi.second.get()) && !u.str.is_empty(wi.first.get())) {
                expr* lhs = wi.first.get();
                expr* rhs = wi.second.get();
                zstring needle;
                if (is_contain_equality(lhs, contain) && u.str.is_string(contain, needle) && !is_trivial_contain(needle)) {
                    expr_ref_vector vec(m);
                    collect_eq_nodes(rhs, vec);
                    if (is_not_important(rhs, needle, eq_combination)){
                        if (not_imp.find(rhs) == not_imp.end())
                            for (const auto& e : vec)
                                not_imp.insert(e);
                    }
                    else {
                        for (const auto& e : vec) {
                            mustbe_imp.insert(e);
                            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " must be nonfresh " << mk_pp(e, m) << " " << needle << std::endl;);
                        }
                    }
                }
                else if (is_contain_equality(rhs, contain) && u.str.is_string(contain, needle) && !is_trivial_contain(needle)) {
                    expr_ref_vector vec(m);
                    collect_eq_nodes(lhs, vec);
                    if (is_not_important(lhs, needle, eq_combination)){
                        if (not_imp.find(rhs) == not_imp.end())
                            for (const auto& e : vec)
                                not_imp.insert(e);
                    }
                    else {
                        for (const auto& e : vec) {
                            mustbe_imp.insert(e);
                            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << "  must be nonfresh " << mk_pp(e, m) << " " << needle << std::endl;);
                        }
                    }
                }
                else {
                }

            }
        }

        std::set<std::pair<expr *, int>> tmp;
        for (const auto& p : non_fresh_vars) {
            if (not_imp.find(p.first) != not_imp.end() &&
                p.second == -1 &&
                mustbe_imp.find(p.first) == mustbe_imp.end()) {
                continue;
            }
            else {
                tmp.insert(p);
            }
        }

        non_fresh_vars.clear();
        non_fresh_vars = tmp;

        TRACE("str", tout << __LINE__ << " " << __FUNCTION__ << std::endl;);
        for (const auto& nn : non_fresh_vars)
            STRACE("str", tout << "\t "<< mk_pp(nn.first, m) << ": " << nn.second << std::endl;);
    }

    bool theory_str::is_not_important(expr* haystack, zstring needle, std::map<expr *, std::set<expr *>> eq_combination){
        ast_manager & m = get_manager();
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(haystack, m) << " " << needle << std::endl;);
        for (const auto& eq : eq_combination) {
            if (eq.second.size() > 1 && appear_in_eq(haystack, needle, eq.second)) {
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " appear_in_eq: " << mk_pp(haystack, m) << " " << needle << std::endl;);
                if (!appear_in_other_eq(eq.first, needle, eq_combination)) {
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " !appear_in_other_eq: " << mk_pp(haystack, m) << " " << needle << std::endl;);
                    return true;
                }
                else
                    return false;
            }
        }
        return false;
    }

    bool theory_str::appear_in_eq(expr* haystack, zstring needle, std::set<expr *> s) {
        ast_manager & m = get_manager();
        for (const auto& n : s)
            if (u.str.is_concat(n)){
                ptr_vector<expr> nodes;
                get_nodes_in_concat(n, nodes);
                if (eq_in_list(haystack, nodes) && nodes.contains(u.str.mk_string(needle))) {
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(haystack, m) << " " << needle << " in " << mk_pp(n, m) << std::endl;);
                    // compare with other elements in s
                    for (const auto& nn : s)
                        if (nn != n) {
                            // shorten two parts
                            if (!can_omit(n, nn, needle)){
                                return false;
                            }
                        }
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(haystack, m) << " " << needle << " in " << mk_pp(n, m) << std::endl;);
                    return true;
                }
            }
        return false;
    }

    bool theory_str::eq_in_list(expr* n, ptr_vector<expr> nodes) {
        expr_ref_vector eqs(get_manager());
        collect_eq_nodes(n, eqs);
        for (const auto& nn : eqs)
            if (nodes.contains(nn))
                return true;
        return false;
    }

    bool theory_str::can_omit(expr* lhs, expr* rhs, zstring needle){
        ast_manager & m = get_manager();
        ptr_vector<expr> lhsVec;
        get_nodes_in_concat(lhs, lhsVec);

        ptr_vector<expr> rhsVec;
        get_nodes_in_concat(rhs, rhsVec);

        /* cut prefix */
        int prefix = -1;
        for (int i = 0; i < (int)std::min(lhsVec.size(), rhsVec.size()); ++i)
            if (are_equal_exprs(lhsVec[i], rhsVec[i])) {
                prefix = i;
            }
            else
                break;

        prefix = prefix + 1;

        int suffix = 0;
        for (int i = 0; i < (int)std::min(lhsVec.size(), rhsVec.size()); ++i)
            if (are_equal_exprs(lhsVec[lhsVec.size() - 1 - i], rhsVec[rhsVec.size() - 1 - i])) {
                suffix = i;
            }
            else
                break;

        zstring val;
        for (int i = prefix; i < rhsVec.size() - suffix; ++i)
            if (u.str.is_string(rhsVec[i], val))
                if (val.contains(needle) || needle.contains(val))
                    return false;

        return true;
    }

    bool theory_str::appear_in_other_eq(expr* root, zstring needle, std::map<expr *, std::set<expr *>> eq_combination) {
        for (const auto& eq : eq_combination)
            if (eq.first != root) {
                for (const auto& n : eq.second) {
                    ptr_vector<expr> nodes;
                    get_nodes_in_concat(n, nodes);
                    zstring val;
                    for (const auto& nn : nodes)
                        if (u.str.is_string(nn, val))
                            if (val.contains(needle) || needle.contains(val))
                                return true;
                }
            }
        return false;
    }

    /*
     * two branches are equal if SAT core of a branch is TRUE in the other branch
     */
    bool theory_str::is_completed_branch(bool &addAxiom){
        ast_manager & m = get_manager();
        addAxiom = false;
        expr_ref_vector guessedEqs(m), guessedDisEqs(m);
        fetch_guessed_exprs_with_scopes(guessedEqs, guessedDisEqs);

        const str::state &root = build_state_from_memo();

        if (at_same_eq_state(uState) && at_same_diseq_state(root, uState.currState)) {
            if (uState.reassertDisEQ && uState.reassertEQ) {
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " DONE eqLevel = " << uState.eqLevel << "; diseqLevel = " << uState.diseqLevel << std::endl;);
                return true;
            }
            else {
                if (!uState.reassertEQ){
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " reassertEQ = false " << uState.eqLevel << std::endl;);
                    underapproximation_cached();
                    uState.eqLevel = get_actual_trau_lvl();
                }

                if (!uState.reassertDisEQ){
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " reassertDisEQ = false " << uState.diseqLevel << std::endl;);
                    handle_diseq(true);
                    uState.diseqLevel = get_actual_trau_lvl();
                }

                uState.reassertDisEQ = true;
                uState.reassertEQ = true;

                addAxiom = true;
                return true;
            }
        }
        else {
            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " completed state " << completedStates.size() << std::endl;);
            // check all completed state, skip the last one
            for (int i = 0; i < (int)completedStates.size() - 1; ++i){
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " comparing with completed state " << uState.eqLevel << std::endl;);
                if (at_same_eq_state(completedStates[i]) && at_same_diseq_state(root, completedStates[i].currState)){
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " eq with completed state " << uState.eqLevel << std::endl;);
                    return true;
                }
            }
        }
        return false;
    }

    /*
     *
     */
    void theory_str::update_state(){
        uState.eqLevel = get_actual_trau_lvl();
        uState.diseqLevel = get_actual_trau_lvl();
        uState.reassertEQ = true;
        uState.reassertDisEQ = true;
    }

    /*
     * a . b = c .d && |a| = |b| --> a = b
     */
    bool theory_str::propagate_eq_combination(std::map<expr *, std::set<expr *>> eq_combination){
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << std::endl;);
        ast_manager & m = get_manager();
        expr_ref_vector guessedEqs(m), guessedDisEqs(m);
        fetch_guessed_exprs_with_scopes(guessedEqs, guessedDisEqs);
        fetch_guessed_core_exprs(eq_combination, guessedEqs, guessedDisEqs);
        expr* coreExpr = createAndOperator(guessedEqs);


        expr_ref_vector impliedEqualites(m);
        for (const auto &c : eq_combination) {
            std::vector<expr*> tmp;
            for (const auto& e : c.second)
                tmp.push_back(e);

            // compare with the root
            if (c.second.find(c.first) == c.second.end())
                tmp.push_back(c.first);

            for (int i = 0; i < tmp.size(); ++i)
                for (int j = i + 1; j < tmp.size(); ++j) {
                    if (!propagate_equality(tmp[i], tmp[j], impliedEqualites)){
                        // found some inconsistence
                        return true;
                    }
                }
        }
        if (impliedEqualites.size() > 0){
            expr* tmp = createAndOperator(impliedEqualites);
            expr* assertingExpr = rewrite_implication(coreExpr, tmp);
            assert_axiom(tmp);
            impliedFacts.push_back(assertingExpr);
            return true;
        }
        else
            return false;
    }

    /*
     * check all ~contain
     *
     * x does not contain A, means
     *      x = y . z --> y , z cannot contain A
     *      t = replace (y, B, C) --> t cannot contain A
     *
     * t, y, z are called related variables of x
     *
     */
    bool theory_str::is_notContain_consistent(std::map<expr *, std::set<expr *>> eq_combination){
        expr_ref_vector eqList(get_manager()), diseqList(get_manager());
        fetch_guessed_exprs_with_scopes(eqList, diseqList);
        fetch_guessed_core_exprs(eq_combination, eqList, diseqList);
        expr* core = createAndOperator(eqList);

        for (const auto &wi : m_wi_expr_memo) {
            if (!u.str.is_empty(wi.second.get()) && !u.str.is_empty(wi.first.get())) {
                expr* lhs = wi.first.get();
                expr* rhs = wi.second.get();

                if (!is_notContain_consistent(lhs, rhs, core))
                    return false;
            }
        }
        return true;
    }

    /*
     * x does not contain A, means
     *      x = y . z --> y , z cannot contain A
     *      t = replace (y, B, C) --> t cannot contain A
     *
     * t, y, z are called related variables of x
     */
    bool theory_str::is_notContain_consistent(expr* lhs, expr* rhs, expr* core){
        ast_manager & m = get_manager();
        expr* contain = nullptr;
        expr_ref conclusion(createEqualOperator(lhs, rhs), m);
        expr* simplifiedLhs = simplify_concat(lhs);
        expr* simplifiedRhs = simplify_concat(rhs);
        if (is_contain_equality(simplifiedLhs, contain)) {
            zstring value;
            if (u.str.is_string(contain, value) && !is_trivial_contain(value))
                return is_notContain_const_consistent(rhs, value, conclusion);
        }
        else if (is_contain_equality(simplifiedRhs, contain)) {
            zstring value;
            if (u.str.is_string(contain, value) && !is_trivial_contain(value))
                return is_notContain_const_consistent(lhs, value, conclusion);
        }
        return true;
    }

    /*
     * x does not contain A, means
     *      x = y . z --> y , z cannot contain A
     *      t = replace (y, B, C) --> t cannot contain A
     *
     * t, y, z are called related variables of x
     */
    bool theory_str::is_notContain_const_consistent(expr* lhs, zstring containKey, expr_ref conclusion){
        // find all related nodes
        ast_manager & m = get_manager();
        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " contains(" << mk_pp(lhs, m) << ", " << containKey << ")" << std::endl;);
        expr_ref_vector relatedVars = check_contain_related_vars(lhs, containKey);
        if (relatedVars.size() > 0){
            expr_ref_vector eqs(m), diseqs(m);
            fetch_guessed_exprs_with_scopes(eqs);
            fetch_related_exprs(relatedVars, eqs);

            // implies that x contains A if needed, means negating the context
            expr_ref toAssert(rewrite_implication(createAndOperator(eqs), conclusion), m);
            assert_axiom(toAssert);
            impliedFacts.push_back(toAssert);
            return false;
        }
        return true;
    }

    /*
     * check all eq
     *
     * x = y . z
     * x = t . "A"
     * z does not contain "A"
     *
     * z is empty
     *
     */
    bool theory_str::implies_empty_str_from_notContain(std::map<expr *, std::set<expr *>> eq_combination){
        ast_manager & m = get_manager();
        expr_ref_vector ret(m);
        for (const auto& v : eq_combination) {
            for (const auto& e : v.second){
                // if last expr is const
                ptr_vector<expr> nodes;
                get_nodes_in_concat(e, nodes);
                if (u.str.is_string(nodes[nodes.size() - 1])){
                    // check all other eq
                    ret.append(implies_empty_tail_str_from_notContain(v.second, nodes[nodes.size() - 1], e));
                }

                if (u.str.is_string(nodes[0])){
                    // check all other eq
                    ret.append(implies_empty_start_str_from_notContain(v.second, nodes[0], e));
                }
            }
        }
        if (ret.size() > 0){
            expr_ref_vector eqList(m), diseqList(m);
            fetch_guessed_exprs_with_scopes(eqList, diseqList);

            fetch_guessed_core_exprs(eq_combination, eqList, diseqList);
            expr* asserting = rewrite_implication(createAndOperator(eqList), createAndOperator(ret));
//            assert_axiom(createAndOperator(ret));
            impliedFacts.push_back(asserting);
            negate_context();
            return true;
        }
        return false;
    }

    expr_ref_vector theory_str::implies_empty_tail_str_from_notContain(std::set<expr *> v, expr* key, expr* lhs){
        ast_manager & m = get_manager();
        expr_ref_vector ret(m);
        for (const auto& s : v){
            ptr_vector<expr> nodes;
            get_nodes_in_concat(s, nodes);
            for (int i = (int)nodes.size() - 1; i >= 0; --i){
                expr* real_haystack = nullptr;
                if (does_contain(nodes[i], key, real_haystack)){
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(nodes[i], m) << " " << mk_pp(key, m) << " " <<  mk_pp(real_haystack, m) << std::endl;);
                    zstring emptystr = "";
                    app* a = u.str.mk_contains(real_haystack, key);
                    enode* tmpenode = ensure_enode(a);
                    if (!are_equal_exprs(u.str.mk_string(emptystr), contain_split_map[tmpenode].second->get_owner())) {
                        expr_ref_vector ands(m);
//                        ands.push_back(createEqualOperator(lhs, s));
                        if (real_haystack != nodes[i])
                            ands.push_back(createEqualOperator(nodes[i], real_haystack));
                        ands.push_back(contain_pair_bool_map[std::make_pair(real_haystack, key)]);
                        rational len;
                        if (lower_bound(contain_split_map[tmpenode].second->get_owner(), len) && len.get_int64() > 0)
                            ret.push_back(rewrite_implication(createAndOperator(ands),
                                    createEqualOperator(u.str.mk_string(emptystr), contain_split_map[tmpenode].second->get_owner())));
                        return ret;
                    }
                }

                if (not_contain(nodes[i], key, real_haystack)){
                    zstring emptystr = "";
                    if (!are_equal_exprs(nodes[i], u.str.mk_string(emptystr))) {
                        expr_ref_vector ands(m);
//                        ands.push_back(createEqualOperator(lhs, s));
                        if (real_haystack != nodes[i])
                            ands.push_back(createEqualOperator(nodes[i], real_haystack));

                        app* a = u.str.mk_contains(real_haystack, key);
                        ensure_enode(a);
                        SASSERT(contain_pair_bool_map.contains(std::make_pair(real_haystack, key)));
                        ands.push_back(mk_not(m, contain_pair_bool_map[std::make_pair(real_haystack, key)]));
                        rational len;
                        if (lower_bound(nodes[i], len) && len.get_int64() > 0)
                            ret.push_back(rewrite_implication(createAndOperator(ands), createEqualOperator(nodes[i], u.str.mk_string(emptystr))));
                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(nodes[i], m) << " must be empty" << std::endl;);
                        return ret;
                    }

                }
                else
                    break;
            }
        }
        return ret;
    }

    expr_ref_vector theory_str::implies_empty_start_str_from_notContain(std::set<expr *> v, expr* key, expr* lhs){
        ast_manager & m = get_manager();
        expr_ref_vector ret(m);
        for (const auto& s : v){
            ptr_vector<expr> nodes;
            get_nodes_in_concat(s, nodes);

            for (int i = 0; i < (int)nodes.size(); ++i){
                expr* real_haystack = nullptr;
                 if (does_contain(nodes[i], key, real_haystack)){
                     STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << std::endl;);
                    zstring tmp = "";
                    app* a = u.str.mk_contains(real_haystack, key);
                    enode* tmpenode = ensure_enode(a);
                    rational len;
                    if (!get_len_value(contain_split_map[tmpenode].second->get_owner(), len) || len.get_int64() != 0) {

                        expr_ref_vector ands(m);
//                        ands.push_back(createEqualOperator(lhs, s));
                        if (real_haystack != nodes[i])
                            ands.push_back(createEqualOperator(nodes[i], real_haystack));
                        ands.push_back(contain_pair_bool_map[std::make_pair(real_haystack, key)]);
                        rational len;
                        if (lower_bound(contain_split_map[tmpenode].first->get_owner(), len) && len.get_int64() > 0)
                            ret.push_back(rewrite_implication(createAndOperator(ands),
                                                           createEqualOperator(u.str.mk_string(tmp), contain_split_map[tmpenode].first->get_owner())));
                         return ret;
                    }
                }

                if (not_contain(nodes[i], key, real_haystack)){
                    zstring tmp = "";
                    rational len;
                    if (!get_len_value(nodes[i], len) || len.get_int64() != 0) {

                        expr_ref_vector ands(m);
//                        ands.push_back(createEqualOperator(lhs, s));
                        if (real_haystack != nodes[i])
                            ands.push_back(createEqualOperator(nodes[i], real_haystack));

                        SASSERT(contain_pair_bool_map.contains(std::make_pair(real_haystack, key)));
                        ands.push_back(mk_not(m, contain_pair_bool_map[std::make_pair(real_haystack, key)]));
                        rational len;
                        if (lower_bound(nodes[i], len) && len.get_int64() > 0)
                            ret.push_back(rewrite_implication(createAndOperator(ands), createEqualOperator(nodes[i], u.str.mk_string(tmp))));
                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(nodes[i], get_manager()) << " must be empty" << std::endl;);
                        return ret;
                    }

                }
                else
                    break;
            }
        }
        return ret;
    }

    /*
     * check all eqs
     *
     * maximum of some letters
     * x = t . "A"
     * z does not contain "A"
     *
     * z is empty
     *
     */
    bool theory_str::parikh_image_check(std::map<expr *, std::set<expr *>> eq_combination){
        ast_manager & m = get_manager();
        expr_ref_vector ret(m);
        std::map<zstring, int> maxImages;
        for (const auto& v : eq_combination) {
            for (const auto& e : v.second){
                expr_ref_vector constList(m);
                if (get_image_in_expr(e, constList)){
                    for (const auto& nn : v.second)
                        if (nn != e){
                            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << std::endl;);
                            int cnt = get_lower_bound_image_in_expr(nn, constList[0].get());
                            if (cnt > constList.size())
                                return false;
                        }
                }
                constList.reset();
                not_contain_string_in_expr(e, constList);
                for (const auto& s : constList){

                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(v.first, get_manager()) << " does not contain " << mk_pp(s, get_manager()) << std::endl;);
                    for (const auto& nn : v.second)
                        if (nn != e){
                            int cnt = get_lower_bound_image_in_expr(nn, s);
                            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << std::endl;);
                            if (cnt > 0)
                                return false;
                        }
                }

                zstring value;
                if (u.str.is_string(e, value)){
                    for (const auto& nn : v.second){
                        if (!can_match(value, nn)) {
                            assert_axiom(mk_not(m, createEqualOperator(e, nn)));
                            return false;
                        }
                    }
                }

                for (const auto& ee : v.second)
                    if (e != ee){
                        if (!equal_parikh(e, ee))
                            return false;
                    }

                for (const auto& ee : v.second)
                    if (e != ee){
                        if (!same_prefix_same_parikh(e, ee))
                            return false;
                    }
            }
        }
        return true;
    }

    bool theory_str::same_prefix_same_parikh(expr* nn, expr* n){
        ptr_vector<expr> nodes;
        get_nodes_in_concat(n, nodes);

        ptr_vector<expr> nnodes;
        get_nodes_in_concat(nn, nnodes);

        ptr_vector<expr> lhs;
        ptr_vector<expr> rhs;
        std::map<char, int> img_lhs;
        std::map<char, int> img_rhs;
        int diff_len = 0;
        for (int i = 0; i < std::max(nodes.size(), nnodes.size()); ++i){
            zstring val;
            bool remove_lhs = false;
            bool remove_rhs = false;
            if (i < nodes.size()) {
                if (u.str.is_string(nodes[i], val)) {
                    get_parikh_from_strs(val, img_lhs);
                    diff_len += val.length();
                    remove_lhs = true;
                } else {
                    // try to remove
                    if (rhs.contains(nodes[i])) {
                        rhs.erase(nodes[i]);
                        remove_lhs = true;
                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << i << std::endl;);
                    }
                }
            }

            if (i < nnodes.size()) {
                if (u.str.is_string(nnodes[i], val)) {
                    get_parikh_from_strs(val, img_rhs);
                    diff_len -= val.length();
                    remove_rhs = true;
                } else {
                    // try to remove
                    if (lhs.contains(nnodes[i])) {
                        lhs.erase(nnodes[i]);
                        remove_rhs = true;
                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << i << std::endl;);
                    }
                    // if cannot remove
                }
            }

            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << i << " " << lhs.size() << " " << rhs.size()<< " " << diff_len << std::endl;);

            if (lhs.size() == 0 && rhs.size() == 0 && diff_len == 0) {
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << i << std::endl;);
                if (!eq_parikh(img_lhs, img_rhs))
                    return false;
            }
            if (i < nodes.size() && !remove_lhs)
                lhs.push_back(nodes[i]);
            if (i < nnodes.size() && !remove_rhs)
                rhs.push_back(nnodes[i]);
        }

        return true;
    }

    bool theory_str::equal_parikh(expr* nn, expr* n){
        ptr_vector<expr> nodes;
        get_nodes_in_concat(n, nodes);

        ptr_vector<expr> nnodes;
        get_nodes_in_concat(nn, nnodes);

        ptr_vector<expr> remain_vector;
        // remove common vars
        for (const auto& e : nodes)
            if (nnodes.contains(e)) {
                nnodes.erase(e);
            }
            else
                remain_vector.push_back(e);

        std::map<char, int> parikh_n;
        std::map<char, int> parikh_nn;

        // eval parikh
        zstring val;
        for (const auto& e : nnodes)
            if (!u.str.is_string(e, val)) {
                return true;
            }
            else {
                get_parikh_from_strs(val, parikh_nn);
            }

        for (const auto& e : remain_vector)
            if (!u.str.is_string(e, val)) {
                return true;
            }
            else {
                get_parikh_from_strs(val, parikh_n);
            }

        // only const left
        for (const auto& e : nnodes)
            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " lhs: " << mk_pp(e, get_manager()) << std::endl;);

        for (const auto& e : remain_vector)
            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " rhs: " << mk_pp(e, get_manager()) << std::endl;);

        // check two parikhs
        if (!eq_parikh(parikh_n, parikh_nn))
            return false;

        // special case for a . x = x . a
//        if (nnodes.size() == 1 && remain_vector.size() == 1){
//            u.str.is_string(nnodes[0], val);
//            zstring lhs = val + val;
//
//            zstring rhs;
//            u.str.is_string(remain_vector[0], rhs);
//            if (!lhs.contains(rhs))
//                return false;
//        }

        return true;
    }

    void theory_str::get_parikh_from_strs(zstring s, std::map<char, int> &img){
        for (int i = 0; i < s.length(); ++i)
            img[s[i]]++;
    }

    bool theory_str::eq_parikh(std::map<char, int> lhs, std::map<char, int> rhs){
        for (const auto& ch : lhs)
            if (rhs[ch.first] != ch.second)
                return false;
        return true;
    }

    bool theory_str::can_match(zstring value, expr* n){
        ptr_vector<expr> nodes;
        get_nodes_in_concat(n, nodes);
        for (const auto& nn : nodes){
            zstring v;
            if (u.str.is_string(nn, v)) {
                if (!value.contains(v)) {
                    return false;
                }
                else {
                    value = value.extract(0, value.indexof(v, 0)) +
                            value.extract(value.indexof(v, 0) + v.length(), value.length() - value.indexof(v, 0) - v.length());
                }
            }
        }
        return true;
    }

    void theory_str::not_contain_string_in_expr(expr* n, expr_ref_vector &constList){
        context &ctx = get_context();
        ptr_vector<expr> nodes;
        get_nodes_in_concat(n, nodes);
        for (const auto& nn : nodes){
            if (!u.str.is_string(nn)) {
                expr_ref_vector eqs(get_manager());
                collect_eq_nodes(nn, eqs);

                for (const auto &c : contain_pair_bool_map) {
                    if (eqs.contains(c.get_key1())) {
                        switch (ctx.get_assignment(c.get_value())){
                            case l_true:
                                break;
                            case l_false:
                                if (agree_on_not_contain(n, c.get_key2()))
                                    constList.push_back(c.get_key2());
                                break;
                            case l_undef:
                                break;
                        }
                    }
                }
            }
        }
    }

    bool theory_str::agree_on_not_contain(expr* n, expr* key){
//        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " checking if " << mk_pp(n, get_manager()) << " does not contain " << mk_pp(key, get_manager()) << std::endl;);
        ptr_vector<expr> nodes;
        get_nodes_in_concat(n, nodes);
        zstring valueKey, nodeValue;
        bool isStr = u.str.is_string(key, valueKey);
        for (const auto& nn : nodes) {
            if (u.str.is_string(nn, nodeValue)) {
                if (isStr) {
                    if (nodeValue.contains(valueKey))
                        return false;
                    else
                        continue;
                }
            }
            expr* real_haystack = nullptr;
            if (!not_contain(nn, key, real_haystack)){
                return false;
            }
        }
        return true;
    }

    int theory_str::get_lower_bound_image_in_expr(expr* n, expr* str){
        ptr_vector<expr> nodes;
        get_nodes_in_concat(n, nodes);
        int cnt = 0;

        zstring value;
        u.str.is_string(str, value);
        zstring tmpValue;
        for (const auto& nn : nodes){
            expr* real_haystack = nullptr;
            if (does_contain(nn, str, real_haystack)){
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << std::endl;);
                cnt ++;
            }
            else if (u.str.is_string(nn, tmpValue) && value.length() > 0) {
                if (tmpValue.contains(value))
                    cnt++;
            }
        }

        if (cnt > 0)
            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " there are at least" << cnt << " in " << mk_pp(n, get_manager()) << std::endl;);
        return cnt;
    }

    bool theory_str::get_image_in_expr(expr* n, expr_ref_vector &constList){

        ptr_vector<expr> nodes;
        get_nodes_in_concat(n, nodes);

        int constCount = 0;
        for (const auto& e : nodes) {
            if (u.str.is_string(e)) {
                if (!constList.contains(e))
                    constCount++;
                constList.push_back(e);
            }
        }
        if (constCount == 1){
            // check other variabes do not contain const
            for (const auto& s : nodes){
                if (s != constList[0].get()){
                    expr* realHaystack = nullptr;
                    if (not_contain(s, constList[0].get(), realHaystack)){
                        // good
                    }
                    else {
                        constList.reset();
                        return false;
                    }
                }
            }

            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " there are " << constList.size() << " in " << mk_pp(constList[0].get(), get_manager()) << std::endl;);
            // can get the image here
            return true;
        }
        else
            return false;
    }

    bool theory_str::not_contain(expr* haystack, expr* needle, expr* &realHaystack){
        context &ctx = get_context();
        expr_ref_vector eqs(get_manager());
        collect_eq_nodes(haystack, eqs);
        for (const auto& s: eqs) {
            std::pair<expr *, expr *> key = std::make_pair(s, needle);
            if (contain_pair_bool_map.contains(key)) {
                STRACE("str",
                       tout << __LINE__ << " " << __FUNCTION__ << " not_contain check" << mk_pp(haystack, get_manager())
                            << " " << mk_pp(needle, get_manager()) << std::endl;);

                switch (ctx.get_assignment(contain_pair_bool_map[key])) {
                    case l_true: STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " l_true"
                                                    << mk_pp(haystack, get_manager()) << " "
                                                    << mk_pp(needle, get_manager()) << std::endl;);
                        break;
                    case l_false: STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " l_false"
                                                     << mk_pp(haystack, get_manager()) << " "
                                                     << mk_pp(needle, get_manager()) << std::endl;);
                        realHaystack = s;
                        return true;
                    case l_undef: STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " l_undef"
                                                     << mk_pp(haystack, get_manager()) << " "
                                                     << mk_pp(needle, get_manager()) << std::endl;);
                        break;
                }
            }
        }
        return false;
    }

    bool theory_str::does_contain(expr* haystack, expr* needle, expr* &realHaystack){
        context &ctx = get_context();
        expr_ref_vector eqs(get_manager());
        collect_eq_nodes(haystack, eqs);
        for (const auto& s: eqs) {
            std::pair<expr *, expr *> key = std::make_pair(s, needle);
            if (contain_pair_bool_map.contains(key)) {
                STRACE("str",
                       tout << __LINE__ << " " << __FUNCTION__ << " does_contain check" << mk_pp(haystack, get_manager())
                            << " " << mk_pp(needle, get_manager()) << std::endl;);

                switch (ctx.get_assignment(contain_pair_bool_map[key])) {
                    case l_true: STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " l_true"
                                                    << mk_pp(haystack, get_manager()) << " "
                                                    << mk_pp(needle, get_manager()) << std::endl;);
                        realHaystack = s;
                        return true;
                    case l_false: STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " l_false"
                                                     << mk_pp(haystack, get_manager()) << " "
                                                     << mk_pp(needle, get_manager()) << std::endl;);
                        break;
                    case l_undef: STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " l_undef"
                                                     << mk_pp(haystack, get_manager()) << " "
                                                     << mk_pp(needle, get_manager()) << std::endl;);
                        break;
                }
            }
        }
        return false;
    }

    int theory_str::get_actual_trau_lvl(){
        return m_scope_level;
        context& ctx = get_context();
        int tmpz3State = 0;
        if (mful_scope_levels.size() > 0) {
            expr_ref lastAssign = mful_scope_levels[(int)mful_scope_levels.size() - 1];
            literal tmpL = ctx.get_literal(lastAssign);
            tmpz3State = std::max(0, (int)ctx.get_assign_level(tmpL));
        }
        return tmpz3State;
    }

    /*
     * if all equalities in previous branch are still true
     * Note 1: some equalities can change where some len = 0, e.g. x . y . z becomes x . z if y.len = 0
     * Note 2: some new equalties because of length information, e.g. x . y = "abc" && y.len = 2 implies y = "bc"
     * In such cases, we are still the same "core" branch.
     */
    bool theory_str::at_same_eq_state(UnderApproxState state) {
        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << std::endl;);
        ast_manager & m = get_manager();
        expr_ref_vector guessedExprs(m),  guessedDisEqExprs(m);
        fetch_guessed_exprs_with_scopes(guessedExprs, guessedDisEqExprs);
        guessedExprs.append(guessedDisEqExprs);

        expr_ref_vector prev_guessedExprs(m);
        fetch_guessed_exprs_from_cache(state, prev_guessedExprs);

        if (state.equalities.size() == 0 && state.disequalities.size() == 0)
            return false;

        // compare all eq
        for(const auto& e : prev_guessedExprs){
            if (e != m.mk_true() && !guessedExprs.contains(e) ) {
                // check the case where some var disappear because of len = 0
                if (to_app(e)->get_num_args() != 2)
                    continue;

                // check if it is the bound var
                std::string toStr = expr2str(e);
                if (toStr.find("Bound!") != std::string::npos)
                    continue;
                expr* lhs = simplify_concat(to_app(e)->get_arg(0));
                expr* rhs = simplify_concat(to_app(e)->get_arg(1));
                expr* eq = createEqualOperator(lhs, rhs);
                expr_ref_vector eqs(m);
                collect_eq_nodes(lhs, eqs);
                if (eq != m.mk_true() && !eqs.contains(rhs)) {
                    STRACE("str", tout << __LINE__ << " not at_same_state " << mk_pp(e, m) << std::endl;);
                    for (const auto& s: eqs)
                        STRACE("str", tout << __LINE__ << " not at_same_state " << mk_pp(lhs, m) << " " << mk_pp(s, m) << std::endl;);
                    return false;
                }
                else
                    STRACE("str", tout << __LINE__ << " does contain expr at_same_state " << mk_pp(e, m) << " --> " << mk_pp(eq, m)<< std::endl;);
            }
        }

        return true;

//        // compare all eq
//        for(const auto& e : prev.m_wes_to_satisfy){
//            if (curr.m_wes_to_satisfy.find(e) == curr.m_wes_to_satisfy.end()) {
//                STRACE("str", tout << __LINE__ <<  " not at_same_state " << e << std::endl;);
//                return false;
//            }
//        }
//
//        for(const auto& e : curr.m_wes_to_satisfy){
//            // skip x = ""
//            if (e.lhs() == str::word_term().of_string("\"\"") || e.rhs() == str::word_term().of_string("\"\""))
//                continue;
//
//            if (prev.m_wes_to_satisfy.find(e) == prev.m_wes_to_satisfy.end()) {
//                STRACE("str", tout << __LINE__ <<  " not at_same_state " << e << std::endl;);
//
//                // skip x = "" . x
//                {
//                    str::word_term lhs = e.lhs();
//                    str::word_term rhs = e.rhs();
//                    std::set<str::element> lhs_elements = lhs.variables();
//                    std::set<str::element> rhs_elements = rhs.variables();
//                    if (lhs_elements.size() != 0 && rhs_elements.size() != 0) {
//                        bool included = true;
//                        if (lhs_elements.size() < rhs_elements.size()) {
//                            for (const auto &el : lhs_elements)
//                                if (rhs_elements.find(el) == rhs_elements.end()) {
//                                    included = false;
//                                    break;
//                                }
//                        } else
//                            for (const auto &el : rhs_elements)
//                                if (lhs_elements.find(el) == lhs_elements.end()) {
//                                    included = false;
//                                    break;
//                                }
//
//                        if (included) {
//                            STRACE("str", tout << __LINE__ << " skip constraint " << e << std::endl;);
//                            continue;
//                        }
//                    }
//                }
//
//                return false;
//            }
//        }
//
//        return true;
    }

    bool theory_str::at_same_diseq_state(str::state curr, str::state prev) {
        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << std::endl;);

        // compare all diseq
        for(const auto& e : prev.m_wes_to_fail){
            // skip x = ""
            if (e.lhs() == str::word_term().of_string("\"\"") || e.rhs() == str::word_term().of_string("\"\""))
                continue;
            if (curr.m_wes_to_fail.find(e) == curr.m_wes_to_fail.end() && curr.m_wes_to_satisfy.find(e) != curr.m_wes_to_satisfy.end()) {
                STRACE("str", tout << __LINE__ <<  " not at_same_state  " << e << std::endl;);
                return false;
            }
        }

        return true;
    }

    /*
     * for all constraints over a variable, if they start/end with const strings,
     *      const start/end strings should be consistent
     */
    bool theory_str::review_starting_ending_combination(std::map<expr *, std::set<expr *>> eq_combination){
        for (const auto& c : eq_combination) {
            std::vector<zstring> starts;
            std::vector<zstring> ends;
            zstring constStr;
            for (const auto& concat : c.second)
                if (u.str.is_concat(concat)){
                    ptr_vector<expr> childNodes;
                    get_nodes_in_concat(concat, childNodes);
                    zstring value;
                    if (u.str.is_string(childNodes[0], value))
                        starts.push_back(value);
                    if (u.str.is_string(childNodes[childNodes.size() - 1], value))
                        ends.push_back(value);
                }
                else if (u.str.is_string(concat, constStr)) {
                    starts.push_back(constStr);
                    ends.push_back(constStr);
                }
            // check all starts
            for (int i = 0; i < starts.size(); ++i)
                for (int j = i + 1; j < starts.size(); ++j)
                    if (starts[i].prefixof(starts[j]) || starts[j].prefixof(starts[i])) {

                    }
                    else {
                        ast_manager &m = get_manager();
                        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " " << mk_pp(c.first, m) << " starts with " << starts[i] << " and " << starts[j] << std::endl;);
                        return false;
                    }

            // check all ends
            for (int i = 0; i < ends.size(); ++i)
                for (int j = i + 1; j < ends.size(); ++j)
                    if (ends[i].suffixof(ends[j]) || ends[j].suffixof(ends[i])) {

                    }
                    else {
                        ast_manager &m = get_manager();
                        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " " << mk_pp(c.first, m) << " ends with " << ends[i] << " and " << ends[j] << std::endl;);
                        return false;
                    }
        }
        return true;
    }

    bool theory_str::all_length_solved(){
        ast_manager &m = get_manager();
        bool notSolved = false;
        for (const auto& n : variable_set){
            rational vLen;
            if (get_len_value(n, vLen)) {
                STRACE("str", tout << __LINE__ << " var " << mk_pp(n, m) << " len = " << vLen << std::endl;);
            }
            else {
                STRACE("str", tout << __LINE__ << " var " << mk_pp(n, m) << " len = not solved" << std::endl;);
                notSolved = true;
            }
        }
        return !notSolved;
    }

    /*
     *
     */
    std::set<char> theory_str::collect_char_domain_from_concat(){
        std::set<char> charDomain;
        for (const auto& we : m_we_expr_memo) {
            zstring value;
            // lhs
            if (u.str.is_concat(we.first.get())) {
                ptr_vector<expr> childNodes;
                get_nodes_in_concat(we.first.get(), childNodes);
                for (const auto& n : childNodes){
                    if (u.str.is_string(n, value)) {
                        for (int i = 0; i < value.length(); ++i)
                            charDomain.insert(value[i]);
                    }
                }

            }
            else if (u.str.is_string(we.first.get(), value)) {
                for (int i = 0; i < value.length(); ++i)
                    charDomain.insert(value[i]);
            }

            // rhs
            if (u.str.is_concat(we.second.get())) {
                ptr_vector<expr> childNodes;
                get_nodes_in_concat(we.second.get(), childNodes);
                for (const auto& n : childNodes){
                    if (u.str.is_string(n, value)) {
                        for (int i = 0; i < value.length(); ++i)
                            charDomain.insert(value[i]);
                    }
                }

            }
            else if (u.str.is_string(we.second.get(), value)) {
                for (int i = 0; i < value.length(); ++i)
                    charDomain.insert(value[i]);
            }
        }

        for (const auto& mem : membership_memo){
            std::set<zstring> tmp = collect_strs_in_membership(mem.second);
            for (const auto& s : tmp)
                for (int i = 0; i < s.length(); ++i)
                    charDomain.insert(s[i]);
        }

        if (string_int_conversion_terms.size() > 0) {
            charDomain.insert('-');
            for (int i = 0; i < 10; ++i)
                charDomain.insert('0' + i);
        }

        for (const auto& ch : charDomain)
            STRACE("str", tout << __LINE__ <<  " sigmaDomain: " << ch << std::endl;);

        return charDomain;
    }

    std::set<char> theory_str::collect_char_domain_from_eqmap(std::map<expr *, std::set<expr *>> eq_combination){
        std::set<char> charDomain;
        for (const auto& v : eq_combination) {
            // skip if it is a simple case
            if ((v.second.size() == 1 && v.first == *(v.second.begin())) || v.second.size() == 0)
                continue;

            zstring value;
            if (u.str.is_concat(v.first)) {
                ptr_vector<expr> childNodes;
                get_nodes_in_concat(v.first, childNodes);
                for (const auto& n : childNodes){
                    if (u.str.is_string(n, value)) {
                        for (int i = 0; i < value.length(); ++i)
                            charDomain.insert(value[i]);
                    }
                }
            }
            else if (u.str.is_string(v.first, value)) {
                for (int i = 0; i < value.length(); ++i)
                    charDomain.insert(value[i]);
            }

            for (const auto& e : v.second) {
                if (u.str.is_concat(e)) {
                    ptr_vector<expr> childNodes;
                    get_nodes_in_concat(e, childNodes);
                    for (const auto& n : childNodes){
                        if (u.str.is_string(n, value)) {
                            for (int i = 0; i < value.length(); ++i)
                                charDomain.insert(value[i]);
                        }
                    }
                }
                else if (u.str.is_string(e, value)) {
                    for (int i = 0; i < value.length(); ++i)
                        charDomain.insert(value[i]);
                }
            }
        }

        for (const auto& mem : membership_memo){
            std::set<zstring> tmp = collect_strs_in_membership(mem.second);
            for (const auto& s : tmp)
                for (int i = 0; i < s.length(); ++i)
                    charDomain.insert(s[i]);
        }

        if (string_int_conversion_terms.size() > 0) {
            charDomain.insert('-');
            for (int i = 0; i < 10; ++i)
                charDomain.insert('0' + i);
        }

        for (const auto& ch : charDomain)
            STRACE("str", tout << __LINE__ <<  " sigmaDomain: " << ch << std::endl;);
        return charDomain;
    }

    /*
     * x = y . indexOf1 . "A" . ...
     * x = y . replace1 . "A" . ...
     * --> indexOf1 = replace1
     */
    bool theory_str::handle_contain_family(std::map<expr *, std::set<expr *>> eq_combination) {
        ast_manager & m = get_manager();
        expr_ref_vector ands(m);
        for (const auto &v : eq_combination)
            if (v.second.size() > 1) {
                std::vector<expr *> tmpVector;
                tmpVector.insert(tmpVector.end(), v.second.begin(), v.second.end());
                for (int i = 0; i < tmpVector.size(); ++i)
                    for (int j = i + 1; j < tmpVector.size(); ++j) {
                        expr* tmp = create_equations_over_contain_vars(tmpVector[i], tmpVector[j]);
                        if (tmp != nullptr)
                            ands.push_back(tmp);
                    }
            }

        if (ands.size() > 0) {
            expr_ref_vector eqcores(m), diseqcores(m);
            fetch_guessed_exprs_with_scopes(eqcores, diseqcores);
            fetch_guessed_core_exprs(eq_combination, eqcores, diseqcores);
            expr_ref toAssert(createAndOperator(ands), m);
            assert_axiom(toAssert.get());
            impliedFacts.push_back(toAssert.get());
            return true;
        }
        else
            return false;
    }

    /*
     * x = y . indexOf1 . "A" . ...
     * x = y . replace1 . "A" . ...
     * --> indexOf1 = replace1
     */
    expr* theory_str::create_equations_over_contain_vars(expr* x, expr* y){
        ptr_vector<expr> nodes_x;
        get_nodes_in_concat(x, nodes_x);

        ptr_vector<expr> nodes_y;
        get_nodes_in_concat(y, nodes_y);

        // remove all prefixes
        int pos = 0;
        for (pos = 0; pos < std::min(nodes_x.size(), nodes_y.size()); ++pos) {
            if (!are_equal_exprs(nodes_x[pos], nodes_y[pos]))
                break;
        }

        if (pos >= std::min(nodes_x.size(), nodes_y.size() - 1))
            return nullptr;
        else {
            std::string name_x = expr2str(nodes_x[pos]);
            std::string name_y = expr2str(nodes_y[pos]);
            if (name_x.find("indexOf1") == 0 || name_x.find("replace1") == 0 || name_x.find("pre_contain") == 0 )
                if (name_y.find("indexOf1") == 0 || name_y.find("replace1") == 0 ||
                        name_y.find("pre_contain") == 0) {
                    if (are_equal_exprs(nodes_x[pos + 1], nodes_y[pos + 1])) {
                        return createEqualOperator(nodes_x[pos], nodes_y[pos]);
                    }
                    else {
                        zstring tmp00;
                        zstring tmp01;
                        if (u.str.is_string(nodes_x[pos + 1], tmp00) && u.str.is_string(nodes_y[pos + 1], tmp01)) {
                            if (tmp00.prefixof(tmp01) || tmp01.prefixof(tmp00))
                                return createEqualOperator(nodes_x[pos], nodes_y[pos]);
                        }
                    }
                }
        }
        return nullptr;
    }

    /*
     * charAt1 = charAt1 at beginning because they have the same len = 1
     */
    bool theory_str::handle_charAt_family(
            std::map<expr *, std::set<expr *>> eq_combination) {
        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << std::endl;);
        clock_t t = clock();
        ast_manager & m = get_manager();
        expr_ref_vector ands(m);
        for (const auto &v : eq_combination)
            if (v.second.size() > 1) {
                std::vector<expr *> tmpVector;
                tmpVector.insert(tmpVector.end(), v.second.begin(), v.second.end());
                for (int i = 0; i < tmpVector.size(); ++i) {
                    ptr_vector<expr> nodes_i;
                    get_nodes_in_concat(tmpVector[i], nodes_i);
                    if (nodes_i.size() > 1) { // charAt
                        std::string name_i = expr2str(nodes_i[0]);
                        zstring value_i("");
                        if (name_i.find("charAt1") == 0 || (u.str.is_string(nodes_i[0], value_i) && value_i.length() > 0)) {
                            expr_ref_vector eqNodes1(m), eqNodes0(m);
                            collect_eq_nodes(nodes_i[1], eqNodes1);
                            collect_eq_nodes(nodes_i[0], eqNodes0);

                            for (int j = i + 1; j < tmpVector.size(); ++j) {
                                ptr_vector<expr> nodes_j;
                                get_nodes_in_concat(tmpVector[j], nodes_j);
                                if (nodes_j.size() > 1) {
                                    std::string name_j = expr2str(nodes_j[0]);
                                    zstring value_j("");
                                    if (name_j.find("charAt1") == 0 || (u.str.is_string(nodes_j[0], value_j) && value_j.length() > 0)) {
                                        if (are_equal_exprs(nodes_i[0], nodes_j[0]))
                                            continue;
                                        if (!(value_i.length() > 0 && value_j.length() > 0)) {
                                            if (value_i.length() == 0 && value_j.length() == 0){
                                                // both are indexofs
                                                ands.push_back(createEqualOperator(nodes_i[0], nodes_j[0]));

                                            }
                                            else {
                                                if (value_i.length() > 0) {
                                                    // indexof vs string
                                                    zstring valueIndexof = value_i.extract(0, 1);
                                                    if (!are_equal_exprs(nodes_j[0], u.str.mk_string(valueIndexof))) {
                                                        expr* tmp = createEqualOperator(u.str.mk_string(valueIndexof), nodes_j[0]);
                                                        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " " << mk_pp(tmp, m) << std::endl;);
                                                        ands.push_back(tmp);
                                                    }
                                                }
                                                else if (value_j.length() > 0){
                                                    // indexof vs string
                                                    zstring valueIndexof = value_j.extract(0, 1);
                                                    if (!are_equal_exprs(nodes_i[0], u.str.mk_string(valueIndexof))) {
                                                        expr* tmp = createEqualOperator(nodes_i[0], u.str.mk_string(valueIndexof));
                                                        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " " << mk_pp(tmp, m) << std::endl;);
                                                        ands.push_back(tmp);
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }

        if (ands.size() > 0) {
            expr_ref_vector eqcores(m), diseqcores(m);
            fetch_guessed_exprs_with_scopes(eqcores, diseqcores);
            fetch_guessed_core_exprs(eq_combination, eqcores, diseqcores);
            expr_ref toAssert(rewrite_implication(createAndOperator(eqcores), createAndOperator(ands)), m);
            assert_axiom(toAssert.get());
            impliedFacts.push_back(toAssert.get());
            return true;
        }
        else
            return false;
    }

    bool theory_str::are_equal_exprs(expr* x, expr* y){
        expr_ref_vector eqs(get_manager());
        collect_eq_nodes(x, eqs);
        if (eqs.contains(y))
            return true;
        return false;
    }

    std::set<expr*> theory_str::get_eqc_roots(){
        context & ctx = get_context();
        ast_manager & m = get_manager();
        std::set<expr*> eqc_roots;
        sort* string_sort = u.str.mk_string_sort();
        for (ptr_vector<enode>::const_iterator it = ctx.begin_enodes(); it != ctx.end_enodes(); ++it) {
            enode * e = *it;
            enode * root = e->get_root();
            if ((m.get_sort(root->get_owner()) == string_sort) && eqc_roots.find(root->get_owner()) == eqc_roots.end()) {
                eqc_roots.insert(root->get_owner());
            }
        }

        return eqc_roots;
    }

    void theory_str::add_theory_aware_branching_info(expr * term, double priority, lbool phase) {
        context & ctx = get_context();
        ctx.internalize(term, false);
        bool_var v = ctx.get_bool_var(term);
        ctx.add_theory_aware_branching_info(v, priority, phase);
    }

    std::vector<unsigned> theory_str::sort_indexes(const std::vector<std::pair<expr*, rational>> v) {

        // initialize original index locations
        std::vector<unsigned> idx(v.size());
        iota(idx.begin(), idx.end(), 0);

        // sort indexes based on comparing values in v
        std::sort(idx.begin(), idx.end(),
             [&v](size_t i1, size_t i2) {return v[i1].second > v[i2].second;});
        return idx;
    }

    bool theory_str::assignValues(
            model_generator& mg,
            const std::vector<std::pair<expr*, rational>> freeVars,
            std::map<expr*, rational> varLens,
            std::set<std::pair<expr *, int>> non_fresh_vars){
        bool unassigned = true;
        context& ctx = get_context();
        ast_manager & m = get_manager();
        STRACE("str", tout << __LINE__  << " " <<  __FUNCTION__ << std::endl;);
        std::vector<unsigned> idx = sort_indexes(freeVars);
        std::map<expr*, std::vector<int>> strValue;
        bool completion = true;
        syncConst(varLens, strValue, completion);
        if (completion) {


            std::map<expr*, int> iterInt;
            for (const auto& v : variable_set) {
                for (int i = 0; i < varPieces[v]; ++i){
                    rational val;
                    expr* tmp = getExprVarFlatIter(std::make_pair(v, i));
                    if (get_arith_value(tmp, val)){
                        iterInt[tmp] = val.get_int64();
                    }
                }
            }

            std::map<expr*, zstring> solverValues;
            for (const auto& n : arrMap){
                STRACE("str", tout << "var " << mk_pp(n.first, m) << " --> " << mk_pp(n.second, m) << std::endl;);
                rational vLen;
                if (get_len_value(n.first, vLen)){
                    zstring zstringVal("");
                    for (int i = 0; i < vLen.get_int64(); ++i){
                        expr* val_i = createSelectOperator(n.second, m_autil.mk_int(i));
                        rational v_i;
                        if (get_arith_value(val_i, v_i)) {
                            STRACE("str", tout << " val_" << i << " = " << v_i << std::endl;);
                        }
                        else {
                            app* value = nullptr;
                            if (mg.get_root2value().find(ctx.get_enode(val_i), value)) {
                                STRACE("str", tout << __LINE__ << " value :  " << mk_pp(val_i, m) << ": "
                                                   << mk_pp(value, m) << std::endl;);
                            }
                        }

                        int intVal = v_i.get_int64();
                        if (intVal <= 0 || intVal >= 128){
                            zstringVal = zstringVal + zstring((char)defaultChar);
                        }
                        else
                            zstringVal = zstringVal + zstring((char)intVal);
                    }

                    solverValues[n.first] = zstringVal;
                }
            }

            std::map<expr*, int> non_fresh_Vars;
            for (const auto& p : non_fresh_vars)
                non_fresh_Vars[p.first] = p.second;

            formatnon_fresh_Vars(idx, solverValues, freeVars, varLens, iterInt, strValue, non_fresh_Vars, completion);
            syncVarValue(strValue);
            formatOtherVars(idx, solverValues, freeVars, varLens, iterInt, strValue, non_fresh_Vars, completion);
        }
        std::pair<expr*, zstring> ands;
        for (const auto& var : freeVars)
            if (strValue.find(var.first) != strValue.end()) {
                bool varCompleted = true;
                zstring value;
                for (int i = 0; i < var.second; ++i) {
                    if (strValue[var.first][i] == 0) {
                        varCompleted = false;
                    } else {
                        value = value + zstring(char(strValue[var.first][i]));
                    }
                }
                if (varCompleted == true) {
                    unassigned = false;
                }
            }


        return !unassigned;
    }

    void theory_str::syncVarValue(std::map<expr*, std::vector<int>> &strValue){
        ast_manager & m = get_manager();
        for (const auto& var : variable_set)
            if (strValue.find(var) == strValue.end()){
                expr_ref_vector eqNodes(m);
                collect_eq_nodes(var, eqNodes);
                for (int i = 0; i < eqNodes.size(); ++i)
                    if (strValue.find(eqNodes[i].get()) != strValue.end()){
                        strValue[var] = strValue[eqNodes[i].get()];
                        break;
                    }
            }
    }

    void theory_str::formatnon_fresh_Vars(
            std::vector<unsigned> indexes,
            std::map<expr*, zstring> solverValues,
            std::vector<std::pair<expr*, rational>> lenVector,
            std::map<expr*, rational> len,
            std::map<expr*, int> iterInt,
            std::map<expr*, std::vector<int>> &strValue,
            std::map<expr *, int> non_fresh_vars,
            bool &completion){
        ast_manager & m = get_manager();
        STRACE("str", tout << __LINE__  << " " <<  __FUNCTION__ << std::endl;);
        /* 1st: handling non_fresh_ vars */
        for (const auto& s : indexes) {
            expr* varName = lenVector[s].first;
            if (variable_set.find(varName) == variable_set.end())
                continue;
            if (lenVector[s].second == 0) {
                strValue[varName] = {};
            }
            else {
                if (non_fresh_vars.find(varName) != non_fresh_vars.end()) {
                    STRACE("str", tout << __LINE__ <<  " varname: " << mk_pp(varName, m) << std::endl;);

                    if (needValue(varName, len, strValue)) {
                        STRACE("str", tout << __LINE__ <<  " consider var: : " << mk_pp(varName, m) << std::endl;);
                        bool assigned = true;

                        zstring solverValue = solverValues[varName];
                        std::vector<std::pair<int, int>> iters;
                        for (unsigned i = 0; i < p_bound.get_int64(); ++i){
                            rational len, iter;
                            if (get_arith_value(getExprVarFlatSize(std::make_pair(varName, i)), len) &&
                                get_arith_value(getExprVarFlatIter(std::make_pair(varName, i)), iter))
                            iters.emplace_back(std::make_pair(len.get_int64(), iter.get_int64()));
                        }

                        std::vector<int> tmp = createString(varName, solverValue, len, strValue, iters, assigned, true);
                        if (assigned) {
                            STRACE("str", tout << __LINE__ <<  " assign: " << mk_pp(varName, m) << std::endl;);
                            strValue[varName] = tmp;

                            backwardPropagarate(varName, len, strValue, completion);
                            forwardPropagate(varName, len, strValue, completion);
                            if (completion == false) {
                                STRACE("str", tout << __LINE__ <<  " cannot find value for var: " << mk_pp(varName, m) << std::endl;);
                            }
                            STRACE("str", tout << __LINE__ <<  " done formating: " << mk_pp(varName, m) << std::endl;);
                        }
                        else
                            STRACE("str", tout << __LINE__ <<  " cannot assign" << mk_pp(varName, m) << std::endl;);
                    }
                }
            }
        }
    }


    /*
     * create str values after running Z3
     */
    void theory_str::formatOtherVars(
            std::vector<unsigned> indexes,
            std::map<expr*, zstring> solverValues,
            std::vector<std::pair<expr*, rational>> lenVector,
            std::map<expr*, rational> len,
            std::map<expr*, int> iterInt,
            std::map<expr*, std::vector<int>> &strValue,
            std::map<expr *, int> non_fresh_vars,
            bool &completion){
        ast_manager & m = get_manager();
        STRACE("str", tout << __LINE__  << " " <<  __FUNCTION__ << std::endl;);
        std::map<expr*, int> index = createSimpleEqualMap(len);

        /* 3rd: handling other vars */
        for (const auto& s : indexes) {
            expr* varName = lenVector[s].first;
            if (lenVector[s].second == 0) {
            }
            else {
                std::string varNameStr = expr2str(varName);

                if (varNameStr.find("!tmp") != std::string::npos){
                    continue;
                }

                bool assigned = true;

                if (needValue(varName, len, strValue)) {
                    expr_ref_vector eqNodes(m);
                    expr* constStrNode = collect_eq_nodes(varName, eqNodes);
                    if (constStrNode != nullptr)
                        continue;

                    std::vector<expr*> eqVar;
                    if (index.find(varName) == index.end()) {
                        eqVar.emplace_back(varName);
                    }
                    else {
                        int num = index[varName];
                        for (const auto& v : index)
                            if (v.second == num)
                                eqVar.emplace_back(v.first);
                    }
//                    if (isBlankValue(varName, len, strValue))
//                        if (findExistsingValue(varName, equalities, len, strValue, eqVar))
//                            continue;
                    STRACE("str", tout << __LINE__ <<  " consider var: : " << mk_pp(varName, m) << std::endl;);

                    zstring solverValue = solverValues[varName];
                    std::vector<std::pair<int, int>> iters;

                    std::vector<int> tmp = createString(varName, solverValue, len, strValue, iters, assigned, true);
                    if (assigned) {
                        STRACE("str", tout << __LINE__ <<  " assign: " << mk_pp(varName, m) << std::endl;);
                        strValue[varName] = tmp;

                        backwardPropagarate(varName, len, strValue, completion);
                        forwardPropagate(varName, len, strValue, completion);
                        if (completion == false) {
                            STRACE("str", tout << __LINE__ <<  " cannot find value for var: " << mk_pp(varName, m) << std::endl;);
                        }
                            STRACE("str", tout << __LINE__ <<  " done formating: " << mk_pp(varName, m) << std::endl;);
                    }
                    else
                        STRACE("str", tout << __LINE__ <<  " cannot assign" << mk_pp(varName, m) << std::endl;);
                }
            }
        }
    }

    std::map<expr*, int> theory_str::createSimpleEqualMap(
            std::map<expr*, rational> len){
        std::map<expr*, int> index;
        int maxIndex = 0;
        for (const auto& op : m_we_expr_memo){
            expr* arg01 = op.first.get();
            expr* arg02 = op.second.get();

            {
                if (getVarLength(arg02, len) != getVarLength(arg01, len)) {
                    if (index.find(arg01) == index.end()){
                        maxIndex++;
                        index[arg01] = maxIndex;
                    }
                    if (index.find(arg02) == index.end()){
                        maxIndex++;
                        index[arg02] = maxIndex;
                    }
                    continue;
                }
                if (index.find(arg01) != index.end()){
                    if (index.find(arg02) != index.end()) {
                        int num01 = index[arg01];
                        int num02 = index[arg02];
                        for (const auto& v : index)
                            if (v.second == num02)
                                index[v.first] = num01;
                    }
                    else {
                        index[arg02] = index[arg01];
                    }

                }
                else if (index.find(arg02) != index.end()){
                    index[arg01] = index[arg02];
                }
                else {
                    maxIndex++;
                    index[arg01] = maxIndex;
                    index[arg02] = maxIndex;
                }
            }
        }
        return index;
    }

    /*
     *
     */
    bool theory_str::isBlankValue(expr* name,
                      std::map<expr*, rational> len,
                      std::map<expr*, std::vector<int>> strValue){
        std::vector<int> value = getVarValue(name, len, strValue);
        for (const auto& v : value)
            if (v != 0)
                return false;
        return true;
    }

    /*
     * note that, value can be wrong because we removed some not-contain constraints.
     */
    std::vector<int> theory_str::createString(
            expr* name,
            zstring value,
            std::map<expr*, rational> len,
            std::map<expr*, std::vector<int>> strValue,
            std::vector<std::pair<int, int>> iters,
            bool &assigned,
            bool assignAnyway){
        ast_manager & m = get_manager();
        int lenVar = getVarLength(name, len).get_int64();

        STRACE("str", tout << __LINE__  << " " <<  __FUNCTION__ << ": " << mk_pp(name, m) << ": " << value << ", len = " << lenVar << std::endl;);
        std::vector<int> val = getVarValue(name, len, strValue);

        STRACE("str", tout << __LINE__ << ": " ;);
        for (int i = 0; i < lenVar; ++i)
            if (val[i] != 0) {
                STRACE("str", tout <<(char)val[i];);
            }
            else
                STRACE("str", tout <<val[i];);
        STRACE("str", tout << std::endl;);

        /* check if the value is usable or not */
        bool usable = true;
        if (notContainMap.find(name) != notContainMap.end())
            for (const auto& str : notContainMap[name]) {
                zstring notContain;
                if (u.str.is_string(str, notContain)){
                    if (value.indexof(notContain, 0) == -1){
                        usable = false;
                    }
                }
            }

        /* update values found by the solver & previous iterations */
        /* collect iter */
//	assert(iters.size() == p_bound.get_int64());
//	int pos = 0;
//	for (int i = 0; i < p_bound.get_int64(); ++i){
//		__debugPrint(logFile, "%d iter_%d : %d %d\n", __LINE__, i, iters[i].first, iters[i].second);
        /* part i */
//		for (int j = 0; j < iters[i].second; ++j)
//			for (int k = 0; k < iters[i].first; ++k)
//				if (val[pos + j * iters[i].first + k] == 0)
//					val[pos + j * iters[i].first + k] = value[pos + k];
//		pos += iters[i].first;
//	}
        if (usable)
            for (int i = 0; i < lenVar; ++i)
                if (val[i] == 0)
                    if (i < (int)value.length())
                        val[i] = value[i];

        bool canAssign = false;
        for (int i = 0; i < lenVar; ++i)
            if (val[i] != 0) {
                canAssign = true;
                break;
            }

        /* do not support substr */

        if (canAssign || assignAnyway) {
            for (int i = 0; i < lenVar; ++i)
                if (val[i] == 0)
                    val[i] = defaultChar;
        }
        else {
            /* cannot assign because we do not know anything */
            assigned = false;
            return val;
        }

        STRACE("str", tout << __LINE__ << ": " ;);
        for (int i = 0; i < lenVar; ++i)
            if (val[i] != 0) {
                STRACE("str", tout <<(char)val[i];);
            }
            else
                STRACE("str", tout <<val[i];);
        STRACE("str", tout << std::endl;);
        assigned = true;
        return val;
    }

    /*
     *
     */
    bool theory_str::needValue(expr* name,
                   std::map<expr*, rational> len,
                   std::map<expr*, std::vector<int>> strValue){
        std::vector<int> value = getVarValue(name, len, strValue);
        for (const auto& v : value)
            if (v == 0)
                return true;
        return false;
    }

    /*
     *
     */
    void theory_str::syncConst(
            std::map<expr*, rational> len,
            std::map<expr*, std::vector<int>> &strValue,
            bool &completion){
        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << std::endl;);
        ast_manager & m = get_manager();
        std::set<expr*> propagatingList;
        for (const auto& var : uState.eq_combination){
            STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << ": " << mk_pp(var.first, m) << std::endl;);
            /* init value */
            zstring value;
            if (u.str.is_string(var.first, value)) {
                if (value.length() == 0)
                    continue;
                std::vector<int> tmp;
                for (int i = 0; i < value.length(); ++i)
                    tmp.emplace_back(value[i]);
                strValue[var.first] = tmp;
                propagatingList.emplace(var.first);
            }
            else {

            }

            bool update = false;
            STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << ": " << mk_pp(var.first, m) << std::endl;);
            std::vector<int> tmp = getVarValue(var.first, len, strValue);
            STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << ": " << mk_pp(var.first, m) << std::endl;);
            for (const auto& eq : var.second){
                int pos = 0;
                ptr_vector<expr> nodes;
                get_nodes_in_concat(eq, nodes);

                for (int i = 0; i < nodes.size(); ++i){
                    STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << ": " << mk_pp(nodes[i], m) << std::endl;);
                    int lengthS = getVarLength(nodes[i], len).get_int64();
                    STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << ": " << mk_pp(nodes[i], m) << std::endl;);
                    zstring value;
                    if (u.str.is_string(nodes[i], value)) {
                        if (value.length() == 0)
                            continue;

                        /* assign value directly */
                        std::vector<int> tmpValue;
                        for (unsigned i = 0; i < value.length(); ++i) {
                            tmpValue.emplace_back(value[i]);
                            if (tmp[pos + i] == 0) {
                                tmp[pos + i] = value[i];
                                update = true;
                            }
                            else {
                                SASSERT(tmp[pos + i] == value[i]);
                            }
                        }

                        strValue[nodes[i]] = tmpValue;
                    }
                    pos += lengthS;
                }
            }
            if (update == true) {
                strValue[var.first] = tmp;
                propagatingList.emplace(var.first);
            }
        }

        for (const auto& s : propagatingList) {
            STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << ": propagating "  << mk_pp(s, m) << std::endl;);
            forwardPropagate(s, len, strValue, completion);
            if (u.str.is_string(s) || uState.eq_combination[s].size() > 1)
                backwardPropagarate(s, len, strValue, completion);
            if (completion == false) {
                STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << ": cannot find var "  << mk_pp(s, m) << std::endl;);
                return;
            }
        }
        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << std::endl;);
    }

    /*
     * a = b . c .We know b, need to update a
     */
    void theory_str::forwardPropagate(
            expr* newlyUpdate,
            std::map<expr*, rational> len,
            std::map<expr*, std::vector<int>> &strValue,
            bool &completion){
        ast_manager & m = get_manager();
        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " " << mk_pp(newlyUpdate, m) << ": completion " << (completion? 1 : 0) << std::endl;);
        if (completion == false)
            return;
        std::vector<int> sValue = getVarValue(newlyUpdate, len, strValue);
        int length = sValue.size();

        if (length == 0) {
            return;
        }

        for (const auto& var : uState.eq_combination){
            if (appearanceMap[newlyUpdate].find(var.first) == appearanceMap[newlyUpdate].end())
                continue;

            if (u.str.is_string(var.first))
                continue;

            std::vector<int> value = getVarValue(var.first, len, strValue);
            int varLen = value.size();
            for (unsigned i = 0; i < value.size(); ++i)
                if (value[i] != 0) {
                    STRACE("str", tout << (char) value[i];);
                } else STRACE("str", tout << value[i];);
            STRACE("str", tout << " end of " << mk_pp(var.first, m) << std::endl;);

            /* update parents */
            bool foundInParents = false;
            for (const auto& eq : var.second) {
                ptr_vector<expr> nodes;
                get_nodes_in_concat(eq, nodes);
                if (std::find(nodes.begin(), nodes.end(), newlyUpdate) != nodes.end()) {
                    int pos = 0;

                    for (int i = 0; i < nodes.size(); ++i) {
                        int varLength = getVarLength(nodes[i], len).get_int64();
                        if (nodes[i] == newlyUpdate) {

                            for (int i = 0; i < varLength; ++i)
                                if (value[pos + i] == 0 && sValue[i] != 0) {
                                    value[pos + i] = sValue[i];
                                    foundInParents = true;
                                } else if (value[pos + i] != 0 && sValue[i] != 0 && value[pos + i] != sValue[i]) {
                                    completion = false;
                                    return;
                                }
                        }
                        pos += varLength;
                    }
                }
            }

            if (foundInParents) {
                STRACE("str", tout << __LINE__ <<  " " << mk_pp(newlyUpdate, m) << " update var " << mk_pp(var.first, m) << std::endl;);
                for (unsigned i = 0; i < value.size(); ++i)
                    if (value[i] != 0) {
                        STRACE("str", tout << (char)value[i];);
                    }
                    else
                        STRACE("str", tout << value[i];);
                STRACE("str", tout << std::endl;);
                strValue[var.first] = value;
                forwardPropagate(var.first, len, strValue, completion);

                /* update peers */
                if (var.second.size() > 1) {
                    STRACE("str", tout << __LINE__ <<  " update peers" << std::endl;);
                    for (const auto& eq : var.second){
                        value = getVarValue(var.first, len, strValue);
                        int pos = 0;
                        ptr_vector<expr> nodes;
                        get_nodes_in_concat(eq, nodes);
                        for (int i = 0; i < nodes.size(); ++i){
                            if (u.str.is_string(nodes[i])) {
                                pos += getVarLength(nodes[i], len).get_int64();
                            }
                            else {
                                int varLength = getVarLength(nodes[i], len).get_int64();
                                std::vector<int> sValue = getVarValue(nodes[i], len, strValue);

                                bool updated = false;
                                for (int i = 0; i < varLength; ++i) {
                                    if (sValue[i] != value[pos + i]) {
                                        updated = true;
                                        sValue[i] = value[pos + i];
                                    }
                                }
                                if (updated == true) {
                                    strValue[nodes[i]] = sValue;
                                    if (uState.eq_combination[nodes[i]].size() > 1)
                                        forwardPropagate(nodes[i], len, strValue, completion);
                                    if (uState.eq_combination.find(nodes[i]) != uState.eq_combination.end())
                                        backwardPropagarate(nodes[i], len, strValue, completion);
                                    if (completion == false) {
                                        STRACE("str", tout << __LINE__ << " cannot find var: " << mk_pp(nodes[i], m) << std::endl;);
                                        return;
                                    }
                                    STRACE("str", tout << __LINE__ << "done update child. " << std::endl;);
                                }
                                pos += varLength;
                            }
                        }
                    }
                }
            }
        }
    }

    /*
 * a = b . c. We know a, need to update b and c
 */
    void theory_str::backwardPropagarate(
            expr* newlyUpdate,
            std::map<expr*, rational> len,
            std::map<expr*, std::vector<int>> &strValue,
            bool &completion){
        ast_manager & m = get_manager();
        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " " << mk_pp(newlyUpdate, m) << ": completion " << (completion? 1 : 0) << std::endl;);
        if (completion == false)
            return;

        std::vector<int> value = getVarValue(newlyUpdate, len, strValue);
        int length = getVarLength(newlyUpdate, len).get_int64();

        if (length == 0) {
            return;
        }
        for (const auto& eq : uState.eq_combination[newlyUpdate]){
            int pos = 0;
            ptr_vector<expr> nodes;
            get_nodes_in_concat(eq, nodes);
            for (int i = 0; i < nodes.size(); ++i) {
                int lengthVar = getVarLength(nodes[i], len).get_int64();
                if (u.str.is_string(nodes[i])) {
                }
                else if(strValue.find(nodes[i]) != strValue.end()){
                    std::vector<int> sValue = getVarValue(nodes[i], len, strValue);
                    /* verify a determined value */
                    bool update = false;
                    for (int i = 0; i < lengthVar; ++i)
                        if (value[pos + i] != 0 && sValue[i] != 0 && value[pos + i] != sValue[i]) {
                            completion = false;
                            return;
                        }
                        else if (value[pos + i] != 0 && sValue[i] == 0){
                            sValue[i] = value[pos + i];
                            update = true;
                        }

                    if (update == true) {
                        STRACE("str", tout << __LINE__ << " update existed value" << std::endl;);
                        for (unsigned i = 0; i < value.size(); ++i)
                            if (value[i] != 0) {
                                STRACE("str", tout << (char)value[i];);
                            }
                            else
                                STRACE("str", tout << value[i];);
                        STRACE("str", tout << std::endl;);

                        strValue[nodes[i]] = sValue;
                        forwardPropagate(nodes[i], len, strValue, completion);
                        backwardPropagarate_simple(nodes[i], len, strValue, completion);
                        if (completion == false) {
                            STRACE("str", tout << __LINE__ << " cannot find value for var: " << mk_pp(nodes[i], m) << std::endl;);
                            return;
                        }
                    }
                }
                else {
                    STRACE("str", tout << __LINE__ << " assign a new value "  << std::endl;);
                    SASSERT(len.find(nodes[i]) != len.end());
                    /* update a new value */
                    std::vector<int> sValue;
                    for (int i = 0; i < lengthVar; ++i)
                        sValue.emplace_back(value[pos + i]);
                    strValue[nodes[i]] = sValue;

                    forwardPropagate(nodes[i], len, strValue, completion);
                    if (completion == false) {
                        STRACE("str", tout << __LINE__ << " cannot find value for var: " << mk_pp(nodes[i], m) << std::endl;);
                        return;
                    }
                }
                pos += lengthVar;
            }
            SASSERT(pos == length);
        }
    }

    /*
     * a = b . c. We know a, need to update b and c
     */
    void theory_str::backwardPropagarate_simple(
            expr* newlyUpdate,
            std::map<expr*, rational> len,
            std::map<expr*, std::vector<int>> &strValue,
            bool &completion){
        ast_manager & m = get_manager();
        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " " << mk_pp(newlyUpdate, m) << ": completion " << (completion? 1 : 0) << std::endl;);
        if (completion == false)
            return;

        std::vector<int> value = getVarValue(newlyUpdate, len, strValue);
        rational length = getVarLength(newlyUpdate, len);

        if (length.get_int64() == 0) {
            return;
        }

        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " " << mk_pp(newlyUpdate, m) << ": completion " << (completion? 1 : 0) << std::endl;);
        for (const auto& eq : uState.eq_combination[newlyUpdate]){

            int pos = 0;
            ptr_vector<expr> nodes;
            get_nodes_in_concat(eq, nodes);
            for (int i = 0; i < nodes.size(); ++i)
                if (nodes[i] != newlyUpdate) {
                    if (u.str.is_string(nodes[i])) {
                        int lengthVar = getVarLength(nodes[i], len).get_int64();
                        pos += lengthVar;
                    } else if (strValue.find(nodes[i]) != strValue.end()) {
                        STRACE("str",
                               tout << __LINE__ << " " << __FUNCTION__ << "  update " << mk_pp(nodes[i], m) << " from "
                                    << mk_pp(newlyUpdate, m) << std::endl;);
                        std::vector<int> sValue = getVarValue(nodes[i], len, strValue);
                        int lengthVar = getVarLength(nodes[i], len).get_int64();
                        /* verify a determined value */

                        bool update = false;
                        for (int i = 0; i < lengthVar; ++i)
                            if (value[pos + i] != 0 && sValue[i] != 0 && value[pos + i] != sValue[i]) {
                                STRACE("str", tout << __LINE__ << " error at :  " << mk_pp(nodes[i], m) << std::endl;);
                                completion = false;
                                return;
                            } else if (value[pos + i] != 0 && sValue[i] == 0) {
                                sValue[i] = value[pos + i];
                                update = true;
                            } else if (value[pos + i] == 0 && sValue[i] != 0) {
                            }

                        pos += lengthVar;

                        if (update == true) {
                            STRACE("str",
                                   tout << __LINE__ << " update existed value " << mk_pp(nodes[i], m) << std::endl;);
                            for (unsigned i = 0; i < value.size(); ++i)
                                if (value[i] != 0) {
                                    STRACE("str", tout << (char) value[i];);
                                } else STRACE("str", tout << value[i];);
                            STRACE("str", tout << std::endl;);

                            strValue[nodes[i]] = sValue;
                            backwardPropagarate_simple(nodes[i], len, strValue, completion);
                        }
                    } else {
                        STRACE("str", tout << __LINE__ << " assign a new value: " << mk_pp(nodes[i], m) << std::endl;);
                        SASSERT(len.find(nodes[i]) != len.end());
                        int lengthVar = getVarLength(nodes[i], len).get_int64();
                        /* update a new value */
                        std::vector<int> sValue;
                        for (int i = 0; i < lengthVar; ++i)
                            sValue.emplace_back(value[pos + i]);
                        strValue[nodes[i]] = sValue;
                        pos += lengthVar;
                        backwardPropagarate_simple(nodes[i], len, strValue, completion);
                    }
                }
            else {
                    pos =  pos + length.get_int64();
            }
            SASSERT(pos == length.get_int64());
        }
    }

    /*
     *
     */
    std::vector<int> theory_str::getVarValue(
            expr* newlyUpdate,
            std::map<expr*, rational> len,
            std::map<expr*, std::vector<int>> &strValue){
        zstring value;
        if (u.str.is_string(newlyUpdate, value)){
            std::vector<int> tmp;
            for (int i = 0; i < value.length(); ++i)
                tmp.push_back(value[i]);
            return tmp;
        }
        else {
            expr_ref_vector eq(get_manager());
            expr* valueExpr = collect_eq_nodes(newlyUpdate, eq);
            if (valueExpr != nullptr){
                u.str.is_string(valueExpr, value);
                std::vector<int> tmp;
                for (int i = 0; i < value.length(); ++i)
                    tmp.push_back(value[i]);
                return tmp;
            }
        }

        if (strValue.find(newlyUpdate) != strValue.end()) {
            std::vector<int> value = strValue[newlyUpdate];
            rational length = getVarLength(newlyUpdate, len);
            if ((int)value.size() < length.get_int64()) {
                for (int i = (int)value.size(); i < length; ++i)
                    value.emplace_back(0);
                strValue[newlyUpdate] = value;
            }
            return value;
        }
        else {
            rational length = getVarLength(newlyUpdate, len);
            strValue[newlyUpdate] = std::vector<int>(length.get_int64(), 0);
            return strValue[newlyUpdate];
        }
    }


    /*
     *
     */
    rational theory_str::getVarLength(
            expr* newlyUpdate,
            std::map<expr*, rational> len){
        zstring value;
        if (u.str.is_string(newlyUpdate, value)){
            return rational(value.length());
        }
        else {
            if (len.find(newlyUpdate) == len.end()){
                if (u.str.is_concat(newlyUpdate)){
                    ptr_vector<expr> nodes;
                    get_nodes_in_concat(newlyUpdate, nodes);
                    rational lenTmp(0);
                    for (int i = 0; i < nodes.size(); ++i)
                        lenTmp = lenTmp + len[nodes[i]];
                    len[newlyUpdate] = lenTmp;
                }
                else
                    SASSERT(false);
            }
            return len[newlyUpdate];
        }
    }

    bool theory_str::fixedValue(std::vector<std::pair<expr*, rational>> &freeVars, std::map<expr*, rational> varLens){
        bool unassigned = true;
        ast_manager & m = get_manager();
        for (const auto& var : variable_set) {
            expr_ref_vector eqClass(m);
            expr * constStrAst = collect_eq_nodes(var, eqClass);

            if (constStrAst == nullptr) {
                unassigned = false;
                freeVars.push_back(std::make_pair(var, varLens[var]));
            }
        }
        return unassigned;
    }

    bool theory_str::fixedLength(std::set<expr*> &freeVars, std::map<expr*, rational> &varLens){
        bool unassigned = true;
        for (const auto& var : variable_set) {
            rational lenVal;
            if (!get_len_value(var, lenVal)){
                unassigned = false;
                freeVars.insert(var);
            }
            else
                varLens[var] = lenVal;
        }
        return unassigned;
    }

    bool theory_str::propagate_concat(){
        clock_t t = clock();
        context & ctx = get_context();
        ast_manager & m = get_manager();
        expr_ref_vector assignments(m);
        ctx.get_assignments(assignments);
        bool axiomAdded = false;

        std::set<expr*> varSet;
        std::set<expr*> concatSet;
        std::map<expr*, int> exprLenMap;

        // collect all concats in context
        for (expr_ref_vector::iterator it = assignments.begin(); it != assignments.end(); ++it) {
            if (! ctx.is_relevant(*it)) {
                continue;
            }
            if (m.is_eq(*it)) {
                collect_var_concat(*it, varSet, concatSet);
            }
        }

        axiomAdded = axiomAdded || propagate_value(concatSet);
        axiomAdded = axiomAdded || propagate_length(varSet, concatSet, exprLenMap);
        STRACE("str", tout << __LINE__ <<  " time: " << __FUNCTION__ << ":  " << ((float)(clock() - t))/CLOCKS_PER_SEC << std::endl;);
        return axiomAdded;
    }

    /*
     *
     */
    bool  theory_str::propagate_value(std::set<expr*> & concatSet){
        ast_manager & m = get_manager();
        context & ctx = get_context();
        bool axiomAdded = false;
        // iterate each concat
        // if a concat doesn't have length info, check if the length of all leaf nodes can be resolved
        for (std::set<expr*>::iterator it = concatSet.begin(); it != concatSet.end(); it++) {
            app * concat = to_app(*it);

            expr * concat_lhs = concat->get_arg(0);
            expr * concat_rhs = concat->get_arg(1);
            expr_ref_vector eqLhs(m);
            collect_eq_nodes(concat_lhs, eqLhs);

            expr_ref_vector eqRhs(m);
            collect_eq_nodes(concat_rhs, eqRhs);

            rational len_lhs, len_rhs;
            bool has_len_lhs = get_len_value(concat_lhs, len_lhs);
            bool has_len_rhs = get_len_value(concat_rhs, len_rhs);

            expr_ref_vector eqNodeSet(m);
            collect_eq_nodes(*it, eqNodeSet);
            for (int i = 0; i < eqNodeSet.size(); ++i)
                if (eqNodeSet[i].get() != *it) {
                    rational len_i;
                    if (get_len_value(eqNodeSet[i].get(), len_i)) {
                        if (has_len_lhs && len_i == len_lhs) {

                            // left = var, right = emtpy
                            zstring empty("");
                            expr_ref_vector rhs_terms(m);

                            if (!eqLhs.contains(eqNodeSet[i].get()))
                                rhs_terms.push_back(ctx.mk_eq_atom(concat_lhs, eqNodeSet[i].get()));
                            if (!eqRhs.contains(mk_string(empty)))
                                rhs_terms.push_back(ctx.mk_eq_atom(concat_rhs, mk_string(empty)));

                            if (rhs_terms.size() > 0) {
                                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(*it, m) << " = "
                                                   << mk_pp(eqNodeSet[i].get(), m) << std::endl
                                                   << "LHS ~= " << mk_pp(eqNodeSet[i].get(), m) << " RHS ~= empty"
                                                   << std::endl;);
                                continue;
                                expr_ref_vector lhs_terms(m);
                                expr_ref expr1(ctx.mk_eq_atom(*it, eqNodeSet[i].get()), m);
                                expr_ref expr2(ctx.mk_eq_atom(mk_strlen(concat_lhs), mk_strlen(eqNodeSet[i].get())), m);

                                lhs_terms.push_back(expr1);
                                lhs_terms.push_back(expr2);

                                expr_ref lhs(mk_and(lhs_terms), m);
                                expr_ref rhs(mk_and(rhs_terms), m);
                                assert_implication(lhs, rhs);

                                axiomAdded = true;
                            }
                        }

                        if (has_len_rhs && len_i == len_rhs) {

                            // right = var, left = emtpy
                            zstring empty("");
                            expr_ref_vector rhs_terms(m);

                            if (!eqRhs.contains(eqNodeSet[i].get()))
                                rhs_terms.push_back(ctx.mk_eq_atom(concat_rhs, eqNodeSet[i].get()));
                            if (!eqLhs.contains(mk_string(empty)))
                                rhs_terms.push_back(ctx.mk_eq_atom(concat_lhs, mk_string(empty)));

                            if (rhs_terms.size() > 0) {
                                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(*it, m) << " = "
                                                   << mk_pp(eqNodeSet[i].get(), m) << std::endl
                                                   << "RHS ~= " << mk_pp(eqNodeSet[i].get(), m) << " LHS ~= empty"
                                                   << std::endl;);
                                continue;
                                expr_ref_vector lhs_terms(m);
                                expr_ref expr1(ctx.mk_eq_atom(*it, eqNodeSet[i].get()), m);
                                expr_ref expr2(ctx.mk_eq_atom(mk_strlen(concat_rhs), mk_strlen(eqNodeSet[i].get())), m);

                                lhs_terms.push_back(expr1);
                                lhs_terms.push_back(expr2);

                                expr_ref lhs(mk_and(lhs_terms), m);
                                expr_ref rhs(mk_and(rhs_terms), m);
                                assert_implication(lhs, rhs);

                                axiomAdded = true;
                            }
                        }
                    }

                    if (u.str.is_concat(eqNodeSet[i].get())) {
                        app *concat_i = to_app(eqNodeSet[i].get());
                        expr *i_lhs = concat_i->get_arg(0);
                        expr *i_rhs = concat_i->get_arg(1);
                        rational len_i_lhs, len_i_rhs;
                        if (get_len_value(i_lhs, len_i_lhs) && has_len_lhs && len_i_lhs == len_lhs) {

                            // left = left, right = right
                            expr_ref_vector rhs_terms(m);

                            if (!eqRhs.contains(i_rhs))
                                rhs_terms.push_back(ctx.mk_eq_atom(concat_rhs, i_rhs));
                            if (!eqLhs.contains(i_lhs))
                                rhs_terms.push_back(ctx.mk_eq_atom(concat_lhs, i_lhs));

                            if (rhs_terms.size() > 0) {
                                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(*it, m) << " = "
                                                   << mk_pp(eqNodeSet[i].get(), m) << std::endl
                                                   << "LHS ~= " << mk_pp(i_lhs, m) << " RHS ~= " << mk_pp(i_rhs, m)
                                                   << std::endl;);
                                continue;
                                expr_ref_vector lhs_terms(m);
                                expr_ref expr1(ctx.mk_eq_atom(*it, eqNodeSet[i].get()), m);
                                expr_ref expr2(ctx.mk_eq_atom(mk_strlen(concat_lhs), mk_strlen(i_lhs)), m);

                                lhs_terms.push_back(expr1);
                                lhs_terms.push_back(expr2);

                                expr_ref lhs(mk_and(lhs_terms), m);
                                expr_ref rhs(mk_and(rhs_terms), m);
                                assert_implication(lhs, rhs);

                                axiomAdded = true;
                            }
                        }

                        if (get_len_value(i_rhs, len_i_rhs) && has_len_rhs && len_i_rhs == len_rhs) {

                            // left = left, right = right
                            expr_ref_vector rhs_terms(m);

                            if (!eqRhs.contains(i_rhs))
                                rhs_terms.push_back(ctx.mk_eq_atom(concat_rhs, i_rhs));
                            if (!eqLhs.contains(i_lhs))
                                rhs_terms.push_back(ctx.mk_eq_atom(concat_lhs, i_lhs));

                            if (rhs_terms.size() > 0) {
                                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(*it, m) << " = "
                                                   << mk_pp(eqNodeSet[i].get(), m) << std::endl
                                                   << "LHS ~= " << mk_pp(i_lhs, m) << " RHS ~= " << mk_pp(i_rhs, m)
                                                   << std::endl;);
                                continue;
                                expr_ref_vector lhs_terms(m);
                                expr_ref expr1(ctx.mk_eq_atom(*it, eqNodeSet[i].get()), m);
                                expr_ref expr2(ctx.mk_eq_atom(mk_strlen(concat_rhs), mk_strlen(i_rhs)), m);

                                lhs_terms.push_back(expr1);
                                lhs_terms.push_back(expr2);

                                expr_ref lhs(mk_and(lhs_terms), m);
                                expr_ref rhs(mk_and(rhs_terms), m);
                                assert_implication(lhs, rhs);

                                axiomAdded = true;
                            }
                        }
                    }

                }

            // If the concat LHS and RHS both have a string constant in their EQC,
            // but the var does not, then we assert an axiom of the form
            // (lhs = "lhs" AND rhs = "rhs") --> (Concat lhs rhs) = "lhsrhs"
            bool concat_lhs_haseqc, concat_rhs_haseqc, concat_haseqc;
            expr * concat_lhs_str = get_eqc_value(concat_lhs, concat_lhs_haseqc);
            expr * concat_rhs_str = get_eqc_value(concat_rhs, concat_rhs_haseqc);
            expr * concat_str = get_eqc_value(*it, concat_haseqc);
            if (concat_lhs_haseqc && concat_rhs_haseqc && !concat_haseqc) {
                STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " " << mk_pp(*it, m) << " = " << mk_pp(concat, m) << std::endl
                                  << "LHS ~= " << mk_pp(concat_lhs_str, m) << " RHS ~= " << mk_pp(concat_rhs_str, m) << std::endl;);

                zstring lhsString, rhsString;
                u.str.is_string(concat_lhs_str, lhsString);
                u.str.is_string(concat_rhs_str, rhsString);

                if (lhsString.length() == 0 || rhsString.length() == 0)
                    continue;
                zstring concatString = lhsString + rhsString;

                // special handling: don't assert that string constants are equal to themselves
                expr_ref_vector lhs_terms(m);
                if (!u.str.is_string(concat_lhs)) {
                    lhs_terms.push_back(ctx.mk_eq_atom(concat_lhs, concat_lhs_str));
                }

                if (!u.str.is_string(concat_rhs)) {
                    lhs_terms.push_back(ctx.mk_eq_atom(concat_rhs, concat_rhs_str));
                }

                if (lhs_terms.empty()) {
                    // no assumptions on LHS
                    expr_ref rhs(ctx.mk_eq_atom(concat, mk_string(concatString)), m);
                    assert_axiom(rhs);
                } else {
                    expr_ref lhs(mk_and(lhs_terms), m);
                    expr_ref rhs(ctx.mk_eq_atom(concat, mk_string(concatString)), m);
                    assert_implication(lhs, rhs);
                }
                axiomAdded = true;
            }
            else if (!concat_lhs_haseqc && concat_rhs_haseqc && concat_haseqc) {
                STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " " << mk_pp(*it, m) << " = " << mk_pp(concat, m) << std::endl
                                  << "Concat ~= " << mk_pp(concat_str, m) << " RHS ~= " << mk_pp(concat_rhs_str, m) << std::endl;);

                zstring concatString, rhsString;
                u.str.is_string(concat_str, concatString);
                u.str.is_string(concat_rhs_str, rhsString);

                zstring lhsString = concatString.extract(0, concatString.length() - rhsString.length());

                // special handling: don't assert that string constants are equal to themselves
                expr_ref_vector terms(m);
                if (!u.str.is_string(*it)) {
                    terms.push_back(ctx.mk_eq_atom(*it, concat_str));
                }

                if (!u.str.is_string(concat_rhs)) {
                    terms.push_back(ctx.mk_eq_atom(concat_rhs, concat_rhs_str));
                }

                if (terms.empty()) {
                    // no assumptions on LHS
                    expr_ref rhs(ctx.mk_eq_atom(concat_lhs, mk_string(lhsString)), m);
                    assert_axiom(rhs);
                } else if (!are_equal_exprs(concat_lhs, mk_string(lhsString))){
                    expr_ref lhs(mk_and(terms), m);
                    expr_ref rhs(ctx.mk_eq_atom(concat_lhs, mk_string(lhsString)), m);
                    assert_implication(lhs, rhs);
                }

                axiomAdded = true;

            }
            else if (concat_lhs_haseqc && !concat_rhs_haseqc && concat_haseqc) {
                STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " " << mk_pp(*it, m) << " = " << mk_pp(concat, m) << std::endl
                                  << "Concat ~= " << mk_pp(concat_str, m) << " LHS ~= " << mk_pp(concat_lhs_str, m) << std::endl;);

                zstring concatString, lhsString;
                u.str.is_string(concat_str, concatString);
                u.str.is_string(concat_lhs_str, lhsString);
                zstring rhsString = concatString.extract(lhsString.length(), concatString.length() - lhsString.length());

                // special handling: don't assert that string constants are equal to themselves
                expr_ref_vector terms(m);
                if (!u.str.is_string(*it)) {
                    terms.push_back(ctx.mk_eq_atom(*it, concat_str));
                }

                if (!u.str.is_string(concat_lhs)) {
                    terms.push_back(ctx.mk_eq_atom(concat_lhs, concat_lhs_str));
                }

                if (terms.empty()) {
                    // no assumptions on LHS
                    expr_ref rhs(ctx.mk_eq_atom(concat_rhs, mk_string(rhsString)), m);
                    assert_axiom(rhs);
                } else if (!are_equal_exprs(concat_rhs, mk_string(rhsString))){
                    expr_ref lhs(mk_and(terms), m);
                    expr_ref rhs(ctx.mk_eq_atom(concat_rhs, mk_string(rhsString)), m);
                    assert_implication(lhs, rhs);
                }

                axiomAdded = true;
            }
            else if (!concat_lhs_haseqc && !concat_rhs_haseqc && concat_haseqc) {
                rational lhs_len, rhs_len;
                if (get_len_value(concat_lhs, lhs_len)){
                    STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " " << mk_pp(*it, m) << " = " << mk_pp(concat, m) << std::endl
                                      << "Concat ~= " << mk_pp(concat_str, m) << " | LHS | ~= " << lhs_len << std::endl;);
                    zstring concatString;
                    u.str.is_string(concat_str, concatString);

                    zstring lhsString = concatString.extract(0, lhs_len.get_int64());
                    zstring rhsString = concatString.extract(lhs_len.get_int64(), concatString.length() - lhsString.length());

                    expr_ref_vector lhs_terms(m), rhs_terms(m);
                    if (!u.str.is_string(*it)) {
                        lhs_terms.push_back(ctx.mk_eq_atom(*it, concat_str));
                    }

                    lhs_terms.push_back(ctx.mk_eq_atom(mk_int(lhs_len), mk_strlen(concat_lhs)));

                    expr_ref lhs(mk_and(lhs_terms), m);

                    expr_ref rhs_val(ctx.mk_eq_atom(concat_rhs, mk_string(rhsString)), m);
                    expr_ref lhs_val(ctx.mk_eq_atom(concat_lhs, mk_string(lhsString)), m);
                    rhs_terms.push_back(rhs_val);
                    rhs_terms.push_back(lhs_val);
                    expr_ref rhs(mk_and(rhs_terms), m);

                    assert_implication(lhs, rhs);
                    axiomAdded = true;
                }

                else if (get_len_value(concat_rhs, rhs_len)){
                    STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " " << mk_pp(*it, m) << " = " << mk_pp(concat, m) << std::endl
                                      << "Concat ~= " << mk_pp(concat_str, m) << " | RHS | ~= " << rhs_len << std::endl;);
                    zstring concatString;
                    u.str.is_string(concat_str, concatString);

                    zstring lhsString = concatString.extract(0, concatString.length() - rhs_len.get_int64());
                    zstring rhsString = concatString.extract(concatString.length() - rhs_len.get_int64(), rhs_len.get_int64());

                    expr_ref_vector lhs_terms(m), rhs_terms(m);
                    if (!u.str.is_string(*it)) {
                        lhs_terms.push_back(ctx.mk_eq_atom(*it, concat_str));
                    }

                    lhs_terms.push_back(ctx.mk_eq_atom(mk_int(rhs_len), mk_strlen(concat_rhs)));

                    expr_ref lhs(mk_and(lhs_terms), m);

                    expr_ref rhs_val(ctx.mk_eq_atom(concat_rhs, mk_string(rhsString)), m);
                    expr_ref lhs_val(ctx.mk_eq_atom(concat_lhs, mk_string(lhsString)), m);
                    rhs_terms.push_back(rhs_val);
                    rhs_terms.push_back(lhs_val);
                    expr_ref rhs(mk_and(rhs_terms), m);

                    assert_implication(lhs, rhs);
                    axiomAdded = true;
                }
            }
        }
        return axiomAdded;
    }

    bool theory_str::propagate_length(std::set<expr*> & varSet, std::set<expr*> & concatSet, std::map<expr*, int> & exprLenMap) {
        context & ctx = get_context();
        ast_manager & m = get_manager();
        bool axiomAdded = false;

        // iterate each concat
        // if a concat doesn't have length info, check if the length of all leaf nodes can be resolved
        for (std::set<expr*>::iterator it = concatSet.begin(); it != concatSet.end(); it++) {
            expr * concat = *it;
            rational lenValue;
            expr_ref concatlenExpr (mk_strlen(concat), m) ;
            bool allLeafResolved = true;
            if (! get_arith_value(concatlenExpr, lenValue)) {
                // the length of concat is unresolved yet
                if (get_len_value(concat, lenValue)) {
                    // but all leaf nodes have length information
                    TRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " " <<  mk_ismt2_pp(concat, m) << "| = " << lenValue << std::endl;);
                    std::set<expr*> leafNodes;
                    get_unique_non_concat_nodes(concat, leafNodes);
                    expr_ref_vector l_items(m);
                    for (std::set<expr*>::iterator leafIt = leafNodes.begin(); leafIt != leafNodes.end(); ++leafIt) {
                        rational leafLenValue;
                        if (get_len_value(*leafIt, leafLenValue)) {
                            expr_ref leafItLenExpr (mk_strlen(*leafIt), m);
                            expr_ref leafLenValueExpr (mk_int(leafLenValue), m);
                            expr_ref lcExpr (ctx.mk_eq_atom(leafItLenExpr, leafLenValueExpr), m);
                            l_items.push_back(lcExpr);
                        } else {
                            allLeafResolved = false;
                            break;
                        }
                    }
                    if (allLeafResolved) {
                        expr_ref axl(m.mk_and(l_items.size(), l_items.c_ptr()), m);
                        expr_ref lenValueExpr (mk_int(lenValue), m);
                        expr_ref axr(ctx.mk_eq_atom(concatlenExpr, lenValueExpr), m);
                        assert_implication(axl, axr);
                        axiomAdded = true;
                    }
                }
            }
            else {
                TRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " " <<  mk_ismt2_pp(concat, m) << "  --->  " << lenValue << std::endl;);
                // infer child len from concat len
                ptr_vector<expr> leafNodes;
                get_nodes_in_concat(concat, leafNodes);
                std::map<expr*, int> unresolvedNodes;
                expr_ref_vector l_items(m);

                expr_ref concatLenValueExpr (mk_int(lenValue), m);
                expr_ref lcExpr (ctx.mk_eq_atom(concatlenExpr, concatLenValueExpr), m);
                l_items.push_back(lcExpr);
                int pos = -1;
                for (int i = 0; i < leafNodes.size(); ++i) {
                    rational leafLenValue;
                    if (get_len_value(leafNodes[i], leafLenValue)) {
                        expr_ref leafItLenExpr (mk_strlen(leafNodes[i]), m);
                        expr_ref leafLenValueExpr (mk_int(leafLenValue), m);
                        expr_ref lcExpr (ctx.mk_eq_atom(leafItLenExpr, leafLenValueExpr), m);
                        l_items.push_back(lcExpr);

                        lenValue = lenValue - leafLenValue;
                    } else {
                        if (unresolvedNodes.find(leafNodes[i]) == unresolvedNodes.end()) {
                            unresolvedNodes[leafNodes[i]] = 1;
                            if (unresolvedNodes.size() > 1)
                                break;
                            pos = i;
                        }
                        else
                            unresolvedNodes[leafNodes[i]] = unresolvedNodes[leafNodes[i]] + 1;
                    }
                }

                if (unresolvedNodes.size() == 1){
                    STRACE("str", tout <<  " Number of unresolved nodes  " << unresolvedNodes.size() << " at " << mk_ismt2_pp(leafNodes[pos], m) <<  std::endl;);
                    // get the node
                    SASSERT(pos != -1);
                    rational tmp(unresolvedNodes[leafNodes[pos]]);
                    rational newLen = div(lenValue, tmp);
                    expr_ref nodeLenExpr (mk_strlen(leafNodes[pos]), m) ;

                    expr_ref axl(m.mk_and(l_items.size(), l_items.c_ptr()), m);
                    expr_ref lenValueExpr (mk_int(newLen), m);
                    expr_ref axr(ctx.mk_eq_atom(nodeLenExpr, lenValueExpr), m);
                    assert_implication(axl, axr);
                    STRACE("str", tout <<  mk_ismt2_pp(axl, m) << "  --->  " <<  mk_ismt2_pp(axr, m)<< std::endl;);
                    axiomAdded = true;
                }
                else {
                    STRACE("str", tout <<  " Number of unresolved nodes  " << unresolvedNodes.size() << std::endl;);
                }
            }
        }

        // if no concat length is propagated, check the length of variables.
        if (! axiomAdded) {
            for (std::set<expr*>::iterator it = varSet.begin(); it != varSet.end(); it++) {
                expr * var = *it;
                rational lenValue;
                expr_ref varlen (mk_strlen(var), m) ;
                if (! get_arith_value(varlen, lenValue)) {
                    if (propagate_length_within_eqc(var)) {
                        axiomAdded = true;
                    }
                }
            }

        }
        return axiomAdded;
    }

    void theory_str::collect_var_concat(expr * node, std::set<expr*> & varSet, std::set<expr*> & concatSet) {
        if (variable_set.find(node) != variable_set.end()) {
            varSet.insert(node);
        }
        else if (is_app(node)) {
            app * aNode = to_app(node);
            if (u.str.is_length(aNode)) {
                // Length
                return;
            }
            if (u.str.is_concat(aNode)) {
                if (concatSet.find(node) == concatSet.end()) {
                    concatSet.insert(node);
                }
            }
            // recursively visit all arguments
            for (unsigned i = 0; i < aNode->get_num_args(); ++i) {
                expr * arg = aNode->get_arg(i);
                collect_var_concat(arg, varSet, concatSet);
            }
        }
    }

    void theory_str::get_unique_non_concat_nodes(expr * node, std::set<expr*> & argSet) {
        app * a_node = to_app(node);
        if (!u.str.is_concat(a_node)) {
            argSet.insert(node);
            return;
        } else {
            SASSERT(a_node->get_num_args() == 2);
            expr * leftArg = a_node->get_arg(0);
            expr * rightArg = a_node->get_arg(1);
            get_unique_non_concat_nodes(leftArg, argSet);
            get_unique_non_concat_nodes(rightArg, argSet);
        }
    }

    bool theory_str::propagate_length_within_eqc(expr * var) {
        bool res = false;
        ast_manager & m = get_manager();
        context & ctx = get_context();

        TRACE("str", tout << __FUNCTION__ << ": " << mk_ismt2_pp(var, m) << std::endl ;);

        rational varLen;
        if (! get_len_value(var, varLen)) {
            bool hasLen = false;
            expr * nodeWithLen= var;
            do {
                if (get_len_value(nodeWithLen, varLen)) {
                    hasLen = true;
                    break;
                }
                nodeWithLen = get_eqc_next(nodeWithLen);
            } while (nodeWithLen != var);

            if (hasLen) {
                // var = nodeWithLen --> |var| = |nodeWithLen|
                expr_ref_vector l_items(m);
                expr_ref varEqNode(ctx.mk_eq_atom(var, nodeWithLen), m);
                l_items.push_back(varEqNode);

                expr_ref nodeWithLenExpr (mk_strlen(nodeWithLen), m);
                expr_ref varLenExpr (mk_int(varLen), m);
                expr_ref lenEqNum(ctx.mk_eq_atom(nodeWithLenExpr, varLenExpr), m);
                l_items.push_back(lenEqNum);

                expr_ref axl(m.mk_and(l_items.size(), l_items.c_ptr()), m);
                expr_ref varLen(mk_strlen(var), m);
                expr_ref axr(ctx.mk_eq_atom(varLen, mk_int(varLen)), m);
                assert_implication(axl, axr);
                STRACE("str", tout <<  mk_ismt2_pp(axl, m) << std::endl << "  --->  " << std::endl <<  mk_ismt2_pp(axr, m););
                res = true;
            }
        }
        return res;
    }

    bool theory_str::underapproximation(
            std::map<expr*, std::set<expr*>> eq_combination,
            std::set<std::pair<expr*, int>> non_fresh_vars) {
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** (" << m_scope_level << "/" << mful_scope_levels.size() << ")" << connectingSize << std::endl;);
        ast_manager & m = get_manager();
        context & ctx = get_context();
        print_eq_combination(eq_combination, __LINE__);

        expr_ref_vector guessedEqs(m), guessedDisEqs(m);
        fetch_guessed_exprs_with_scopes(guessedEqs, guessedDisEqs);
        fetch_guessed_core_exprs(eq_combination, guessedEqs, guessedDisEqs);
        const str::state &root = build_state_from_memo();
        UnderApproxState state(m, get_actual_trau_lvl(), get_actual_trau_lvl(), eq_combination, non_fresh_vars, guessedEqs, guessedDisEqs, root, str_int_bound);

        if (is_equal(uState, state)) {
            bool axiomAdded = assert_state(guessedEqs, guessedDisEqs, root);
            return axiomAdded;
        }
        else {
            uState = state;
            uState.str_int_bound = str_int_bound;
            completedStates.push_back(uState);
        }

        std::map<expr*, int> non_fresh_map = set2map(non_fresh_vars);

        init_underapprox(eq_combination, non_fresh_map);

        handle_diseq();

        bool axiomAdded = handle_str_int();
        axiomAdded = convert_equalities(mapset2mapvector(eq_combination), non_fresh_map, createAndOperator(guessedEqs)) || axiomAdded;

        return axiomAdded;
    }

    bool theory_str::assert_state(expr_ref_vector guessedEqs, expr_ref_vector guessedDisEqs, str::state root){
        expr_ref_vector corePrev(get_manager());
        fetch_guessed_exprs_from_cache(uState, corePrev);

        // update guessed exprs
        uState.equalities.reset();
        uState.equalities.append(guessedEqs);

        uState.disequalities.reset();
        uState.disequalities.append(guessedDisEqs);

        bool axiomAdded = false;
//            if (!is_weaker_expr_sets(guessedEqs, corePrev)) {
        if (is_equal(corePrev, guessedEqs)) {
            axiomAdded = true;
            underapproximation_cached();
            handle_diseq(true);
            uState.eqLevel = get_actual_trau_lvl();
            uState.diseqLevel = get_actual_trau_lvl();
        }
        else if (!uState.reassertDisEQ){
            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " reassertDisEQ = false " << uState.diseqLevel << std::endl;);
            handle_diseq(true);
            uState.diseqLevel = get_actual_trau_lvl();
            axiomAdded = true;
        }
        uState.currState = root;
        uState.reassertEQ = true;
        uState.reassertDisEQ = true;
        return axiomAdded;
    }

    bool theory_str::handle_str_int(){
        if (string_int_conversion_terms.size() > 0) {

            ast_manager & m = get_manager();
            STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << std::endl;);
            expr_ref_vector guessedEqs(m), guessedDisEqs(m);
            fetch_guessed_str_int_with_scopes(guessedEqs, guessedDisEqs);
            for (const auto &e : guessedEqs) {
                STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " " << mk_pp(e, get_manager()) << std::endl;);
                app* a = to_app(e);
                if (u.str.is_stoi(a->get_arg(0))){
                    expr* s = to_app(a->get_arg(0))->get_arg(0);
                    if (!m_autil.is_numeral(a->get_arg(1)))
                        handle_str2int(a->get_arg(1), s);
                }
                else if (u.str.is_itos(a->get_arg(0))){
                    expr* num = to_app(a->get_arg(0))->get_arg(0);
                    if (!m_autil.is_numeral(num))
                        handle_int2str(num, a->get_arg(1));
                }
                else if (u.str.is_stoi(a->get_arg(1))){
                    expr* s = to_app(a->get_arg(1))->get_arg(0);
                    if (!m_autil.is_numeral(a->get_arg(0)))
                        handle_str2int(a->get_arg(0), s);
                }
                else if (u.str.is_itos(a->get_arg(1))){
                    expr* num = to_app(a->get_arg(1))->get_arg(0);
                    if (!m_autil.is_numeral(num))
                        handle_int2str(num, a->get_arg(0));
                }
            }

            for (const auto &e : guessedDisEqs) {
                app* a = to_app(to_app(e)->get_arg(0));
                STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " " << mk_pp(a, get_manager()) << std::endl;);
                if (u.str.is_stoi(a->get_arg(0))){
                    expr* s = to_app(a->get_arg(0))->get_arg(0);
                    if (!m_autil.is_numeral(a->get_arg(1)))
                        handle_str2int(a->get_arg(1), s);
                }
                else if (u.str.is_itos(a->get_arg(0))){
                    expr* num = to_app(a->get_arg(0))->get_arg(0);
                    if (!m_autil.is_numeral(num))
                        handle_int2str(num, a->get_arg(1));
                }
                else if (u.str.is_stoi(a->get_arg(1))){
                    expr* s = to_app(a->get_arg(1))->get_arg(0);
                    if (!m_autil.is_numeral(a->get_arg(0)))
                        handle_str2int(a->get_arg(0), s);
                }
                else if (u.str.is_itos(a->get_arg(1))){
                    expr* num = to_app(a->get_arg(1))->get_arg(0);
                    if (!m_autil.is_numeral(num))
                        handle_int2str(num, a->get_arg(0));
                }
            }
            return true;
        }
        return false;
    }

    void theory_str::handle_str2int(expr* num, expr* str){
        ast_manager & m = get_manager();
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << std::endl;);
        expr* unrollConstraint = unroll_str_int(num, str);
        expr* lenConstraint = lower_bound_str_int(num, str);
        expr* boundConstraint = createEqualOperator(get_bound_str_int_control_var(), mk_int(str_int_bound));
        expr* fill_0 = fill_0_1st_loop(num, str);
        rational max_value = ten_power(str_int_bound) - rational(1);
        expr_ref_vector conclusions(m);

//        conclusions.push_back(lenConstraint);
        conclusions.push_back(unrollConstraint);
        conclusions.push_back(createLessEqOperator(num, mk_int(max_value)));
        conclusions.push_back(fill_0);

        expr_ref_vector premises(m);
        premises.push_back(boundConstraint);
        premises.push_back(createEqualOperator(num, u.str.mk_stoi(str)));

        expr* to_assert = rewrite_implication(createAndOperator(premises), createAndOperator(conclusions));
        assert_axiom(to_assert);
        impliedFacts.push_back(to_assert);
    }

    void theory_str::handle_int2str(expr* num, expr* str){
        ast_manager & m = get_manager();
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << std::endl;);
        expr* unrollConstraint = unroll_str_int(num, str);
        expr* lenConstraint = lower_bound_int_str(num, str);
        expr* boundConstraint = createEqualOperator(get_bound_str_int_control_var(), mk_int(str_int_bound));
        expr* fill_0 = fill_0_1st_loop(num, str);

        rational max_value = ten_power(str_int_bound) - rational(1);

        expr_ref_vector conclusions(m);

//        conclusions.push_back(lenConstraint);
        conclusions.push_back(unrollConstraint);
        conclusions.push_back(createLessEqOperator(num, mk_int(max_value)));
        conclusions.push_back(fill_0);

        expr_ref_vector premises(m);
        premises.push_back(boundConstraint);
        premises.push_back(createEqualOperator(str, u.str.mk_itos(num)));

        expr* to_assert = rewrite_implication(createAndOperator(premises), createAndOperator(conclusions));
        assert_axiom(to_assert);
        impliedFacts.push_back(to_assert);
    }

    expr* theory_str::unroll_str2int(expr* n){
        ast_manager & m = get_manager();
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " " << mk_pp(n, m) << std::endl;);
        rational ten(10);
        rational zero(0);
        rational zeroChar(48);
        rational coeff(1);
        expr_ref_vector adds(m);
        rational pos = str_int_bound - rational(1);
        expr* arr = getExprVarFlatArray(n);
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " " << mk_pp(arr, m) << std::endl;);
        while (pos >= zero){
            STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " " << mk_pp(createSelectOperator(arr, mk_int(pos)), m) << std::endl;);
            STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " " << mk_pp(createMultiplyOperator(createSelectOperator(arr, mk_int(pos)), mk_int(coeff)), m) << std::endl;);
            adds.push_back(createMultiplyOperator(createSelectOperator(arr, mk_int(pos)), mk_int(coeff)));
            rational base = zeroChar * coeff * rational(-1);
            adds.push_back(mk_int(base));
            pos = pos - 1;
            coeff = coeff * ten;
        }
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " " << mk_pp(createAddOperator(adds), m) << std::endl;);
        return createAddOperator(adds);
    }

    expr* theory_str::unroll_str_int(expr* num, expr* str){
        ast_manager & m = get_manager();
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " " << mk_pp(str, m) << std::endl;);
        rational ten(10);
        rational one(1);
        rational zero(0);
        rational zeroChar(48);
        rational pos = str_int_bound - one;
        expr* arr = getExprVarFlatArray(str);
        SASSERT(arr);
        expr* strLen = mk_strlen(str);
        expr_ref_vector ands(m);
        ands.push_back(rewrite_implication(createEqualOperator(strLen, mk_int(0)), createEqualOperator(num, mk_int(- 1))));


        expr_ref_vector ands_tmp(m);
        for (rational len = one; len <= str_int_bound; len = len + one) {
            expr_ref_vector adds(m);
            rational pos = len - one;
            rational coeff(1);
            while (pos >= zero) {
                expr* at_pos = nullptr;
                if (len == str_int_bound) {
                    expr_ref_vector adds_tmp(m);
                    adds_tmp.push_back(strLen);
                    rational tmp = rational(-1) * str_int_bound + pos;
                    adds_tmp.push_back(mk_int(tmp));
                    at_pos = createSelectOperator(arr, createAddOperator(adds_tmp));
                }
                else
                    at_pos = createSelectOperator(arr, mk_int(pos));
                adds.push_back(createMultiplyOperator(at_pos, mk_int(coeff)));
                rational base = zeroChar * coeff * rational(-1);
                adds.push_back(mk_int(base));
                pos = pos - 1;
                coeff = coeff * ten;
            }

            expr* premise = nullptr;
            if (len == str_int_bound)
                premise = createGreaterEqOperator(strLen, mk_int(len));
            else
                premise = createEqualOperator(strLen, mk_int(len));
            expr* conclusion = createEqualOperator(num, createAddOperator(adds));
            ands_tmp.push_back(rewrite_implication(premise, conclusion));
        }

        // if !valid --> value = -1, else ands_tmp
        expr* valid_s2i = valid_str_int(str);
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " valid_s2i: " << mk_pp(valid_s2i, m) << std::endl;);
        ands.push_back(rewrite_implication(valid_s2i, createAndOperator(ands_tmp)));
        ands.push_back(rewrite_implication(mk_not(m, valid_s2i), createEqualOperator(num, mk_int(- 1))));
        return createAndOperator(ands);
    }

    expr* theory_str::valid_str_int(expr* str){
        // from 0 - q_bound
        ast_manager & m = get_manager();
        expr_ref_vector ands(m);
        expr* arr = getExprVarFlatArray(str);
        expr* strLen = mk_strlen(str);
        for (int i = 0; i < q_bound.get_int64(); ++i) {
            expr* premise = createGreaterEqOperator(strLen, mk_int(i + 1));
            expr_ref_vector conclusions(m);
            conclusions.push_back(createGreaterEqOperator(
                    createSelectOperator(arr, mk_int(i)),
                    mk_int('0')));
            conclusions.push_back(createLessEqOperator(
                    createSelectOperator(arr, mk_int(i)),
                    mk_int('9')));
            ands.push_back(rewrite_implication(premise, createAndOperator(conclusions)));
        }

        for (int i = 0; i < str_int_bound; ++i){
            expr* premise = createGreaterEqOperator(strLen, mk_int(q_bound.get_int64() + i));
            rational to_minus = rational(-1) * rational(i);
            expr* pos = createAddOperator(strLen, mk_int(to_minus));

            expr_ref_vector conclusions(m);
            conclusions.push_back(createGreaterEqOperator(
                    createSelectOperator(arr, pos),
                    mk_int('0')));
            conclusions.push_back(createLessEqOperator(
                    createSelectOperator(arr, pos),
                    mk_int('9')));
            ands.push_back(rewrite_implication(premise, createAndOperator(conclusions)));
        }
        return createAndOperator(ands);
    }

    /*
     * 0 <= val < 10 --> len < 2
     * 10 <= val < 100 --> len < 3
     * ..
     * -1 >= val > -10 --> len < 3
     * -10 >= val > -100 --> len < 4
     */
    expr* theory_str::lower_bound_str_int(expr* num, expr* str){
        ast_manager & m = get_manager();
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " " << mk_pp(num, m) << " " << mk_pp(str, m) << std::endl;);
        expr_ref_vector ands(m);

        rational ten(10);
        rational powerOf(1);
        rational one(1);
        rational len(1);
        rational zero(0);
        rational prePower(0);
        rational minusOne = zero - one;
        expr* len_e = mk_strlen(str);
        while (len < str_int_bound){
            len = len + 1;
            powerOf = powerOf * ten; // 10^len
            expr* premise = createGreaterEqOperator(num, mk_int(powerOf));
            expr* conclusion = createGreaterEqOperator(len_e, mk_int(len));
            ands.push_back(rewrite_implication(premise, conclusion));
        }
//        ands.push_back(createLessEqOperator(len_e, mk_int(str_int_bound)));
        return createAndOperator(ands);
    }

    /*
     * 0 <= val < 10 --> len < 2
     * 10 <= val < 100 --> len < 3
     * ...
     */
    expr* theory_str::lower_bound_int_str(expr* num, expr* str){
        ast_manager & m = get_manager();
        expr_ref_vector ands(m);

        rational ten(10);
        rational powerOf(1);
        rational one(1);
        rational len(1);
        rational zero(0);
        rational prePower(0);
        rational minusOne = zero - one;
        expr* len_e = mk_strlen(str);
        while (len <= str_int_bound){
            len = len + 1;
            powerOf = powerOf * ten; // 10^len

            rational powerOf_minus_one = powerOf - one;
            rational len_minus_one = len - one;

            // positive number
            expr_ref_vector tmpAnds(m);
            tmpAnds.push_back(createGreaterEqOperator(num, mk_int(prePower)));
            tmpAnds.push_back(createLessEqOperator(num, mk_int(powerOf_minus_one)));
            ands.push_back(rewrite_implication(
                    createAndOperator(tmpAnds),
                    createEqualOperator(mk_strlen(str), mk_int(len_minus_one))));
            prePower = powerOf;
        }
        ands.push_back(createLessEqOperator(len_e, mk_int(str_int_bound)));
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(createAndOperator(ands), m) << std::endl;);
        return createAndOperator(ands);
    }

    expr* theory_str::fill_0_1st_loop(expr* num, expr* str){
        ast_manager & m = get_manager();
        expr_ref_vector ands(m);

        rational one(1);
        rational len = str_int_bound;
        rational zero_char(48);
        expr* zero_e = mk_int(zero_char);
        expr* arr = getExprVarFlatArray(str);
        expr* len_n = mk_strlen(str);

        while (len < str_int_bound + q_bound){
            expr* premise = createGreaterEqOperator(len_n, mk_int(len));

            rational tmp = len - str_int_bound;
            expr* conclusion = createEqualOperator(createSelectOperator(arr, mk_int(tmp)), zero_e);
            ands.push_back(rewrite_implication(premise, conclusion));
            len = len + 1;
        }

        expr* premise = createGreaterEqOperator(num, mk_int(0));

        return rewrite_implication(premise, createAndOperator(ands));
    }


    std::map<expr*, std::vector<expr*>> theory_str::mapset2mapvector(std::map<expr*, std::set<expr*>> m){
        std::map<expr*, std::vector<expr*>> ret;
        for (const auto& v : m){
            std::vector<expr*> tmp(v.second.begin(), v.second.end());
            ret[v.first] = tmp;
        }
        return ret;
    }

    std::map<expr*, int> theory_str::set2map(std::set<std::pair<expr*, int>> s){
        std::map<expr*, int> ret;
        for (const auto& p : s)
            ret[p.first] = p.second;
        return ret;
    }

    void theory_str::print_eq_combination(std::map<expr*, std::set<expr*>> eq_combination, int line){
        ast_manager & m = get_manager();
        for (const auto& com : eq_combination){
            if (line > 0) {
                STRACE("str", tout << line << " EQ set of " << mk_pp(com.first, m) << std::endl;);
            }
            else
                STRACE("str", tout << "EQ set of " << mk_pp(com.first, m) << std::endl;);
            for (const auto& e : com.second)
            STRACE("str",
                   if (!u.str.is_concat(e))
                       tout << "\t\t" << mk_pp(e, m) << std::endl;
                   else {
                       ptr_vector<expr> childrenVector;
                       get_nodes_in_concat(e, childrenVector);
                       tout << "\t\t";
                       for (int i = 0; i < childrenVector.size(); ++i)
                           tout << mk_pp(childrenVector[i], m)  << " ";
                       tout << std::endl;
                   });
        }
    }

    bool theory_str::is_equal(UnderApproxState preState, UnderApproxState currState){
        return false;
        ast_manager & m = get_manager();
        std::map<expr*, std::set<expr*>> _eq_combination = preState.eq_combination;

        if (_eq_combination.size() != currState.eq_combination.size()) {
            STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << ": " << _eq_combination.size() << " vs " << currState.eq_combination.size() <<  std::endl;);
            return false;
        }

        for (const auto& v : currState.non_fresh_vars)
            if (preState.non_fresh_vars.find(v) == preState.non_fresh_vars.end()) {
                expr_ref_vector eqs(m);
                collect_eq_nodes(v.first, eqs);
                bool found = false;
                for (const auto& eq : eqs)
                    // check if there are any equivalent variables
                    if (preState.non_fresh_vars.find(std::make_pair(eq, v.second)) != preState.non_fresh_vars.end()) {
                        found = true;
                        break;
                    }

                if (!found) {
                    STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " NOT EQ " << mk_pp(v.first, m)
                                       << std::endl;);
                    return false;
                }
            }

        std::set<expr*> checked;

        for (const auto& n : currState.eq_combination) {
            std::set<expr*> comb;
            if (_eq_combination.find(n.first) != _eq_combination.end()) {
                comb = _eq_combination[n.first];
                checked.insert(n.first);
            }
            else {
                // check if there are any equivalent combinations
                expr_ref_vector eqs(m);
                collect_eq_nodes(n.first, eqs);
                for (const auto& eq : eqs)
                    if (_eq_combination.find(eq) != _eq_combination.end()){
                        comb = _eq_combination[eq];
                        checked.insert(eq);
                        break;
                    }
            }


            for (const auto &e : n.second) {

                if (comb.find(e) == comb.end()) {
                    // check if there are any equivalent combinations, can be the case that some empty variables are omitted
                    if (!are_some_empty_vars_omitted(e, comb)) {
                        STRACE("str",
                               tout << __LINE__ << " *** " << __FUNCTION__ << " NOT EQ " << mk_pp(n.first, m) << " == "
                                    << mk_pp(e, m) << std::endl;);
                        return false;
                    }
                }
                else {
                    // it is ok if some elements missing because if its size = 0
                }
            }
        }

        if (currState.eq_combination.size() < preState.eq_combination.size()) {
            // check if all missing combinations are trivial
            for (const auto& n : preState.eq_combination)
                if (checked.find(n.first) == checked.end()) {
                    // it is not in currState.eq_combination
                    if (!is_trivial_combination(n.first, n.second, currState.non_fresh_vars))
                        return false;
                }
        }

        return true;
    }

    bool theory_str::are_some_empty_vars_omitted(expr* n, std::set<expr*> v){
        ast_manager & m = get_manager();
        ptr_vector <expr> elements;
        get_nodes_in_concat(n, elements);
        rational len;
        for (const auto& nn : v){
            ptr_vector <expr> tmp;
            get_nodes_in_concat(nn, tmp);
            if (elements.size() <= tmp.size()){
                int pos = 0;

                for (int i = 0; i < tmp.size(); ++i){
                    if (get_len_value(tmp[i], len) && len.get_int64() == 0) // skip empty vars
                        continue;

                    if (elements.size() <= i)
                        break;
                    else if (elements[pos] != tmp[i]) {
                        // check equivalent class
                        expr_ref_vector eqs(m);
                        collect_eq_nodes(tmp[i], eqs);
                        if (!eqs.contains(elements[pos]))
                            break;
                    }

                    pos++;
                }

                // reach the end
                if (pos == elements.size())
                    return true;
            }
        }
        return false;
    }

    bool theory_str::is_equal(expr_ref_vector corePrev, expr_ref_vector coreCurr){
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << std::endl;);
        ast_manager & m = get_manager();

        if (coreCurr.size() != corePrev.size())
            return false;

        for (const auto& e : coreCurr)
            if (!corePrev.contains(e))
                return false;

        return true;
    }

    bool theory_str::is_weaker_expr_sets(expr_ref_vector curr, expr_ref_vector prev){
        ast_manager & m = get_manager();
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << curr.size() << " vs " << curr.size() << std::endl;);
        // check if prev is WEAKER than curr, means all exprs in prev are in curr
        for (const auto& e : prev) {
            STRACE("str",
                   tout << __LINE__ << " prev eq " << mk_pp(e, m) << std::endl;);

            if (!curr.contains(e)) {
                STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** return false" << std::endl;);
                return false;
            }
        }

        for (const auto& e : curr)
            STRACE("str",
               tout << __LINE__ << " curr eq " << mk_pp(e, m) << std::endl;);
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** return true" << std::endl;);
        return true;
    }

    bool theory_str::underapproximation_cached(){
        ast_manager & m = get_manager();
        context & ctx = get_context();

        expr_ref_vector guessedExprs(m);
        fetch_guessed_exprs_from_cache(uState, guessedExprs);
        expr* causexpr = createAndOperator(guessedExprs);

        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** eqLevel = " << uState.eqLevel << "; bound = " << uState.str_int_bound << " @lvl " << m_scope_level << std::endl;);
        if (uState.assertingConstraints.size() > 0)
            init_underapprox_cached();
        bool axiomAdded = false;

        for (const auto& a : uState.assertingConstraints){
            axiomAdded = true;
            ensure_enode(a);

            if (m.is_and(a)) {
                assert_axiom(rewrite_implication(causexpr, a));
            }
            else
                assert_axiom(a);
        }
        return axiomAdded;
    }

    void theory_str::handle_diseq(bool cached){
//        return;
        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " cached = " << cached << " @lvl " << m_scope_level << "\n";);
        if (!cached){
            handle_NOTEqual();
            handle_NOTContain();
        }
        else {
            handle_NOTEqual_cached();
            handle_NOTContain_cached();
        }

    }

    void theory_str::handle_NOTEqual(){
        for (const auto &wi : m_wi_expr_memo) {
            if (!u.str.is_empty(wi.second.get()) && !u.str.is_empty(wi.first.get())) {
                expr* lhs = wi.first.get();
                expr* rhs = wi.second.get();
                expr* contain = nullptr;
                if (!is_contain_equality(lhs, contain) && !is_contain_equality(rhs, contain)) {
                    handle_NOTEqual(lhs, rhs);
                }
            }
        }
    }

    void theory_str::handle_NOTEqual_cached(){
        for (const auto &wi : uState.disequalities) {
            SASSERT(to_app(wi)->get_num_args() == 1);
            expr* equality = to_app(wi)->get_arg(0);

            SASSERT(to_app(equality)->get_num_args() == 2);
            expr* lhs = to_app(equality)->get_arg(0);
            expr* rhs = to_app(equality)->get_arg(1);
            if (!u.str.is_empty(lhs) && !u.str.is_empty(lhs)) {
                expr* contain = nullptr;
                if (!is_contain_equality(lhs, contain) && !is_contain_equality(rhs, contain)) {
                    handle_NOTEqual(lhs, rhs);
                }
            }
        }
    }

    void theory_str::handle_NOTEqual(expr* lhs, expr* rhs){
        expr* contain = nullptr;
        if (!is_contain_equality(lhs, contain) && !is_contain_equality(rhs, contain)) {
            ast_manager & m = get_manager();
            expr_ref_vector eqLhs(m);
            expr_ref_vector eqRhs(m);
            expr* constLhs = collect_eq_nodes(lhs, eqLhs);
            expr* constRhs = collect_eq_nodes(rhs, eqRhs);
            if (constLhs != nullptr && constRhs != nullptr) {
                STRACE("str", tout << __LINE__ <<  " simple not (" << mk_pp(lhs, m) << " = " << mk_pp(rhs, m) << ")\n";);
                STRACE("str", tout << __LINE__ <<  " simple not (" << mk_pp(constLhs, m) << " = " << mk_pp(constRhs, m) << ")\n";);
                return;
            }
            zstring value;

            if (constLhs != nullptr && u.str.is_string(constLhs, value))
                handle_NOTEqual_const(rhs, value);
            else if (constRhs != nullptr && u.str.is_string(constRhs, value))
                handle_NOTEqual_const(lhs, value);
            else
                handle_NOTEqual_var(lhs, rhs);
        }
    }

    void theory_str::handle_NOTEqual_var(expr* lhs, expr* rhs){
        return;

        ast_manager & m = get_manager();
        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " not (" << mk_pp(lhs, m) << " = " << mk_pp(rhs, m) << ")\n";);

        expr_ref_vector cases(m);
        expr_ref lenLhs(mk_strlen(lhs), m);
        expr_ref lenRhs(mk_strlen(rhs), m);
        expr_ref eqref(createEqualOperator(lenLhs.get(),lenRhs.get()), m);
        cases.push_back(mk_not(m, eqref));

        int len1, len2;
        if (is_important(lhs, len1) && is_important(rhs, len2)) {
            expr* arrLhs = getExprVarFlatArray(lhs);
            expr* arrRhs = getExprVarFlatArray(rhs);
            STRACE("str", tout << __LINE__ <<  " min len: " << std::min(len1, len2) << "\n";);
            for (int i = 0; i < std::min(len1, len2); ++i) {
                expr_ref_vector subcases(m);
                subcases.push_back(createGreaterEqOperator(lenLhs.get(), m_autil.mk_int(i + 1)));
                STRACE("str", tout << __LINE__ <<  "  " << mk_pp(subcases[0].get(), m)  << ")\n";);
                subcases.push_back(createGreaterEqOperator(lenRhs.get(), m_autil.mk_int(i + 1)));
                STRACE("str", tout << __LINE__ <<  "  " << mk_pp(arrLhs, m) <<  "  " << mk_pp(arrRhs, m) << ")\n";);
                expr_ref tmp(createEqualOperator(createSelectOperator(arrLhs, m_autil.mk_int(i)), createSelectOperator(arrRhs, m_autil.mk_int(i))), m);
                STRACE("str", tout << __LINE__ <<  "  " << mk_pp(tmp.get(), m)  << ")\n";);
                subcases.push_back(mk_not(m, tmp.get()));
                cases.push_back(createAndOperator(subcases));
            }

            expr_ref notcause(createEqualOperator(lhs, rhs), m);
            expr_ref cause(mk_not(notcause), m);
            ensure_enode(cause.get());
            expr* assertExpr = createOrOperator(cases);

            assert_axiom(assertExpr, cause.get());
            expr_ref tmpAxiom(createEqualOperator(cause.get(), assertExpr), m);
//            uState.addAssertingConstraints(tmpAxiom);

//            ctx.assign(assertLiteral, b_justification(causeLiteral), false);

//            expr_ref axiom(m.mk_or(notcause, createOrOperator(cases)), m);
//            assert_axiom(axiom);

//
        }


    }

    void theory_str::handle_NOTEqual_const(expr* lhs, zstring rhs){
        ast_manager & m = get_manager();
        expr_ref_vector cases(m);
        expr_ref lenLhs(mk_strlen(lhs), m);
        expr_ref lenRhs(mk_int(rhs.length()), m);
        expr_ref eqref(createEqualOperator(lenLhs.get(),lenRhs.get()), m);
        expr_ref notLenEq(mk_not(m, eqref.get()), m);

        cases.push_back(notLenEq);
        int val = -1;
        if (is_important(lhs, val) && !is_trivial_inequality(lhs, rhs)) {
            STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " not (" << mk_pp(lhs, m) << " = " << rhs << ")\n";);
            expr* arrLhs = getExprVarFlatArray(lhs);
            if (arrLhs == nullptr)
                return;

            for (int i = 0; i < rhs.length(); ++i) {
                expr_ref_vector subcases(m);
                subcases.push_back(createGreaterEqOperator(lenLhs.get(), m_autil.mk_int(i + 1)));
                expr_ref tmp(createEqualOperator(createSelectOperator(arrLhs, m_autil.mk_int(i)), m_autil.mk_int(rhs[i])), m);
                subcases.push_back(mk_not(m, tmp));
                cases.push_back(createAndOperator(subcases));
            }
            expr_ref premise(mk_not(m, createEqualOperator(lhs, u.str.mk_string(rhs))), m);
            ensure_enode(premise.get());
            expr_ref conclusion(createOrOperator(cases), m);


            expr_ref tmpAxiom(createEqualOperator(premise.get(), conclusion.get()), m);
            assert_axiom(tmpAxiom.get());
        }

    }

    void theory_str::handle_NOTContain(){
        for (const auto &wi : m_wi_expr_memo) {
            if (!u.str.is_empty(wi.second.get()) && !u.str.is_empty(wi.first.get())) {
                expr* lhs = wi.first.get();
                expr* rhs = wi.second.get();

                handle_NOTContain(lhs, rhs);
            }
        }
    }

    void theory_str::handle_NOTContain_cached(){
        for (const auto &wi : uState.disequalities) {
            SASSERT(to_app(wi)->get_num_args() == 1);
            expr* equality = to_app(wi)->get_arg(0);

            SASSERT(to_app(equality)->get_num_args() == 2);
            expr* lhs = to_app(equality)->get_arg(0);
            expr* rhs = to_app(equality)->get_arg(1);

            handle_NOTContain(lhs, rhs, true);
        }
    }

    void theory_str::handle_NOTContain(expr* lhs, expr* rhs, bool cached){
        ast_manager & m = get_manager();
        expr* contain = nullptr;
        expr* premise = mk_not(m, createEqualOperator(lhs, rhs));
        if (is_contain_equality(lhs, contain)) {
            zstring value;
            if (u.str.is_string(contain, value))
                handle_NOTContain_const(rhs, value, premise, cached);
            else
                handle_NOTContain_var(rhs, contain, premise, cached);
        }
        else if (is_contain_equality(rhs, contain)) {
            zstring value;
            if (u.str.is_string(contain, value))
                handle_NOTContain_const(lhs, value, premise, cached);
            else
                handle_NOTContain_var(lhs, contain, premise, cached);
        }
    }

    void theory_str::handle_NOTContain_var(expr* lhs, expr* rhs, expr* premise, bool cached){

    }

    void theory_str::handle_NOTContain_const(expr* lhs, zstring rhs, expr* premise, bool cached){
        zstring tmp("U");
        if (rhs == tmp)
            return;
        ast_manager & m = get_manager();
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " not contains (" << mk_pp(lhs, m) << ", " << rhs << ")\n";);
        int bound = -1;

        bool has_eqc_value = false;
        expr *constValue = get_eqc_value(lhs, has_eqc_value);
        if (has_eqc_value) {
            zstring value;

            if (u.str.is_string(constValue, value)) {
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " not contains (" << value << ", " << rhs << "; cached" << cached << ")\n";);
                if (value.indexof(rhs, 0) >= 0 && !cached) {
                    negate_context();
                }
            }
            return;
        }



        if (is_important(lhs, bound) && !is_trivial_contain(rhs)){
            expr_ref_vector cases(m);
            expr* lenExpr = mk_strlen(lhs);
            expr* arr = getExprVarFlatArray(lhs);

            if (arr == nullptr)
                return;

            for (unsigned i = rhs.length(); i <= bound; ++i){
                expr_ref_vector subcases(m);
//                subcases.push_back(createLessEqOperator(lenExpr, mk_int(i - 1)));
                for (unsigned k = 0; k < rhs.length(); ++k) {
                    unsigned pos = k + i - rhs.length();
                    subcases.push_back(mk_not(m, createEqualOperator(
                            createSelectOperator(arr, mk_int(pos)),
                            mk_int(rhs[k]))));
                }
                cases.push_back(createOrOperator(subcases));
            }
            cases.push_back(createLessEqOperator(lenExpr, mk_int(bound)));

            expr_ref axiom(createAndOperator(cases), m);
            assert_axiom(createEqualOperator(premise, axiom.get()));
//            assert_axiom(axiom.get(), mk_not(m, mk_contains(lhs, u.str.mk_string(rhs))));

//            expr_ref tmpAxiom(createEqualOperator(mk_not(m, mk_contains(lhs, u.str.mk_string(rhs))), axiom.get()), m);
//            uState.addAssertingConstraints(axiom);
        }
    }

    bool theory_str::is_trivial_contain(zstring s){
        for (int i = 0; i < s.length(); ++i)
            if (sigmaDomain.find(s[i]) == sigmaDomain.end())
                return true;

        return false;
    }

    bool theory_str::is_contain_equality(expr* n){

        ast_manager & m = get_manager();
        expr_ref_vector eqs(m);
        collect_eq_nodes(n, eqs);
        for  (const auto& nn : eqs) {
            if (u.str.is_concat(nn)) {
                ptr_vector<expr> exprVector;
                get_nodes_in_concat(nn, exprVector);
                if (exprVector.size() == 3) {
                    // check var name
                    std::string n1 = expr2str(exprVector[0]);
                    std::string n3 = expr2str(exprVector[2]);
                    if ((n1.find("pre_contain!tmp") != std::string::npos &&
                         n3.find("post_contain!tmp") != std::string::npos) ||
                        (n1.find("indexOf1!tmp") != std::string::npos &&
                         n3.find("indexOf2!tmp") != std::string::npos) ||
                        (n1.find("replace1!tmp") != std::string::npos &&
                         n3.find("replace2!tmp") != std::string::npos)) {
                        return true;
                    }
                }
            }
        }

        for (const auto& nn : eqs){
            if (collect_not_contains(nn))
                return true;
        }

        return false;
    }

    bool theory_str::is_contain_equality(expr* n, expr* &contain){
        if (u.str.is_concat(n)){
            ptr_vector<expr> exprVector;
            get_nodes_in_concat(n, exprVector);
            if (exprVector.size() == 3) {
                // check var name
                std::string n1 = expr2str(exprVector[0]);
                std::string n3 = expr2str(exprVector[2]);
                if ((n1.find("pre_contain!tmp") != std::string::npos &&
                     n3.find("post_contain!tmp") != std::string::npos) ||
                    (n1.find("indexOf1!tmp") != std::string::npos &&
                     n3.find("indexOf2!tmp") != std::string::npos) ||
                        (n1.find("replace1!tmp") != std::string::npos &&
                         n3.find("replace2!tmp") != std::string::npos)) {
                    contain = exprVector[1];
                    return true;
                }
            }
        }
        contain = nullptr;
        return false;
    }

    void theory_str::static_analysis(std::map<expr*, std::set<expr*>> eq_combination){
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << connectingSize << std::endl;);
        ast_manager & m = get_manager();
        std::set<expr*> allStrExprs;
        std::set<expr*> allConstExprs;
        for (const auto& v : eq_combination){
            expr_ref_vector eqNodeSet(m);
            collect_eq_nodes(v.first, eqNodeSet);
            for (int i = 0; i < eqNodeSet.size(); ++i)
                allStrExprs.insert(eqNodeSet[i].get());

            if (u.str.is_string(v.first))
                allConstExprs.insert(v.first);

            for (const auto& eq : v.second){
                if (is_app(eq)){
                    ptr_vector<expr> exprVector;
                    get_nodes_in_concat(eq, exprVector);
                    for (unsigned i = 0; i < exprVector.size(); ++i) {
                        allStrExprs.insert(exprVector[i]);
                        if (u.str.is_string(exprVector[i]))
                            allConstExprs.insert(exprVector[i]);
                    }
                }
            }
        }

        // calculate sum consts
        int sumConst = 0;
        for (const auto& s: allConstExprs){
            zstring tmp;
            u.str.is_string(s, tmp);
            sumConst += tmp.length();
        }

        sumConst = std::min(sumConst, 100);

        int maxInt = -1;

        for (const auto& v: allStrExprs){
            rational vLen;
            bool vLen_exists = get_len_value(v, vLen);
            if (vLen_exists){
                maxInt = std::max(maxInt, vLen.get_int32());
            }
            else {
                rational lo(-1), hi(-1);

                if (lower_bound(v, lo))
                    maxInt = std::max(maxInt, lo.get_int32());
                if (upper_bound(v, hi))
                    maxInt = std::max(maxInt, hi.get_int32());
            }
        }

        // count non internal var
        int cnt = 5;
        for (const auto& v: allStrExprs){
            if (!isInternalVar(v))
                cnt++;
        }

        connectingSize = std::min(maxInt + cnt + sumConst, std::max(300, maxInt));
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << connectingSize << std::endl;);
    }

    void theory_str::init_underapprox(
            std::map<expr*, std::set<expr*>> eq_combination,
            std::map<expr*, int> &non_fresh_vars){
        static_analysis(eq_combination);
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << connectingSize << std::endl;);
        ast_manager & m = get_manager();
        context & ctx = get_context();
        std::set<expr*> allStrExprs;
        noFlatVariables = 0;
        for (const auto& v : eq_combination){
            if (is_app(v.first)) {
                app *ap = to_app(v.first);
                if (!u.str.is_concat(ap))
                    allStrExprs.insert(v.first);
                else {
                    ptr_vector<expr> exprVector;
                    get_nodes_in_concat(v.first, exprVector);
                    for (unsigned i = 0; i < exprVector.size(); ++i)
                        allStrExprs.insert(exprVector[i]);
                    expr* tmp = ctx.get_enode(v.first)->get_root()->get_owner();
                    if (!u.str.is_concat(tmp))
                        allStrExprs.insert(tmp);
                    else {
                        expr_ref_vector eqNodes(m);
                        collect_eq_nodes(tmp, eqNodes);
                        for (int i = 0; i < eqNodes.size(); ++i)
                            if (!u.str.is_concat(eqNodes[i].get())) {
                                allStrExprs.insert(eqNodes[i].get());
                                break;
                            }
                    }

                }
            }

            for (const auto& eq : v.second){
                if (is_app(eq)){
                    ptr_vector<expr> exprVector;
                    get_nodes_in_concat(eq, exprVector);
                    for (unsigned i = 0; i < exprVector.size(); ++i)
                        allStrExprs.insert(exprVector[i]);
                }
            }
        }

        for (const auto& we: non_membership_memo) {
            allStrExprs.insert(we.first);
        }

        for (const auto& we: membership_memo) {
            allStrExprs.insert(we.first);
        }

        std::map<expr*, int> str_int_vars;
        collect_important_vars_str_int(str_int_vars);
        setup_flats();
        for (const auto& we: str_int_vars) {
            allStrExprs.insert(we.first);
        }

        // create all tmp vars
        for(const auto& v : allStrExprs){
            mk_and_setup_arr(v, non_fresh_vars);
        }

        create_notcontain_map();
        create_const_set();

        init_connecting_size(eq_combination, non_fresh_vars, false);
        init_connecting_size(eq_combination, non_fresh_vars);
        createAppearanceMap(eq_combination);
    }

    void theory_str::mk_and_setup_arr(
            expr* v,
            std::map<expr*, int> &non_fresh_vars){
        ast_manager & m = get_manager();
        context & ctx = get_context();

        expr* arrVar = getExprVarFlatArray(v);
        if (arrVar != nullptr) {
            // check if we can use that: cannot use if two nodes are not equal

            ensure_enode(arrVar);
            std::string arr_str = expr2str(arrVar);
            STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** checking existing array " << arr_str << " " << mk_pp(arrVar, m) << " " << std::endl;);
            SASSERT(arr_str.find_last_of("!", arr_str.length() - 3) != std::string::npos);

            arr_str = arr_str.substr(0, arr_str.find_last_of("!", arr_str.length() - 3));

            if (arr_str[0] == '|')
                arr_str = arr_str.substr(1, arr_str.length() - 1);
            STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** checking existing array " << arr_str  << " of " << mk_pp(v, m) << " " << mk_pp(arrVar, m) << " " << std::endl;);

            SASSERT(arr_linker.find(arrVar) != arr_linker.end());
            if (!are_equal_exprs(v, arr_linker[arrVar])) {
                STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** changing array " << mk_pp(v, m)  << " " << mk_pp(arrVar, m) << std::endl;);
                arrVar = nullptr;
            }
            else {
                zstring val;
                if (u.str.is_string(v, val)) {
                    if (v != arr_linker[arrVar])
                        setup_str_const(val, arrVar, createEqualOperator(v, arr_linker[arrVar]));
                    else
                        setup_str_const(val, arrVar);
                }
                return;
            }
        }

        if ((!u.str.is_concat(v) || non_fresh_vars.find(v) != non_fresh_vars.end()) && arrVar == nullptr) {
            STRACE("str", tout << __LINE__ << " making arr: " << mk_pp(v, m) << std::endl;);
            std::string flatArr = generateFlatArray(std::make_pair(ctx.get_enode(v)->get_root()->get_owner(), 0));
            expr_ref v1(m);
            if (arrMap_reverse.find(flatArr) != arrMap_reverse.end()) {
                v1 = arrMap_reverse[flatArr];
            }
            else {
                v1 = mk_arr_var(flatArr);
                arrMap_reverse[flatArr] = v1;
                STRACE("str", tout << __LINE__ << " making arr: " << flatArr << " --> " << mk_pp(v1, m) << std::endl;);
                arr_linker[v1] = v;
            }

            {
                expr_ref_vector eqs(m);
                collect_eq_nodes(v, eqs);

                for (const auto& vv : eqs)
                    arrMap[vv] = v1;
            }


            STRACE("str", tout << __LINE__ << " arr: " << flatArr << " : " << mk_pp(v1, m) << std::endl;);

            zstring val;
            expr* rexpr;
            if (u.str.is_string(v, val)){
                setup_str_const(val, v1);
            }
            else if (isInternalRegexVar(v, rexpr)) {
            }
            else if (is_str_int_var(v)){
                // setup_str_int_arr
            }
        }
    }

    void theory_str::setup_str_int_arr(expr* v, int start){
        ast_manager & m = get_manager();
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << mk_pp(v, m) << std::endl;);
        expr_ref_vector ands(m);
        rational one(1);
        rational zero((int)('0'));
        rational nine((int)('9'));
        expr* arr = getExprVarFlatArray(v);
        expr* zero_e(mk_int(zero));
        expr* nine_e(mk_int(nine));
        for (rational i = one - one; i < str_int_bound; i = i + one){
            expr* rhs = leng_prefix_rhs(std::make_pair(v, start + 1), true);
            ands.push_back(createGreaterEqOperator(createSelectOperator(arr, createAddOperator(rhs, mk_int(i))), zero_e));
            ands.push_back(createLessEqOperator(createSelectOperator(arr, createAddOperator(rhs, mk_int(i))), nine_e));
        }

        expr *len = mk_strlen(v);

        // flat 1 = zero
        for (rational i = one; i <= q_bound; i = i + one) {
            rational total_len = str_int_bound + i;
            expr* premise = createGreaterEqOperator(len, mk_int(total_len));
            rational j = i - one;
            expr* conclusion = createEqualOperator(createSelectOperator(arr, mk_int(j)), zero_e);
            ands.push_back(rewrite_implication(premise, conclusion));
        }

        expr_ref tmp(createAndOperator(ands), m);
        assert_axiom(tmp.get());
        impliedFacts.push_back(tmp);
    }

    void theory_str::setup_str_const(zstring val, expr* arr, expr* premise){
        ast_manager & m = get_manager();
        STRACE("str", tout << __LINE__ << " " << mk_pp(arr, m) << " = " << val << std::endl;);
        expr_ref_vector ands(m);
        for (int i = 0; i < val.length(); ++i){
            ands.push_back(createEqualOperator(createSelectOperator(arr, mk_int(i)), mk_int(val[i])));
        }

        expr* to_assert = createAndOperator(ands);
        if (premise != nullptr) {
            expr* tmp = rewrite_implication(premise, to_assert);
            assert_axiom(tmp);
            impliedFacts.push_back(tmp);
        }
        else {
            assert_axiom(to_assert);
            impliedFacts.push_back(to_assert);
        }
    }

    expr* theory_str::setup_regex_var(expr* rexpr, expr* arr, rational bound, expr* prefix){
        ast_manager & m = get_manager();
        expr* ret = setup_char_range_arr(rexpr, arr, bound, prefix);
        if (ret != nullptr) {
        }
        else {
            std::vector<zstring> elements;
            expr_ref_vector ors(m);
            collect_alternative_components(rexpr, elements);
            for (int i = 0; i < elements.size(); ++i) {
                expr_ref_vector ands(m);
                for (int j = 0; j < bound.get_int64(); ++j) {
                    int pos = j % elements[i].length();
                    ands.push_back(createEqualOperator(createSelectOperator(arr, createAddOperator(prefix, mk_int(j))), mk_int(elements[i][pos])));
                }
                ors.push_back(createAndOperator(ands));
            }
            ret = createOrOperator(ors);
        }

        return ret;
    }

    expr* theory_str::setup_char_range_arr(expr* e, expr* arr, rational bound, expr* prefix){
        ast_manager & m = get_manager();
        std::vector<std::pair<int, int>> charRange = collectCharRange(e);
        expr* pre_lhs = mk_int(0);
        if (charRange[0].first != -1) {
            expr_ref_vector ret(m);

            for (int i = 0; i < bound.get_int64(); ++i) {
                expr_ref_vector ors(m);
                expr_ref_vector ors_range(m);
                for (int j = 0; j < charRange.size(); ++j) {
                    expr_ref_vector ands(m);
                    ands.push_back(createGreaterEqOperator(
                            createSelectOperator(arr, createAddOperator(prefix, m_autil.mk_int(i))),
                            m_autil.mk_int(charRange[j].first)));
                    ands.push_back(createLessEqOperator(
                            createSelectOperator(arr, createAddOperator(prefix, m_autil.mk_int(i))),
                            m_autil.mk_int(charRange[j].second)));
                    ors_range.push_back(createAndOperator(ands));
                }
                ret.push_back(createOrOperator(ors_range));
            }
            STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " ***" << mk_pp(createAndOperator(ret), m) << std::endl;);
            return createAndOperator(ret);
        }
        return nullptr;
    }

    void theory_str::setup_flats(){
        if (should_use_flat() && p_bound == rational(0)) {
            p_bound = rational(2);
            q_bound = rational(5);
            assert_axiom(createEqualOperator(get_bound_p_control_var(), mk_int(p_bound)));
            assert_axiom(createEqualOperator(get_bound_q_control_var(), mk_int(q_bound)));
            if (p_bound >= max_p_bound)
                impliedFacts.push_back(createEqualOperator(get_bound_p_control_var(), mk_int(p_bound)));
            if (q_bound >= max_q_bound)
                impliedFacts.push_back(createEqualOperator(get_bound_q_control_var(), mk_int(q_bound)));
        }
        else if (should_use_flat() && (p_bound < max_p_bound || q_bound < max_q_bound)){
            if (p_bound < max_p_bound) {
//                p_bound = p_bound + rational(1);
                assert_axiom(createEqualOperator(get_bound_p_control_var(), mk_int(p_bound)));
                if (p_bound >= max_p_bound)
                    impliedFacts.push_back(createEqualOperator(get_bound_p_control_var(), mk_int(p_bound)));
            }
            if (q_bound < max_q_bound) {
//                q_bound = q_bound + rational(5);
                assert_axiom(createEqualOperator(get_bound_q_control_var(), mk_int(q_bound)));
                if (q_bound >= max_q_bound)
                    impliedFacts.push_back(createEqualOperator(get_bound_q_control_var(), mk_int(q_bound)));
            }
        }
    }

    bool theory_str::should_use_flat(){
        if (string_int_vars.size() > 0)
            return true;
        return false;
    }

    void theory_str::init_underapprox_cached(){
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << connectingSize << std::endl;);
        ast_manager & m = get_manager();
        context & ctx = get_context();
        std::set<expr*> allStrExprs;
        noFlatVariables = 0;
        for (const auto& v : uState.eq_combination){
            ensure_enode(v.first);
            if (is_app(v.first)) {
                app *ap = to_app(v.first);
                if (!u.str.is_concat(ap))
                    allStrExprs.insert(v.first);
                else {
                    expr* tmp = ctx.get_enode(v.first)->get_root()->get_owner();
                    if (!u.str.is_concat(tmp))
                        allStrExprs.insert(tmp);
                    else {
                        expr_ref_vector eqNodes(m);
                        collect_eq_nodes(tmp, eqNodes);
                        for (int i = 0; i < eqNodes.size(); ++i)
                            if (!u.str.is_concat(eqNodes[i].get())) {
                                allStrExprs.insert(eqNodes[i].get());
                                break;
                            }
                    }

                }
            }
            for (const auto& eq : v.second){
                ensure_enode(eq);
                if (is_app(eq)){
                    ptr_vector<expr> exprVector;
                    get_nodes_in_concat(eq, exprVector);
                    for (unsigned i = 0; i < exprVector.size(); ++i)
                        allStrExprs.insert(exprVector[i]);
                }
            }
        }

        for (const auto& we: non_membership_memo) {
            allStrExprs.insert(we.first);
        }

        for (const auto& we: membership_memo) {
            allStrExprs.insert(we.first);
        }

        std::map<expr*, int> str_int_vars;
        collect_important_vars_str_int(str_int_vars);
        for (const auto& we: str_int_vars) {
            allStrExprs.insert(we.first);
        }

        // create all tmp vars
        for(const auto& v : allStrExprs){
            app *ap = to_app(v);
            expr* arrVar = getExprVarFlatArray(v);
            if (arrVar == nullptr)
                continue;
            if (!u.str.is_concat(ap) && arrVar == nullptr) {
                std::string flatArr = generateFlatArray(std::make_pair(ctx.get_enode(v)->get_root()->get_owner(), 0));
                if (u.str.is_string(v))
                    flatArr = generateFlatArray(std::make_pair(v, 0));

                expr_ref v1(m);
                if (arrMap_reverse.find(flatArr) != arrMap_reverse.end()) {
                    v1 = arrMap_reverse[flatArr];

                    if (!ctx.e_internalized(v1.get())){
                        ctx.internalize(v1, false);
                    }
                }
                else {
                    v1 = mk_arr_var(flatArr);
                    arrMap_reverse[flatArr] = v1;
                }
                {
                    expr_ref_vector eqs(m);
                    collect_eq_nodes(v, eqs);

                    for (const auto& vv : eqs)
                        arrMap[vv] = v1;
                }
                STRACE("str", tout << __LINE__ << " arr: " << flatArr << " : " << mk_pp(v1, m) << std::endl;);
            }
            else if (arrVar != nullptr) {
                ensure_enode(arrVar);
                // I'm assuming that this combination will do the correct thing in the integer theory.
                STRACE("str", tout << __LINE__ << " arr: " << mk_pp(arrVar, m) << std::endl;);
                m_trail.push_back(arrVar);
            }
        }

        for  (const auto& arr : arrMap_reverse) {
            ensure_enode(arr.second);
        }
    }

    void theory_str::create_notcontain_map(){
        ast_manager & m = get_manager();
        for (const auto& ieq : m_wi_expr_memo){
            expr* lhs = ieq.first.get();
            expr* rhs = ieq.second.get();

            if (u.str.is_concat(lhs)){
                ptr_vector<expr> exprVector;
                get_nodes_in_concat(lhs, exprVector);
                if (exprVector.size() == 3) {
                    std::stringstream ss01;
                    ss01 << mk_ismt2_pp(exprVector[0], m);
                    std::string varName = ss01.str();

                    bool found01 = varName.find("pre_contain") != std::string::npos;

                    std::stringstream ss02;
                    ss02 << mk_ismt2_pp(exprVector[2], m);
                    varName = ss02.str();
                    bool found02 = varName.find("post_contain") != std::string::npos;

                    if (found01 && found02){
                        notContainMap[rhs].insert(exprVector[1]);
                    }
                }
            }

            if (u.str.is_concat(rhs)){
                ptr_vector<expr> exprVector;
                get_nodes_in_concat(rhs, exprVector);
                if (exprVector.size() == 3) {
                    std::stringstream ss01;
                    ss01 << mk_ismt2_pp(exprVector[0], m);
                    std::string varName = ss01.str();

                    bool found01 = varName.find("pre_contain") != std::string::npos;

                    std::stringstream ss02;
                    ss02 << mk_ismt2_pp(exprVector[2], m);
                    varName = ss02.str();
                    bool found02 = varName.find("post_contain") != std::string::npos;

                    if (found01 && found02){
                        notContainMap[lhs].insert(exprVector[1]);
                    }
                }
            }
        }


    }

    void theory_str::create_const_set(){
        constSet.clear();
        for (const auto _eq : uState.eq_combination) {
            zstring value;
            if (u.str.is_string(_eq.first, value)) {
                constSet.insert(value);
            }
            for (const auto v: _eq.second){
                ptr_vector<expr> exprVector;
                get_nodes_in_concat(v, exprVector);
                /* push to map */
                for (int i = 0; i < exprVector.size(); ++i)
                    if (u.str.is_string(exprVector[i], value)){
                        constSet.insert(value);
                    }
            }
        }
    }

    char theory_str::setupDefaultChar(std::set<char> includeChars, std::set<char> excludeChars){
        char defaultChar = 'a';

        for (const auto& ch : includeChars)
            if (excludeChars.find(ch) == excludeChars.end()) {
                defaultChar = ch;
                break;
            }
        return defaultChar;
    }

    std::set<char> theory_str::initExcludeCharSet(){
        std::set<char> excludeCharSet;
        for (const auto& s : constSet){
            for (unsigned i = 0; i < s.length(); ++i) {
                excludeCharSet.emplace(s[i]);
            }
        }
        return excludeCharSet;
    }

    /*
     *
     */
    std::set<char> theory_str::initIncludeCharSet(){
        std::set<char> includeCharSet;
        if (includeCharSet.size() == 0)
            for (unsigned i = 32; i <= 126; ++i)
                includeCharSet.emplace(i);

        return includeCharSet;
    }

    void theory_str::createAppearanceMap(
            std::map<expr*, std::set<expr*>> eq_combination){
        appearanceMap.clear();
        for (const auto& var : eq_combination){
            for (const auto& eq : var.second) {
                ptr_vector<expr> nodes;
                get_nodes_in_concat(eq, nodes);
                for (int i = 0; i < nodes.size(); ++i)
                    appearanceMap[nodes[i]].emplace(var.first);
            }
        }
    }

    /*
     *
     */
    void theory_str::init_connecting_size(
            std::map<expr*, std::set<expr*>> eq_combination,
            std::map<expr*, int> &non_fresh_vars, bool prep){
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << connectingSize << std::endl;);
        int oldConnectingSize = connectingSize;
        static_analysis(eq_combination);
        if (!prep){
            connectingSize = std::max(CONNECTINGSIZE, connectingSize);
        }
        for (auto &v : non_fresh_vars)
            if (v.second == -1 || v.second == oldConnectingSize)
                v.second = connectingSize;
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << connectingSize << std::endl;);
    }

    bool theory_str::convert_equalities(std::map<expr*, std::vector<expr*>> eq_combination,
                                       std::map<expr*, int> non_fresh_vars,
                                       expr* premise){
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << std::endl;);
        ast_manager &m = get_manager();
        context & ctx = get_context();
        clock_t t = clock();
        currVarPieces.clear();
        generatedEqualities.clear();

        expr_ref_vector assertedConstraints(m);
        bool axiomAdded = false;
        for (std::map<expr*, std::vector<expr*>>::iterator it = eq_combination.begin(); it != eq_combination.end(); ++it) {

            std::string tmp = " ";
            clock_t t;

            /* different tactic for size of it->second */
            const int flatP = 1;
            const int maxPConsidered = 6;
            unsigned maxLocal = findMaxP(it->second);
            STRACE("str", tout << __LINE__ << " " << mk_pp(it->first, m) <<  " maxLocal:  " << maxLocal << std::endl;);

            if (it->second.size() == 0)
                continue;
            expr* reg = nullptr;
            if ((isInternalRegexVar(it->first, reg)) || is_important(it->first) || u.str.is_string(it->first)){
                STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << mk_pp(it->first, m) << std::endl;);
                /* compare with others */
                expr* root_tmp = find_equivalent_variable(it->first);
                for (const auto& element: it->second) {
                    if (element == it->first && !u.str.is_concat(element)){
                        continue;
                    }
                    STRACE("str",
                            tout << __LINE__ <<  " *** " << __FUNCTION__ << " " << mk_pp(root_tmp, m) << " vs ";
                            tout << mk_pp(element, m) << std::endl;
                            );
                    ptr_vector<expr> lhs;
                    ptr_vector<expr> rhs;
                    optimize_equality(root_tmp, element, lhs, rhs);
                    STRACE("str",
                           tout << __LINE__ <<  " *** " << __FUNCTION__ << " " << lhs.size() << " vs ";
                                   tout << rhs.size() << std::endl;
                    );
                    std::vector<std::pair<expr*, int>> lhs_elements = create_equality(lhs);
                    STRACE("str",
                           tout << __LINE__ <<  " *** " << __FUNCTION__ << " " << lhs.size() << " vs ";
                                   tout << rhs.size() << std::endl;
                    );
                    std::vector<std::pair<expr*, int>> rhs_elements = create_equality(rhs);
                    STRACE("str",
                           tout << __LINE__ <<  " *** " << __FUNCTION__ << " " << lhs_elements.size() << " vs ";
                                   tout << rhs_elements.size() << std::endl;
                    );
                    t = clock();
                    expr* result = equality_to_arith(lhs_elements, rhs_elements, non_fresh_vars);
                    t = clock() - t;
                    assert_breakdown_combination(result, premise, assertedConstraints, axiomAdded);
                    if (result == nullptr)
                        return true;
                }

                expr* regexExpr;
                if (is_regex_var(it->first, regexExpr) && !isInternalVar(it->first)){
                    STRACE("str", tout << __LINE__ <<  "  " << mk_pp(it->first, m) << " = " << mk_pp(regexExpr, m) << " " << getStdRegexStr(regexExpr) << std::endl;);
                    //std::vector<std::vector<zstring>> regexElements = combine_const_str(refineVectors(parse_regex_components(remove_star_in_star(getStdRegexStr(regexExpr)))));
                    std::vector<expr*> regexElements = combine_const_str(parse_regex_components(remove_star_in_star(regexExpr)));
                    expr_ref_vector ors(m);
                    for (const auto& v : regexElements){
                        ptr_vector <expr> elements;
                        get_nodes_in_reg_concat(v, elements);
                        ptr_vector<expr> lhs;
                        ptr_vector<expr> rhs;
                        optimize_equality(it->first, elements, lhs, rhs);
                        std::vector<std::pair<expr*, int>> lhs_elements = create_equality(lhs);
                        std::vector<std::pair<expr*, int>> rhs_elements = create_equality(rhs);

                        expr* result = equality_to_arith(lhs_elements,
                                                         rhs_elements,
                                                         non_fresh_vars);

                        if (result != nullptr) {
                            expr_ref tmp(result, m);
                            ors.push_back(tmp);
                        }
                    }

                    if (ors.size() > 0) {
                        expr_ref tmp(createOrOperator(ors), m);
                        assertedConstraints.push_back(tmp);
                        assert_axiom(tmp.get(), m.mk_true());
                    }
                }
            }
            else if (maxLocal > maxPConsidered) {
                /* add an eq = flat . flat . flat, then other equalities will compare with it */

                std::vector<std::pair<expr*, int>> lhs_elements = create_equality(it->first, false);
                uState.non_fresh_vars.insert(std::make_pair(it->first, connectingSize));
                non_fresh_vars.insert(std::make_pair(it->first, connectingSize));
                mk_and_setup_arr(it->first, non_fresh_vars);

                /* compare with others */
                for (const auto& element: it->second) {
                    std::vector<std::pair<expr*, int>> rhs_elements = create_equality(element);
                    t = clock();
                    expr* result = equality_to_arith(
                            lhs_elements,
                            rhs_elements,
                            non_fresh_vars
                    );
                    t = clock() - t;
                    assert_breakdown_combination(result, premise, assertedConstraints, axiomAdded);
                    if (result == nullptr)
                        return true;
                }
            }
            else {
                STRACE("str", tout << __LINE__ <<  " work as usual " << std::endl;);
                /* work as usual */
                for (unsigned i = 0; i < it->second.size(); ++i)
                    for (unsigned j = i + 1; j < it->second.size(); ++j) {
                        /* optimize: find longest common prefix and posfix */
                        ptr_vector<expr> lhs;
                        ptr_vector<expr> rhs;
                        optimize_equality(it->second[i], it->second[j], lhs, rhs);

                        if (lhs.size() == 0 || rhs.size() == 0){
                            continue;
                        }

                        /* [i] = [j] */
                        std::vector<std::pair<expr*, int>> lhs_elements = create_equality(lhs);
                        std::vector<std::pair<expr*, int>> rhs_elements = create_equality(rhs);
                        t = clock();
                        expr* result = equality_to_arith(
                                lhs_elements,
                                rhs_elements,
                                non_fresh_vars
                        );
                        t = clock() - t;
                        assert_breakdown_combination(result, premise, assertedConstraints, axiomAdded);
                        if (result == nullptr)
                            return true;
                    }
            }

        }

        if (assertedConstraints.size() > 0) {
            expr_ref tmp(createAndOperator(assertedConstraints), m);
            uState.addAssertingConstraints(tmp);
        }
        STRACE("str", tout << __LINE__ <<  " time: " << __FUNCTION__ << ":  " << ((float)(clock() - t))/CLOCKS_PER_SEC << std::endl;);
        return axiomAdded;
    }

    void theory_str::assert_breakdown_combination(expr* e, expr* premise, expr_ref_vector &assertedConstraints, bool &axiomAdded){
        ast_manager &m = get_manager();
        if (e != nullptr) {
            if (!m.is_true(e)){
                axiomAdded = true;
                assertedConstraints.push_back(e);
                assert_breakdown_combination(e, premise);
            }
        }
        else {
            /* trivial unsat */
            assertedConstraints.reset();
            negate_context(premise);
        }
    }

    void theory_str::assert_breakdown_combination(expr* e, expr* premise){
        context &ctx = get_context();
        ensure_enode(e);
        assert_axiom(e, premise);
    }

    void theory_str::negate_context(){
        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << std::endl;);
        ast_manager &m = get_manager();
        expr_ref_vector guessedEqs(m), guessedDisEqs(m);
        fetch_guessed_exprs_with_scopes(guessedEqs, guessedDisEqs);
        guessedEqs.append(guessedDisEqs);

        expr_ref tmp(mk_not(m, createAndOperator(guessedEqs)), m);
        assert_axiom(tmp.get());
        impliedFacts.push_back(tmp.get());
    }

    void theory_str::negate_context(expr* premise){
        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << std::endl;);
        ast_manager &m = get_manager();
        expr_ref tmp(mk_not(m,premise), m);
        assert_axiom(tmp.get());
        impliedFacts.push_back(tmp.get());
    }

    void theory_str::negate_context(expr_ref_vector v){
        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << std::endl;);
        ast_manager &m = get_manager();
        expr_ref_vector guessedEqs(m), guessedDisEqs(m);
        fetch_guessed_exprs_with_scopes(guessedEqs, guessedDisEqs);
        guessedEqs.append(v);
        guessedEqs.append(guessedDisEqs);
        expr_ref tmp(mk_not(m, createAndOperator(guessedEqs)), m);
        assert_axiom(tmp.get());
    }

    expr* theory_str::find_equivalent_variable(expr* e){
        if (u.str.is_concat(e)) {
            // change from concat to variable if it is possible
            expr_ref_vector eqNodeSet(get_manager());
            collect_eq_nodes(e, eqNodeSet);
            for (int i = 0; i < eqNodeSet.size(); ++i)
                if (!u.str.is_concat(eqNodeSet[i].get())) {
                    return eqNodeSet[i].get();
                }
        }
        return e;
    }

    bool theory_str::isInternalVar(expr* e){
        std::string tmp = expr2str(e);
        return tmp.find("!tmp") != std::string::npos;
    }

    bool theory_str::isInternalRegexVar(expr* e, expr* &regex){
        expr_ref_vector eqs(get_manager());
        collect_eq_nodes(e, eqs);
        for (const auto& we: membership_memo) {
            if (eqs.contains(we.first)){
                regex = we.second;
                for (const auto& n : eqs)
                    if (!u.str.is_concat(n)){
                        std::string tmp = expr2str(n);
                        if (tmp.find("!tmp") != std::string::npos && !u.re.is_concat(we.second))
                            return true;
                    }
            }
        }
        return false;
    }

    std::vector<expr*> theory_str::createExprFromRegexVector(std::vector<zstring> v) {
        ast_manager &m = get_manager();
        STRACE("str", tout << __LINE__ << __FUNCTION__ << std::endl;);
        for (const auto& s : v)
            STRACE("str", tout << __LINE__ << __FUNCTION__ << " " << s << std::endl;);
        std::vector<expr*> ret;
        for (int i = 0; i < v.size(); ++i){
            if (isRegexStr(v[i])){
                if (v[i][v[i].length() - 1] == '*'){
                    zstring tmp = parse_regex_content(v[i]);

                    if (!isUnionStr(tmp)) {
                        ret.push_back(u.re.mk_star(u.re.mk_to_re(u.str.mk_string(tmp))));
                    }
                    else {
                        std::vector<zstring> tmpVectorStr = collect_alternative_components(tmp);
                        std::vector<expr*> tmpVectorExpr = createExprFromRegexVector(tmpVectorStr);
                        expr * args[tmpVectorExpr.size()];
                        for (int j = 0; j < tmpVectorExpr.size(); ++j) {
                            args[j] =  u.re.mk_to_re(tmpVectorExpr[j]);
                        }
                        expr* tmp = m.mk_app(u.re.get_family_id(), OP_RE_UNION, 0, nullptr, tmpVectorExpr.size(), args);
                        ret.push_back(u.re.mk_star(tmp));
                        STRACE("str", tout << __LINE__ <<  " tmp = " << mk_pp(tmp, m) << std::endl;);
                    }
                }
                else if (v[i][v[i].length() - 1] == '+'){
                    zstring tmp = parse_regex_content(v[i]);
                    if (!isUnionStr(tmp)) {
                        ret.push_back(u.re.mk_plus(u.re.mk_to_re(u.str.mk_string(tmp))));
                    }
                    else {
                        std::vector<zstring> tmpVectorStr = collect_alternative_components(tmp);
                        std::vector<expr*> tmpVectorExpr = createExprFromRegexVector(tmpVectorStr);
                        expr * args[tmpVectorExpr.size()];
                        for (int j = 0; j < tmpVectorExpr.size(); ++j) {
                            args[j] =  u.re.mk_to_re(tmpVectorExpr[j]);
                        }
                        expr* tmp = m.mk_app(u.re.get_family_id(), OP_RE_UNION, 0, nullptr, tmpVectorExpr.size(), args);
                        ret.push_back(u.re.mk_plus(tmp));
                        STRACE("str", tout << __LINE__ <<  " tmp = " << mk_pp(tmp, m) << std::endl;);
                    }
                }
                else {
                    SASSERT(false);
                }
            }
            else if (isUnionStr(v[i]) && v[i].contains("(") && v[i].contains(")")){
                zstring tmp = v[i];
                if (tmp.length() > 0 && tmp[0] == '"')
                    tmp = tmp.extract(1, tmp.length() - 2);
                STRACE("str", tout << __LINE__ <<  " tmp = " << tmp << std::endl;);
                std::vector<zstring> tmpV = collect_alternative_components(tmp);
                std::vector<expr*> tmpVectorExpr = createExprFromRegexVector(tmpV);
                expr * args[tmpVectorExpr.size()];
                for (int j = 0; j < tmpVectorExpr.size(); ++j) {
                    args[j] =  u.re.mk_to_re(tmpVectorExpr[j]);
                }
                expr* tmpE = m.mk_app(u.re.get_family_id(), OP_RE_UNION, 0, nullptr, tmpVectorExpr.size(), args);

                ret.push_back(tmpE);
            }
            else {
                zstring tmp = v[i];
                if (tmp.length() > 0 && tmp[0] == '"' && tmp.length() >= 2)
                    tmp = tmp.extract(1, tmp.length() - 2);
                STRACE("str", tout << __LINE__ <<  " tmp = " << tmp << std::endl;);
                ret.push_back(u.str.mk_string(tmp));
            }
        }
        return ret;
    }

    /*
     * (abc)* -> abc
     */
    zstring theory_str::parse_regex_content(zstring str){
        int pos = str.indexof("*", 0);
        if (pos == -1)
            pos = str.indexof("+", 0);

        return str.extract(1, pos - 2);
    }

    /*
     * (abc)*__XXX -> abc
     */
    zstring theory_str::parse_regex_content(expr* e){
        expr* reg = nullptr;
        if (isInternalRegexVar(e, reg)){
            return parse_regex_content(reg);
        }

        SASSERT (u.re.is_star(e) || u.re.is_plus(e) || u.re.is_union(e));

        if (u.re.is_union(e)) {
            return "";
        }
        else {
            expr *arg0 = to_app(e)->get_arg(0);
            if (u.re.is_to_re(arg0)) {
                expr *arg00 = to_app(arg0)->get_arg(0);
                zstring value;
                SASSERT (u.str.is_string(arg00, value));
                return value;
            }
            return zstring("uNkNoWn");
        }
    }

    /*
     * a b c (abc)* --> abc (abc)*
     */
    std::vector<std::vector<zstring>> theory_str::combine_const_str(std::vector<std::vector<zstring>> regexElements){
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << regexElements.size() << std::endl;);
        std::vector<std::vector<zstring>> results;
        for (unsigned i = 0; i < regexElements.size(); ++i) {
            std::vector<zstring> tmp;
            bool isRegex_prev = true;
            for (unsigned j = 0; j < regexElements[i].size(); ++j) {
                STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***  " << regexElements[i][j] << std::endl;);
                if (isRegex_prev == false) {
                    isRegex_prev = isRegexStr(regexElements[i][j]) || isUnionStr(regexElements[i][j]);
                    if (isRegex_prev == false) {
                        zstring tmpStr = tmp[tmp.size() - 1];
                        zstring newStr = regexElements[i][j];
                        tmp[tmp.size() - 1] = zstring("\"") + tmpStr.extract(1, tmpStr.length() - 2) + newStr.extract(1, newStr.length() - 2) + "\"";
                    }
                    else
                        tmp.emplace_back(regexElements[i][j]);
                }
                else {
                    isRegex_prev = isRegexStr(regexElements[i][j]) || isUnionStr(regexElements[i][j]);
                    tmp.emplace_back(regexElements[i][j]);
                }
            }
            results.emplace_back(tmp);
        }
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** DONE " << std::endl;);
        return results;
    }

    std::vector<expr*> theory_str::combine_const_str(std::vector<expr*> v){
        return v;
        ast_manager &m = get_manager();
        std::vector<expr*> result;
        for (const auto& e : v){
            ptr_vector<expr> nodes;
            get_nodes_in_reg_concat(e, nodes);
            if (nodes.size() > 0) {
                ptr_vector<expr> tmp_nodes;
                tmp_nodes.push_back(nodes[0]);
                for (int i = 1; i < nodes.size(); ++i) {
                    if (u.re.is_to_re(nodes[i]) && u.re.is_to_re(tmp_nodes[tmp_nodes.size() - 1])) {

                        // group them
                        expr* tmp00 = to_app(tmp_nodes[tmp_nodes.size() - 1])->get_arg(0);
                        expr* tmp01 = to_app(nodes[i])->get_arg(0);

                        zstring value00, value01;
                        u.str.is_string(tmp00, value00);
                        u.str.is_string(tmp01, value01);
                        value00 = value00 + value01;
                        tmp_nodes.pop_back();
                        tmp_nodes.push_back(u.re.mk_to_re(mk_string(value00)));
                    }
                    else
                        tmp_nodes.push_back(nodes[i]);
                }
                // create big concat
                expr* concat = tmp_nodes[tmp_nodes.size() - 1];
                for (int j = tmp_nodes.size() - 2; j >= 0; --j) {
                    concat = u.re.mk_concat(tmp_nodes[j], concat);
                }
                ensure_enode(concat);
                result.push_back(concat);
            }
            else
                result.push_back(u.re.mk_to_re(mk_string("")));
        }
        return result;
    }

    bool theory_str::isRegexStr(zstring str){
        return str.contains(")*") || str.contains(")+");
    }

    bool theory_str::isUnionStr(zstring str){
        return str.contains("|");
    }

    /*
     * remove duplication
     */
    std::vector<std::vector<zstring>> theory_str::refineVectors(std::vector<std::vector<zstring>> list){
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << list.size() << std::endl;);
        std::vector<std::vector<zstring>> result;
        if (list.size() < 1000) {
            bool duplicated[1000];
            memset(duplicated, false, sizeof duplicated);
            for (unsigned i = 0; i < list.size(); ++i)
                if (!duplicated[i])
                    for (unsigned j = i + 1; j < list.size(); ++j)
                        if (!duplicated[j]) {
                            if (equalStrVector(list[i], list[j])) {
                                duplicated[j] = true;
                            }
                        }

            for (unsigned int i = 0 ; i < list.size(); ++i)
                if (!duplicated[i])
                    result.emplace_back(list[i]);
        }
        else
            result = list;

        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << result.size() << std::endl;);

        for (unsigned i = 0; i < result.size(); ++i)
            for (unsigned j = 0; j < result[i].size(); ++j) {
                if (result[i][j].length() == 0)
                    result[i][j] = zstring("\"\"");
                else if (result[i][j][0] != '(')
                    result[i][j] = zstring("\"") + result[i][j] + "\"";
            }
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << result.size() << std::endl;);
        return result;
    }

    /*
     *
     */
    bool theory_str::equalStrVector(std::vector<zstring> a, std::vector<zstring> b){
        if (a.size() != b.size()) {
            return false;
        }
        for (unsigned i = 0; i < a.size(); ++i)
            if (a[i] != b[i]) {
                return false;
            }
        return true;
    }

    /*
     *
     */
    std::vector<std::vector<zstring>> theory_str::parse_regex_components(zstring str){
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << str << std::endl;);
        if (str.length() == 0)
            return {};
        else if (!str.contains("(") && !str.contains(")"))
            return {{str}};

        std::vector<std::vector<zstring>> result;

        std::vector<zstring> components = collect_alternative_components(str);
        if (components.size() > 1){
            for (const auto& c : components) {
                std::vector<std::vector<zstring>> tmp = parse_regex_components(c);
                for (const auto& comp : tmp)
                    result.emplace_back(comp);
            }
            bool merge = true;
            zstring tmp;
            for (const auto& s : result)
                if (s.size() > 0 && isRegexStr(s[0])){
                    merge = false;
                    break;
                }
                else if (s.size() > 0)
                    tmp = tmp + "|(" + s[0] + ")";

            if (merge == true) {
                tmp = tmp.extract(1, tmp.length() - 1);
                return {{tmp}};
            }
            else
                return result;
        }

        int leftParentheses = str.indexof('(', 0);
        if (leftParentheses == -1)
            return {{str}};
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << str << std::endl;);
        /* abc(def)* */
        if (leftParentheses != 0) {
            zstring header = str.extract(0, leftParentheses);
            std::vector<std::vector<zstring>> rightComponents = parse_regex_components(str.extract(leftParentheses, str.length() - leftParentheses));
            for (unsigned int i = 0; i < rightComponents.size(); ++i) {
                std::vector<zstring> tmp = {header};
                tmp.insert(tmp.end(), rightComponents[i].begin(), rightComponents[i].end());
                result.emplace_back(tmp);
            }
            return result;
        }

        int rightParentheses = find_correspond_right_parentheses(leftParentheses, str);
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << leftParentheses << " " << rightParentheses << std::endl;);
        if (rightParentheses < 0) {
            SASSERT (false);
        }
        else if (leftParentheses + 1 == rightParentheses && str.length() == 2) {
            STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << str << std::endl;);
            return {{zstring("")}};
        }
        else if (rightParentheses == (int)str.length() - 1){
            /* (a) */
            STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << str << std::endl;);
            removeExtraParentheses(str);
            return parse_regex_components(str);
        }
        else if (rightParentheses == (int)str.length() - 2 && (str[str.length() - 1] == '*' || str[str.length() - 1] == '+')){
            /* (a)* */
            STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << str << std::endl;);
            optimizeFlatAutomaton(str);
            return {{str}};
        }
        else {
            STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << str << std::endl;);
            int pos = rightParentheses;
            zstring left, right;
            if (str[rightParentheses + 1] == '*' || str[rightParentheses + 1] == '+'){
                pos++;
                left = str.extract(leftParentheses, pos - leftParentheses + 1);
                right = str.extract(pos + 1, str.length() - pos - 1);
            }
            else if (str[pos] != '|' || str[pos] != '~') {
                if (leftParentheses + 1 == rightParentheses)
                    left = "";
                else
                    left = str.extract(leftParentheses + 1, pos - leftParentheses - 1);
                right = str.extract(pos + 1, str.length() - pos - 1);
            }
            else {
                SASSERT (false);
                /* several options ab | cd | ef */
            }

            if (str[pos] != '|' || str[pos] != '~') {
                std::vector<std::vector<zstring>> leftComponents = parse_regex_components(left);
                std::vector<std::vector<zstring>> rightComponents = parse_regex_components(right);
                if (leftComponents.size() > 0) {
                    if (rightComponents.size() > 0) {
                        for (int i = 0; i < std::min(10, (int)leftComponents.size()); ++i)
                            for (int j = 0; j < std::min(10, (int)rightComponents.size()); ++j) {
                                std::vector<zstring> tmp;
                                tmp.insert(tmp.end(), leftComponents[i].begin(), leftComponents[i].end());
                                tmp.insert(tmp.end(), rightComponents[j].begin(), rightComponents[j].end());
                                result.emplace_back(tmp);
                            }
                    }
                    else {
                        result.insert(result.end(), leftComponents.begin(), leftComponents.end());
                    }
                }
                else {
                    if (rightComponents.size() > 0) {
                        result.insert(result.end(), rightComponents.begin(), rightComponents.end());
                    }
                    else {
                    }
                }

                return result;
            }
        }
        return {};
    }

    /*
     *
     */
    std::vector<expr*> theory_str::parse_regex_components(expr* reg){
        ast_manager &m = get_manager();
        std::vector<expr*> result;
        ensure_enode(reg);
        std::vector<expr*> components = collect_alternative_components(reg);
        if (components.size() > 1){
            for (const auto& c : components) {
                std::vector<expr*> tmp = parse_regex_components(c);
                for (const auto& comp : tmp)
                    result.push_back(comp);
            }
            bool merge = true;
            expr* tmp = nullptr;
            for (const auto& s : result)
                if (u.re.is_star(s) || u.re.is_plus(s)){
                    merge = false;
                    break;
                }
                else {
                    if (tmp == nullptr)
                        tmp = s;
                    else
                        tmp = u.re.mk_union(tmp, s);
                }

            if (merge == true) {
                result.push_back(tmp);
                return result;
            }
            else
                return result;
        }
        else {
            if (u.re.is_concat(reg)) {
                expr* arg0 = to_app(reg)->get_arg(0);
                expr* arg1 = to_app(reg)->get_arg(1);
                std::vector<expr*> tmp00 = parse_regex_components(arg0);
                std::vector<expr*> tmp01 = parse_regex_components(arg1);

                for (int i = 0; i < std::min((int)tmp00.size(), 10); i ++)
                    for (int j = 0; j < std::min((int)tmp01.size(), 10); j ++) {
                        expr* tmp = u.re.mk_concat(tmp00[i], tmp01[j]);
                        ensure_enode(tmp);
                        result.push_back(tmp);
                    }

                return result;
            }
        }

        result.push_back(reg);
        return result;
    }

    /**
     * (abc|cde|ghi)*
     */
    void theory_str::optimizeFlatAutomaton(zstring &s){
        zstring org = s;
        zstring tmp = s.extract(1, s.length() - 3);
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << tmp << std::endl;);
        if (!tmp.contains("(") && !tmp.contains(")")) {
            s = tmp;
        }
        else {
            std::set<zstring> ret = extendComponent(tmp);
            STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " *** " << tmp << std::endl;);
            SASSERT(ret.size() > 0);
            s = "";
            for (const auto &it: ret) {
                s = s + "|(" + it + ")";
            }
            s = s.extract(1, s.length() - 1);

            STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " *** " << s << std::endl;);
        }

        if (org[org.length() - 1] == '*')
            s = zstring("(") + s + ")*";
        else if (org[org.length() - 1] == '+')
            s = zstring("(") + s + ")+";
        else {
            SASSERT(false);
        }
    }

    /*
     * (a)|(b | c) --> {a, b, c}
     */
    std::set<zstring> theory_str::extendComponent(zstring s){
        if (s.length() == 1)
            return {s};
        std::vector<zstring> components = collect_alternative_components(s);
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << std::endl;);
        if (components.size() > 0) {
            if (components.size() == 1)
                return {components[0]};
            std::set<zstring> ret;
            for (unsigned i = 0 ; i < components.size(); ++i) {
                removeExtraParentheses(components[i]);
                std::set<zstring> tmp = extendComponent(components[i]);
                ret.insert(tmp.begin(), tmp.end());
            }
            return ret;
        }
        else
            SASSERT(false);
        return {};
    }

    /*
     * (a) | (b) --> {a, b}
     */
    std::vector<zstring> theory_str::collect_alternative_components(zstring str){
        if (str.length() <= 2)
            return {str};
        else if (str[0] == '(' && str[str.length() - 1] == ')' && find_correspond_right_parentheses(0, str) == str.length() - 1) {
            return collect_alternative_components(str.extract(1, str.length() - 2));
        }
        else {
            std::vector<zstring> result;
            int counter = 0;
            unsigned startPos = 0;
            for (unsigned j = 0; j < str.length(); ++j) {
                if (str[j] == ')') {
                    counter--;
                } else if (str[j] == '(') {
                    counter++;
                } else if ((str[j] == '|' || str[j] == '~') && counter == 0) {
                    zstring tmp = str.extract(startPos, j - startPos);
                    std::vector<zstring> tmp_vec = collect_alternative_components(tmp);

                    result.insert(result.end(), tmp_vec.begin(), tmp_vec.end());
                    startPos = j + 1;
                }
            }
            if (startPos != 0) {
                zstring tmp = str.extract(startPos, str.length() - startPos);
                std::vector<zstring> tmp_vec = collect_alternative_components(tmp);

                result.insert(result.end(), tmp_vec.begin(), tmp_vec.end());
            }
            else {
                return {str};
            }
            return result;
        }
    }

    std::vector<expr*> theory_str::collect_alternative_components(expr* v){
        std::vector<expr*> result;
        if (!collect_alternative_components(v, result))
            result.clear();
        return result;
    }


    bool theory_str::collect_alternative_components(expr* v, std::vector<zstring>& ret){
        if (u.re.is_to_re(v)){
            expr* arg0 = to_app(v)->get_arg(0);
            zstring tmpStr;
            u.str.is_string(arg0, tmpStr);
            ret.push_back(tmpStr);
        }
        else if (u.re.is_union(v)){
            expr* arg0 = to_app(v)->get_arg(0);
            if (!collect_alternative_components(arg0, ret))
                return false;
            expr* arg1 = to_app(v)->get_arg(1);
            if (!collect_alternative_components(arg1, ret))
                return false;
        }
        else if (u.re.is_star(v) || u.re.is_plus(v)) {
            expr* arg0 = to_app(v)->get_arg(0);
            return collect_alternative_components(arg0, ret);
        }
        else if (u.re.is_concat(v)){
            return false;
        }
        else if (u.re.is_range(v)){
            expr* arg0 = to_app(v)->get_arg(0);
            expr* arg1 = to_app(v)->get_arg(1);
            zstring start, finish;
            u.str.is_string(arg0, start);
            u.str.is_string(arg1, finish);
            SASSERT(start.length() == 1);
            SASSERT(finish.length() == 1);

            for (int i = start[0]; i <= finish[0]; ++i){
                zstring tmp(i);
                ret.push_back(tmp);
            }
        }
        else {
            STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << mk_pp(v, get_manager()) << std::endl;);
            SASSERT(false);
        }
        return true;
    }

    bool theory_str::collect_alternative_components(expr* v, std::vector<expr*>& ret){
        if (u.re.is_to_re(v)){
            ret.push_back(v);
        }
        else if (u.re.is_union(v)){
            expr* arg0 = to_app(v)->get_arg(0);
            if (!collect_alternative_components(arg0, ret))
                return false;
            expr* arg1 = to_app(v)->get_arg(1);
            if (!collect_alternative_components(arg1, ret))
                return false;
        }
        else if (u.re.is_star(v) || u.re.is_plus(v)) {
            ret.push_back(v);
        }
        else if (u.re.is_concat(v)){
            return false;
        }
        else if (u.re.is_range(v)){
            expr* arg0 = to_app(v)->get_arg(0);
            expr* arg1 = to_app(v)->get_arg(1);
            zstring start, finish;
            u.str.is_string(arg0, start);
            u.str.is_string(arg1, finish);
            SASSERT(start.length() == 1);
            SASSERT(finish.length() == 1);

            for (int i = start[0]; i <= finish[0]; ++i){
                expr* tmp = mk_string(i);
                ret.push_back(tmp);
            }
        }
        else {
            STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << mk_pp(v, get_manager()) << std::endl;);
            SASSERT(false);
        }
        return true;
    }

    std::set<zstring> theory_str::collect_strs_in_membership(expr* v){
        std::set<zstring> ret;
        collect_strs_in_membership(v, ret);
        return ret;
    }

    void theory_str::collect_strs_in_membership(expr* v, std::set<zstring> &ret) {
        if (u.re.is_to_re(v)){
            expr* arg0 = to_app(v)->get_arg(0);
            zstring tmpStr;
            u.str.is_string(arg0, tmpStr);
            ret.insert(tmpStr);
        }
        else if (u.re.is_union(v)){
            collect_strs_in_membership(to_app(v)->get_arg(0), ret);
            collect_strs_in_membership(to_app(v)->get_arg(1), ret);
        }
        else if (u.re.is_star(v) || u.re.is_plus(v)) {
            collect_strs_in_membership(to_app(v)->get_arg(0), ret);
        }
        else if (u.re.is_concat(v)){
            collect_strs_in_membership(to_app(v)->get_arg(0), ret);
            collect_strs_in_membership(to_app(v)->get_arg(1), ret);
        }
        else if (u.re.is_range(v)){
            expr* arg0 = nullptr;
            expr* arg1 = nullptr;
            arg0 = to_app(v)->get_arg(0);
            arg1 = to_app(v)->get_arg(1);
            zstring start, finish;
            u.str.is_string(arg0, start);
            u.str.is_string(arg1, finish);
            SASSERT(start.length() == 1);
            SASSERT(finish.length() == 1);

            for (int i = start[0]; i <= finish[0]; ++i) {
                zstring tmp((char)i);
                ret.insert(tmp);
            }
        }
        else
            NOT_IMPLEMENTED_YET();
    }


    /*
     *
     */
    int theory_str::find_correspond_right_parentheses(int leftParentheses, zstring str){
        SASSERT (str[leftParentheses] == '(');
        int counter = 1;
        for (unsigned j = leftParentheses + 1; j < str.length(); ++j) {
            if (str[j] == ')'){
                counter--;
                if (counter == 0){
                    return j;
                }
            }
            else if (str[j] == '('){
                counter++;
            }
        }
        return -1;
    }

    /*
     * (a) --> a
     */
    void theory_str::removeExtraParentheses(zstring &s){
        while (s[0] == '(' && find_correspond_right_parentheses(0, s) == (int)s.length() - 1 && s.length() > 2)
            s = s.extract(1, s.length() - 2);
    }

    expr* theory_str::remove_star_in_star(expr* reg){
        if (u.re.is_star(reg)){
            if (contain_star(to_app(reg)->get_arg(0))) {
                STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << mk_pp(reg, get_manager()) << std::endl;);
                return remove_star_in_star(to_app(reg)->get_arg(0));
            }
            else
                return u.re.mk_star(remove_star_in_star(to_app(reg)->get_arg(0)));
        }
        if (u.re.is_plus(reg)){
            if (contain_star(to_app(reg)->get_arg(0)))
                return remove_star_in_star(to_app(reg)->get_arg(0));
            else
                return u.re.mk_plus(remove_star_in_star(to_app(reg)->get_arg(0)));
        }
        else if (u.re.is_concat(reg)) {
            expr* arg0 = to_app(reg)->get_arg(0);
            expr* arg1 = to_app(reg)->get_arg(1);
            return u.re.mk_concat(remove_star_in_star(arg0), remove_star_in_star(arg1));
        }
        else if (u.re.is_union(reg)) {
            expr* arg0 = to_app(reg)->get_arg(0);
            expr* arg1 = to_app(reg)->get_arg(1);
            return u.re.mk_union(remove_star_in_star(arg0), remove_star_in_star(arg1));
        }
        else
            return reg;
    }

    bool theory_str::contain_star(expr* reg){
        if (u.re.is_star(reg)){
            return true;
        }
        if (u.re.is_plus(reg)){
            return true;
        }
        else if (u.re.is_concat(reg)) {
            return contain_star(to_app(reg)->get_arg(0)) || contain_star(to_app(reg)->get_arg(1));
        }
        else if (u.re.is_union(reg)) {
            return contain_star(to_app(reg)->get_arg(0)) || contain_star(to_app(reg)->get_arg(1));
        }
        else
            return false;
    }

    /*
     *
     */
    zstring theory_str::getStdRegexStr(expr* regex) {
        if (u.re.is_to_re(regex)) {
            expr* arg0 = to_app(regex)->get_arg(0);
            zstring value;
            u.str.is_string(arg0, value);
            return value;
        } else if (u.re.is_concat(regex)) {
            expr* arg0 = to_app(regex)->get_arg(0);
            expr* arg1 = to_app(regex)->get_arg(1);
            zstring reg1Str = getStdRegexStr(arg0);
            zstring reg2Str = getStdRegexStr(arg1);
            STRACE("str", tout << __LINE__ <<  " " << zstring("(") + reg1Str + ")(" + reg2Str + ")" << std::endl;);
            return zstring("(") + reg1Str + ")(" + reg2Str + ")";
        } else if (u.re.is_union(regex)) {
            expr* arg0 = to_app(regex)->get_arg(0);
            expr* arg1 = to_app(regex)->get_arg(1);
            zstring reg1Str = getStdRegexStr(arg0);
            zstring reg2Str = getStdRegexStr(arg1);
            STRACE("str", tout << __LINE__ <<  " " << zstring("(") + reg1Str + ")~(" + reg2Str + ")" << std::endl;);
            return  zstring("(") + reg1Str + ")~(" + reg2Str + ")";
        } else if (u.re.is_star(regex)) {
            expr* arg0 = to_app(regex)->get_arg(0);
            zstring reg1Str = getStdRegexStr(arg0);
            STRACE("str", tout << __LINE__ <<  " " << zstring("(") + reg1Str + ")*" << std::endl;);
            return zstring("(") + reg1Str + ")*";
        } else if (u.re.is_range(regex)) {
            expr* arg0 = to_app(regex)->get_arg(0);
            expr* arg1 = to_app(regex)->get_arg(1);
            zstring start;
            zstring finish;
            u.str.is_string(arg0, start);
            u.str.is_string(arg1, finish);

            SASSERT(start.length() == 1);
            SASSERT(finish.length() == 1);
            zstring ret;
            for (unsigned i = start[0]; i <= (unsigned)finish[0]; ++i)
                ret = ret + "~(" + (char)i + ")";
            return ret.extract(1, ret.length() - 1);
        }
        else if (u.re.is_full_seq(regex)){
            std::set<char> tobeEncoded = {'?', '\\', '|', '"', '(', ')', '~', '&', '\'', '+', '%', '#', '*'};
            zstring tmp;
            for (int i = 32; i <= 126; ++i)
                if (tobeEncoded.find((char)i) == tobeEncoded.end())
                    tmp = tmp + "(" + (char)i + ")~";
            return zstring("(") + tmp.extract(0, tmp.length() - 1) + ")*";
        }
        else if (u.re.is_full_char(regex)){
            std::set<char> tobeEncoded = {'?', '\\', '|', '"', '(', ')', '~', '&', '\'', '+', '%', '#', '*'};
            zstring tmp;
            for (int i = 32; i <= 126; ++i)
                if (tobeEncoded.find((char)i) == tobeEncoded.end())
                    tmp = tmp + "(" + (char)i + ")~";
            return tmp.extract(0, tmp.length() - 1);
        } else
            SASSERT(false);
        return nullptr;
    }

    /*
     * convert lhs == rhs to SMT formula
     */
    expr* theory_str::equality_to_arith(
            std::vector<std::pair<expr*, int>> lhs_elements,
            std::vector<std::pair<expr*, int>> rhs_elements,
            std::map<expr*, int> non_fresh_Variables,
            int p){
        ast_manager &m = get_manager();
        th_rewriter rw(m);

        //swap if lhs > rhs
        if (lhs_elements.size() > rhs_elements.size()){
            std::vector<std::pair<expr*, int>> tmpVector = lhs_elements;
            lhs_elements = rhs_elements;
            rhs_elements = tmpVector;
        }

        std::string tmp01;
        std::string tmp02;
        for (unsigned i = 0; i < lhs_elements.size(); ++i)
            tmp01 = tmp01 + "---" + expr2str(lhs_elements[i].first);
        for (unsigned i = 0; i < rhs_elements.size(); ++i)
            tmp01 = tmp01 + "+++" + expr2str(rhs_elements[i].first);
        if (generatedEqualities.find(tmp01) == generatedEqualities.end() &&
                lhs_elements.size() != 0 && rhs_elements.size() != 0){
            expr_ref_vector cases = arrange(
                    lhs_elements,
                    rhs_elements,
                    non_fresh_Variables,
                    p);
            generatedEqualities.emplace(tmp01);
            if (cases.size() > 0) {
                expr_ref tmp(createOrOperator(cases), m);
                return tmp.get();
            }
            else {
                return nullptr;
            }
        }
        else
            return m.mk_true();
    }


    /*
     * lhs: size of the lhs
     * rhs: size of the rhs
     * lhs_elements: elements of lhs
     * rhs_elements: elements of rhs
     *
     * Pre-Condition: x_i == 0 --> x_i+1 == 0
     *
     */
    expr_ref_vector theory_str::arrange(
            std::vector<std::pair<expr*, int>> lhs_elements,
            std::vector<std::pair<expr*, int>> rhs_elements,
            std::map<expr*, int> non_fresh_Variables,
            int p){
        /* first base case */
        clock_t t = clock();
        ast_manager &m = get_manager();
#if 1
        /* because arrangements are reusable, we use "general" functions */
        setup_0_0_general();
        /* second base case : first row and first column */
        setup_0_n_general(lhs_elements.size(), rhs_elements.size());
        setup_n_0_general(lhs_elements.size(), rhs_elements.size());
        /* general cases */
        setup_n_n_general(lhs_elements.size(), rhs_elements.size());

        /* because of "general" functions, we need to refine arrangements */
        std::vector<Arrangment> possibleCases;
        get_arrangements(lhs_elements, rhs_elements, non_fresh_Variables, possibleCases);
#endif

        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << std::endl;);
        for (unsigned i = 0; i < lhs_elements.size(); ++i)
            STRACE("str", tout << mk_pp(lhs_elements[i].first, m) << " ";);

        STRACE("str", tout << std::endl;);
        for (unsigned i = 0; i < rhs_elements.size(); ++i)
            STRACE("str", tout << mk_pp(rhs_elements[i].first, m) << " ";);
        STRACE("str", tout <<  std::endl;);

        expr_ref_vector cases(m);
        /* 1 vs n, 1 vs 1, n vs 1 */
        for (unsigned i = 0; i < possibleCases.size(); ++i) {

            arrangements[std::make_pair(lhs_elements.size() - 1, rhs_elements.size() - 1)][i].printArrangement("Checking case");
            expr* tmp = to_arith(p, possibleCases[i].left_arr, possibleCases[i].right_arr, lhs_elements, rhs_elements, non_fresh_Variables);

            if (tmp != nullptr) {
                cases.push_back(tmp);
                arrangements[std::make_pair(lhs_elements.size() - 1, rhs_elements.size() - 1)][i].printArrangement("Correct case");
                STRACE("str", tout << __LINE__ <<  "  " << mk_pp(tmp, m) << std::endl;);
            }
            else {
            }
        }
        return cases;

    }

    void theory_str::get_arrangements(std::vector<std::pair<expr*, int>> lhs_elements,
                                      std::vector<std::pair<expr*, int>> rhs_elements,
                                      std::map<expr*, int> non_fresh_Variables,
                                      std::vector<Arrangment> &possibleCases) {
        std::string firstVar = expr2str(lhs_elements[0].first);
        if ((firstVar.find(FLATPREFIX) != std::string::npos && lhs_elements.size() == p_bound.get_int64()) ||
            (lhs_elements.size() == 2 &&
             ((non_fresh_Variables.find(lhs_elements[0].first) != non_fresh_Variables.end() && lhs_elements[1].second % p_bound.get_int64() == 1) ||
              (lhs_elements[0].second % p_bound.get_int64() == -1 && lhs_elements[1].first == lhs_elements[0].first)))) {
            /* create manually */
            /*9999999 10000000 vs 1 1 1 1 1 */
            possibleCases.emplace_back(manuallyCreate_arrangment(lhs_elements, rhs_elements));
        } else {
            update_possible_arrangements(lhs_elements, rhs_elements,
                                         arrangements[std::make_pair(lhs_elements.size() - 1, rhs_elements.size() - 1)],
                                         possibleCases);
        }
    }

    void theory_str::update_possible_arrangements(
            std::vector<std::pair<expr*, int>> lhs_elements,
            std::vector<std::pair<expr*, int>> rhs_elements,
            std::vector<Arrangment> tmp,
            std::vector<Arrangment> &possibleCases) {
        for (unsigned i = 0; i < tmp.size(); ++i)
            if (tmp[i].isPossibleArrangement(lhs_elements, rhs_elements))
                possibleCases.emplace_back(tmp[i]);
    }

    /*
     *
     */
    theory_str::Arrangment theory_str::manuallyCreate_arrangment(
            std::vector<std::pair<expr*, int>> lhs_elements,
            std::vector<std::pair<expr*, int>> rhs_elements){

        /* create manually */
        /*10000000 10000000 vs 0 0 1 1 1 */
        std::vector<int> left_arr;
        std::vector<int> right_arr;
        unsigned mid = rhs_elements.size() / 2;
        if (false) {
            left_arr.emplace_back(SUMFLAT);
            left_arr.emplace_back(SUMFLAT);
            for (unsigned i = 0; i <= mid; ++i)
                right_arr.emplace_back(0);
            for (unsigned i = mid + 1; i < rhs_elements.size(); ++i)
                right_arr.emplace_back(1);
        }
        else {
            left_arr.emplace_back(EMPTYFLAT);
            left_arr.emplace_back(SUMFLAT);
            for (unsigned i = 0; i < rhs_elements.size(); ++i)
                right_arr.emplace_back(1);
        }
        return Arrangment(left_arr, right_arr);
    }

    /*
     * a_1 + a_2 + b_1 + b_2 = c_1 + c_2 + d_1 + d_2 ---> SMT
     */
    expr* theory_str::to_arith(int p,
                            std::vector<int> left_arr,
                            std::vector<int> right_arr,
                            std::vector<std::pair<expr*, int>> lhs_elements,
                            std::vector<std::pair<expr*, int>> rhs_elements,
                            std::map<expr*, int> non_fresh_Variables){
        ast_manager &m = get_manager();
        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__  << std::endl;);
        expr_ref_vector result_element(m);

        bool checkLeft[lhs_elements.size()];
        bool checkRight[rhs_elements.size()];
        memset(checkLeft, 0, sizeof checkLeft);
        memset(checkRight, 0, sizeof checkRight);

        /* do the left */
        for (unsigned i = 0; i < left_arr.size(); ++i)
            if (!checkLeft[i]) {
                if (left_arr[i] == SUMFLAT) { /* a = bx + cy */
                    checkLeft[i] = true;

                    std::vector<std::pair<expr*, int>> elements;
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
                    STRACE("str", tout << __LINE__ <<  " before optimizing mode: " << std::endl;);
                    int optimizing = NONE;
                    if (!flat_enabled)
                        optimizing = canBeOptimized_LHS(i, startPos, j, left_arr, right_arr, vectorExpr2vectorStr(lhs_elements), vectorExpr2vectorStr(rhs_elements));
                    STRACE("str", tout << __LINE__ <<  "  optimizing mode: " << optimizing << std::endl;);

                    switch (optimizing) {
                        case NONE:
                            break;
                        case LEFT_EMPTY:
//                            if (left_arr.size() != 2)
//                                return nullptr;

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
                            return nullptr; // duplicate case
                            checkLeft[i + 1] = true;
                            checkRight[j + 1] = true;
                            elements.emplace_back(rhs_elements[j + 1]);
                            STRACE("str", tout << __LINE__ <<  "  RIGHT_EQUAL: elements size: " << elements.size() << std::endl;);
                            break;
                        case RIGHT_SUM:
                            return nullptr; // duplicate case
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

                    expr_ref tmp(generate_constraint02(
                            lhs_elements[i],
                            elements,
                            p,
                            non_fresh_Variables,
                            optimizing != NONE), m);

                    if (tmp == nullptr) { /* cannot happen due to const */
                        STRACE("str", tout << __LINE__ <<  " 02 because of lhs@i: " << i << std::endl;);
                        return nullptr;
                    }
                    else
                        STRACE("str", tout << __LINE__ <<  " done 02 " << i << std::endl;);
                    result_element.push_back(tmp);

                }
            }
        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__  << std::endl;);
        /* do the right */
        for (unsigned i = 0; i < right_arr.size(); ++i)
            if (!checkRight[i]){
                if (right_arr[i] == SUMFLAT) { /* a = bx + cy */
                    checkRight[i] = true;

                    std::vector<std::pair<expr*, int>> elements;
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
                    STRACE("str", tout << __LINE__ <<  " before optimizing mode: " << std::endl;);
                    int optimizing = NONE;
                    if (!flat_enabled)
                        canBeOptimized_RHS(j, startPos, i, left_arr, right_arr, vectorExpr2vectorStr(lhs_elements), vectorExpr2vectorStr(rhs_elements));
                    STRACE("str", tout << __LINE__ <<  "  optimizing mode: " << optimizing << std::endl;);
                    switch (optimizing) {
                        case NONE:
                            break;
                        case LEFT_EMPTY:
//                            if (right_arr.size() != 2)
//                                return nullptr;
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
                            return nullptr; // duplicate case
                            checkRight[i + 1] = true;
                            checkLeft[j + 1] = true;
                            elements.emplace_back(lhs_elements[j + 1]);
                            break;
                        case RIGHT_SUM:
                            return nullptr; // duplicate case
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
                    expr_ref tmp(generate_constraint02(
                            rhs_elements[i],
                            elements,
                            p,
                            non_fresh_Variables, optimizing != NONE), m);
                    if (tmp == nullptr) { /* cannot happen due to const */
                        STRACE("str", tout << __LINE__ <<  " 02 because of rhs@i: " << i << std::endl;);
                        return nullptr;
                    }
                    STRACE("str", tout << __LINE__ <<  " done 02 " << i << std::endl;);
                    STRACE("str", tout << __LINE__ <<  mk_pp(tmp, m) << i << std::endl;);
                    result_element.push_back(tmp);
                }
            }

        for (unsigned i = 0; i < left_arr.size(); ++i)
            if (!checkLeft[i]) {
                if (left_arr[i] == EMPTYFLAT) {
                    zstring value;
                    if (u.str.is_string(lhs_elements[i].first, value)) {
                        if (value.length() == 1) {
                            return nullptr;
                        } else {
                            if (lhs_elements[i].second % p_bound.get_int64() == -1 && i + 1 < left_arr.size() && left_arr[i + 1] == EMPTYFLAT)
                                return nullptr;
                        }
                    }
                    else {
                        if (lhs_elements[i].second % p_bound.get_int64() == 0 && i + 1 < left_arr.size() && left_arr[i + 1] == EMPTYFLAT){
                            rational bound;
                            if (lower_bound(lhs_elements[i].first, bound) && bound.get_int64() > 0){
                                STRACE("str", tout << __LINE__ <<  " " << mk_pp(lhs_elements[i].first, m) << " cannot be empty because of lowerbound " << bound.get_int64() << std::endl;);
                                return nullptr;
                            }
                        }
                    }
                    checkLeft[i] = true;
                }
            }

        for (unsigned i = 0; i < right_arr.size(); ++i)
            if (!checkRight[i]){
                if (right_arr[i] == EMPTYFLAT) {
                    zstring value;
                    if (u.str.is_string(rhs_elements[i].first, value)) {
                        if (value.length() == 1) {
                            return nullptr;
                        } else {
                            if (rhs_elements[i].second % p_bound.get_int64() == -1 && i + 1 < right_arr.size() && right_arr[i + 1] == EMPTYFLAT)
                                return nullptr;
                        }
                    }
                    else {
                        if (rhs_elements[i].second % p_bound.get_int64() == 0 && i + 1 < right_arr.size() && right_arr[i + 1] == EMPTYFLAT){
                            rational bound;
                            if (lower_bound(rhs_elements[i].first, bound) && bound.get_int64() > 0){
                                STRACE("str", tout << __LINE__ <<  " " << mk_pp(rhs_elements[i].first, m) << " cannot be empty because of lowerbound " << bound.get_int64() << std::endl;);
                                return nullptr;
                            }
                        }
                    }
                    checkRight[i] = true;
                }
            }


        STRACE("str", tout << __LINE__ <<  " Do the rest " << std::endl;);
        /* do the rest */
        /* do not need AND */
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
                int optimizing = canBeOptimized_LHS(i, -1, j, left_arr, right_arr, vectorExpr2vectorStr(lhs_elements), vectorExpr2vectorStr(rhs_elements));
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
                expr* tmp = generate_constraint01(
                        lhs_elements[i],
                        (std::pair<expr*, int>)rhs_elements[left_arr[i]],
                        p,
                        non_fresh_Variables,
                        optimizing != NONE);
                if (tmp == nullptr) { /* cannot happen due to const */
                    return nullptr;
                }
                result_element.push_back(tmp);
            }

        for (unsigned i = 0 ; i < rhs_elements.size(); ++i)
            if (checkRight[i] == false) {
                STRACE("str", tout << __LINE__ <<  " error rhs@i: " << i << std::endl;);
                SASSERT (false);
            }
        STRACE("str", tout << __LINE__ <<  " finish " << __FUNCTION__ << std::endl;);
        /* sum up */
        return createAndOperator(result_element);
    }

    /*
	 *
	 * Flat = empty
	 */

    expr* theory_str::generate_constraint00(
            std::pair<expr*, int> a,
            std::string l_r_hs){
        return createEqualOperator(m_autil.mk_int(0), getExprVarFlatSize(a));
    }

    /*
	 * Flat = Flat
	 * size = size && it = it  ||
	 * size = size && it = 1
	 */
    expr* theory_str::generate_constraint01(
            std::pair<expr*, int> a, std::pair<expr*, int> b,
            int pMax,
            std::map<expr*, int> non_fresh_Variables,
            bool optimizing){
        ast_manager &m = get_manager();
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(a.first, m) << " " << mk_pp(b.first, m)<< std::endl;);
        bool isConstA = a.second < 0;
        bool isConstB = b.second < 0;
        expr_ref_vector result(m);

        /*
         * str-int var
         */
        expr* extra_assert = nullptr;
        if (!const_vs_str_int(a.first, {b}, extra_assert)){
            result.push_back(extra_assert);
        }

        expr* reg = nullptr;
        if (isInternalRegexVar(a.first, reg)) {
            if (!const_vs_regex(reg, {b}))
                return nullptr;
            else {
            }

        }
        else if (isInternalRegexVar(b.first, reg)) {
            if (!const_vs_regex(reg, {a}))
                return nullptr;
        }
        expr* nameA = nullptr;
        expr* nameB = nullptr;
        if (optimizing){
            nameA = getExprVarSize(a);
            nameB = getExprVarSize(b);
        }
        else {
            nameA = getExprVarFlatSize(a);
            nameB = getExprVarFlatSize(b);
        }

        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(a.first, m) << " " << mk_pp(b.first, m)<< std::endl;);
        /* do not need AND */
        result.push_back(createEqualOperator(nameA, nameB));

        if (!isConstA && !isConstB) {
            /* size = size && it = it */

            if (non_fresh_Variables.find(b.first) != non_fresh_Variables.end() &&
                non_fresh_Variables.find(a.first) != non_fresh_Variables.end()){

                if (!optimizing) {
                    STRACE("str", tout << __LINE__ <<  " generateConstraint01: non_fresh_Var " << mk_pp(a.first, m) << " == non_fresh_Var " << mk_pp(b.first, m) << std::endl;);
                    if (!flat_enabled)
                        result.push_back(unroll_non_fresh_variable(b, {a}, non_fresh_Variables, optimizing, pMax));
                    else {
                        if ((string_int_vars.find(a.first) != string_int_vars.end() && a.second % p_bound.get_int64() == 1) ||
                                (string_int_vars.find(b.first) != string_int_vars.end() && b.second % p_bound.get_int64() == 1))
                            result.push_back(generate_constraint_flat_flat(a, {b}, 0, pMax, str_int_bound));
                        else
                            result.push_back(generate_constraint_flat_flat(a, {b}, 0, pMax, p_bound));
                    }
                }
                else {
                    if (!flat_enabled) {
                        expr *arrA = getExprVarFlatArray(a);
                        expr *arrB = getExprVarFlatArray(b);
                        for (int i = 0; i < std::max(non_fresh_Variables[b.first], non_fresh_Variables[a.first]); ++i) {
                            expr_ref_vector ors(m);
                            ors.push_back(createEqualOperator(createSelectOperator(arrA, m_autil.mk_int(i)),
                                                              createSelectOperator(arrB, m_autil.mk_int(i))));
                            ors.push_back(createLessEqOperator(nameA, m_autil.mk_int(i)));
                            result.push_back(createOrOperator(ors));
                        }
                    }
                    else {
                        result.push_back(generate_constraint_var_var(a, b, pMax, p_bound));
                    }
                }
            }
        }
        else if (isConstA && isConstB) {
            zstring valA;
            zstring valB;
            u.str.is_string(a.first, valA);
            u.str.is_string(b.first, valB);
            if ((p_bound.get_int64() == 1 || optimizing) && valA != valB) /* const = const */
                return nullptr;
            expr_ref_vector possibleCases(m);

            if (a.second <= REGEX_CODE && b.second % p_bound.get_int64() == -1){
                expr* regex = reg;
                unsigned length = 0;
                if (u.re.is_plus(regex))
                    length = 1;
                while (length <= valB.length()) {
                    zstring regexValue = valB.extract(0, length);
                    if (matchRegex(regex, regexValue)) {
                        expr_ref_vector ands(m);
                        ands.push_back(createEqualOperator(nameA, m_autil.mk_int(length)));
                        expr* prelhs = nullptr;
                        expr* prerhs = nullptr;
                        for (int i = 0; i < length - 1; ++i) {
                            // TODO arr vs arr
                        }
                        possibleCases.push_back(createEqualOperator(nameA, m_autil.mk_int(length)));
                    }
                    length++;
                    STRACE("str", tout << __LINE__ <<  "  accept: " << regexValue << std::endl;);
                }
            }
            else if (a.second <= REGEX_CODE && b.second % p_bound.get_int64() == 0){
                expr* regex = reg;
                unsigned length = 0;
                if (u.re.is_plus(regex))
                    length = 1;
                while (length <= valB.length()) {
                    zstring regexValue = valB.extract(valB.length() - length, length);
                    if (matchRegex(regex, regexValue)) {
                        // TODO arr vs arr
                        possibleCases.push_back(createEqualOperator(nameA, m_autil.mk_int(length)));
                    }
                    length++;
                    STRACE("str", tout << __LINE__ <<  "  accept: " << regexValue << std::endl;);
                }
            }
            else if (b.second <= REGEX_CODE && a.second % p_bound.get_int64() == -1){
                expr* regex = reg;
                unsigned length = 0;
                if (u.re.is_plus(regex))
                    length = 1;
                while (length <= valA.length()) {
                    zstring regexValue = valA.extract(0, length);
                    if (matchRegex(regex, regexValue)) {
                        // TODO arr vs arr
                        possibleCases.push_back(createEqualOperator(nameA, m_autil.mk_int(length)));
                    }
                    length++;
                    STRACE("str", tout << __LINE__ <<  "  accept: " << regexValue << std::endl;);
                }
            }
            else if (b.second <= REGEX_CODE && a.second % p_bound.get_int64() == 0){
                expr* regex = reg;
                unsigned length = 0;
                if (u.re.is_plus(regex))
                    length = 1;
                while (length <= valA.length()) {
                    zstring regexValue = valA.extract(valA.length() - length, length);
                    if (matchRegex(regex, regexValue)) {
                        // TODO arr vs arr
                        possibleCases.push_back(createEqualOperator(nameA, m_autil.mk_int(length)));
                    }
                    length++;
                    STRACE("str", tout << __LINE__ <<  "  accept: " << regexValue << std::endl;);
                }
            }
            else if (a.second <= REGEX_CODE && b.second <= REGEX_CODE) {
                NOT_IMPLEMENTED_YET();
                expr* regexA = nullptr;
                isInternalRegexVar(a.first, regexA);
                unsigned length = 0;
                if (u.re.is_plus(regexA))
                    length = 1;

                expr* regexB = nullptr;
                isInternalRegexVar(b.first, regexB);
                if (u.re.is_plus(regexB))
                    length = 1;

                if (matchRegex(regexA, regexB)) {
                    std::vector<zstring> aComp;
                    collect_alternative_components(regexA, aComp);
                    std::vector<zstring> bComp;
                    collect_alternative_components(regexB, bComp);

                    int minA = 10000, minB = 10000, maxA = 0, maxB = 0;
                    for (const auto& s : aComp) {
                        minA = std::min(minA, (int)s.length());
                        maxA = std::max(maxA, (int)s.length());
                    }

                    for (const auto& s : bComp) {
                        minB = std::min(minB, (int)s.length());
                        maxB = std::max(maxB, (int)s.length());
                    }

                    if (minA == maxA && minB == maxB) {
                        unsigned lcdLength = lcd(minA, minB);
                        possibleCases.push_back(createEqualOperator(m_autil.mk_int(0), createModOperator(nameA,
                                                                                                         m_autil.mk_int(
                                                                                                                 lcdLength))));
                    }
                }
                else {
                    possibleCases.push_back(createEqualOperator(nameA, m_autil.mk_int(0)));
                }
            }
            else if (!optimizing) {
                STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(a.first, m) << std::endl;);
                if ((a.second % p_bound.get_int64() == -1 || valA.length() == 1) && (b.second % p_bound.get_int64()  == -1 || valB.length() == 1)) /* head vs head */ {
                    expr* realHaystack = nullptr;
                    if (not_contain(a.first, b.first, realHaystack) || not_contain(b.first, a.first, realHaystack))
                        return nullptr;


                    STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(a.first, m) << std::endl;);
                    for (int i = std::min(valA.length(), valB.length()); i >= 0; --i) {
                        if (valA.extract(0, i) == valB.extract(0, i)) {
                            /* size can be from 0..i */
                            possibleCases.push_back(createLessEqOperator(nameA, m_autil.mk_int(i)));
                        }
                    }
                }
                else if ((a.second % p_bound.get_int64() == -1 || valA.length() == 1) && b.second % p_bound.get_int64() == 0) /* head vs tail */ {
                    STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(a.first, m) << std::endl;);
                    for (int i = std::min(valA.length(), valB.length()); i >= 0; --i) {
                        if (valA.extract(0, i) == valB.extract(valB.length() - i, i)) {
                            /* size can be i */
                            possibleCases.push_back(createEqualOperator(nameA, m_autil.mk_int(i)));
                        }
                    }
                }
                else if (a.second % p_bound.get_int64() == 0 && (b.second % p_bound.get_int64()  == -1 || valB.length() == 1)) /* tail vs head */ {
                    STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(a.first, m) << std::endl;);
                    for (int i = std::min(valA.length(), valB.length()); i >= 0; --i) {
                        if (valB.extract(0, i) == valA.extract(valA.length() - i, i)) {
                            /* size can be i */
                            possibleCases.push_back(createEqualOperator(nameA, m_autil.mk_int(i)));
                        }
                    }
                }
                else if (a.second % p_bound.get_int64() == 0 && b.second % p_bound.get_int64() == 0) /* tail vs tail */ {
                    STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(a.first, m) << std::endl;);
                    for (int i = std::min(valA.length(), valB.length()); i >= 0; --i) {
                        if (valA.extract(valA.length() - i, i) == valB.extract(valB.length() - i, i)) {
                            /* size can be i */
                            possibleCases.push_back(createLessEqOperator(nameA, m_autil.mk_int(i)));
                        }
                    }
                }
            }
            else {
                SASSERT (optimizing);
            }
            STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << possibleCases.size() << std::endl;);
            /* create or constraint */
            if ((int)possibleCases.size() == 0)
                return nullptr;
            else {
                expr* tmpE = createOrOperator(possibleCases);
                if (tmpE != m.mk_false())
                    result.push_back(createOrOperator(possibleCases));
                else
                    return nullptr;
            }
            STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << possibleCases.size() << std::endl;);
            return createAndOperator(result);
        }

        else if (isConstA) {
            /* record characters for some special variables */
            if (non_fresh_Variables.find(b.first) != non_fresh_Variables.end()){
                std::vector<std::pair<expr*, int>> elements;
                if (optimizing) {
                    elements.emplace_back(std::make_pair(a.first, -1));
                    elements.emplace_back(std::make_pair(a.first, -2));
                }
                else
                    elements.emplace_back(a);
                result.push_back(unroll_non_fresh_variable(b, elements, non_fresh_Variables, optimizing));
            }
        }

        else { /* isConstB */
            /* size = size && it = 1*/
            if (non_fresh_Variables.find(a.first) != non_fresh_Variables.end()){
                std::vector<std::pair<expr*, int>> elements;
                if (optimizing) {
                    elements.emplace_back(std::make_pair(b.first, -1));
                    elements.emplace_back(std::make_pair(b.first, -2));
                }
                else
                    elements.emplace_back(b);
                result.push_back(unroll_non_fresh_variable(a, elements, non_fresh_Variables, optimizing));
            }
        }

        return createAndOperator(result);
    }

    expr* theory_str::generate_constraint_var_var(
            std::pair<expr*, int> a,
            std::pair<expr*, int> b,
            int pMax,
            rational bound){
        ast_manager &m = get_manager();
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(a.first, m) << " = " << mk_pp(b.first, m) << std::endl;);
        expr_ref_vector ands(m);
        a.second = 0;
        b.second = 0;
        for (int i = 1; i <= p_bound.get_int64(); i = i + 1) {
            if (i == 2 && (string_int_vars.find(a.first) != string_int_vars.end() || string_int_vars.find(b.first) != string_int_vars.end()))
                ands.push_back(generate_constraint_flat_flat(a, {b}, 0, pMax, str_int_bound));
            else
                ands.push_back(generate_constraint_flat_flat(a, {b}, 0, pMax, bound));
            a.second = a.second + 1;
            b.second = b.second + 1;
        }
        return createAndOperator(ands);
    }

    expr* theory_str::generate_constraint_flat_var(
            std::pair<expr*, int> a,
            std::vector<std::pair<expr*, int>> elementNames,
            int pos,
            int pMax,
            rational bound){
        ast_manager &m = get_manager();
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(a.first, m) << " = " << mk_pp(elementNames[pos].first, m) << std::endl;);
        expr_ref_vector ands(m);
        for (int i = 1; i <= p_bound.get_int64(); i = i + 1) {
            if (i == 2 && (string_int_vars.find(a.first) != string_int_vars.end() || string_int_vars.find(elementNames[pos].first) != string_int_vars.end()))
                ands.push_back(generate_constraint_flat_flat(a, elementNames, pos, pMax, str_int_bound));
            else
                ands.push_back(generate_constraint_flat_flat(a, elementNames, pos, pMax, bound));
            pos = pos + 1;
        }
        return createAndOperator(ands);
    }

    expr* theory_str::generate_constraint_flat_flat(
            std::pair<expr*, int> a,
            std::vector<std::pair<expr*, int>> elementNames,
            int pos,
            int pMax,
            rational bound,
            bool skip_init){
        ast_manager &m = get_manager();
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(a.first, m) << " = " << mk_pp(elementNames[pos].first, m) << std::endl;);
        rational zero(0);
        rational one(1);
        bool unrollMode = pMax == PMAX;
        std::pair<expr*, int> b = elementNames[pos];

        expr* lenA = getExprVarFlatSize(a);
        expr* lenB = getExprVarFlatSize(b);
        expr* arrA = getExprVarFlatArray(a);
        expr* arrB = getExprVarFlatArray(b);
        expr* iterA = getExprVarFlatIter(a);
        expr* iterB = getExprVarFlatIter(b);
        expr* pre_lhs = leng_prefix_lhs(a, elementNames, pos, false, unrollMode);
        expr* pre_rhs = leng_prefix_rhs(b, unrollMode);
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " pre_rhs: " << mk_pp(pre_rhs, m) << std::endl;);
        expr_ref_vector ands(m);

        if (elementNames.size() == 1) {
            ands.push_back(createEqualOperator(iterA, iterB));
            ands.push_back(createEqualOperator(lenA, lenB));

            for (rational i = one; i <= bound; i = i + one) {
                expr *at_i = mk_int(i);
                rational i_1 = i - one;
                expr *at_i_1 = mk_int(i_1);
                expr *premise = createGreaterEqOperator(lenA, at_i);
                expr *conclusion = createEqualOperator(
                        createSelectOperator(arrA, createAddOperator(pre_lhs, at_i_1)),
                        createSelectOperator(arrB, createAddOperator(pre_rhs, at_i_1)));
                ands.push_back(rewrite_implication(premise, conclusion));
            }
        }
        else {
            STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " pre_rhs: " << mk_pp(pre_rhs, m) << std::endl;);
            for (rational i = one; i <= bound; i = i + one) {
                expr *at_i = mk_int(i);
                rational i_1 = i - one;
                expr *at_i_1 = mk_int(i_1);
                expr *premise = createGreaterEqOperator(lenB, at_i);
                zstring val;
                expr* arr_b = nullptr;
                if (pre_rhs == mk_int(0) && u.str.is_string(elementNames[pos].first, val))
                    arr_b = mk_int(val[i_1.get_int64()]);
                else
                    arr_b = createSelectOperator(arrB, createAddOperator(pre_rhs, at_i_1));
                expr *conclusion = createEqualOperator(
                        createSelectOperator(arrA, createAddOperator(pre_lhs, at_i_1)),
                        arr_b);
                ands.push_back(rewrite_implication(premise, conclusion));
            }
        }

        if (!skip_init) {
            expr *reg = nullptr;
            if (isInternalRegexVar(a.first, reg)) {
                expr *to_assert = setup_regex_var(reg, arrA, bound, pre_lhs);
                ands.push_back(to_assert);
            }

            if (isInternalRegexVar(elementNames[pos].first, reg)) {
                expr *to_assert = setup_regex_var(reg, arrB, bound, pre_rhs);
                ands.push_back(to_assert);
            }
        }
        return createAndOperator(ands);
    }

    int theory_str::lcd(int x, int y) {
        int x1 = x;
        int y1 = y;
        if (x < y) {
            x1 = y;
            y1 = x;
        }

        int r = y1;
        while (r != 0) {
            r = x1 % y1;
            x1 = y1;
            y1 = r;
        }

        return x * y / x1;
    }

    bool theory_str::matchRegex(expr* a, zstring b){
        expr* tmp = u.re.mk_to_re(u.str.mk_string(b));
        return matchRegex(a, tmp);
    }

    bool theory_str::matchRegex(expr* a, expr* b) {
        expr* intersection = u.re.mk_inter(a, b);
        eautomaton *au01 = get_automaton(intersection);
        return !au01->is_empty();
    }

    /*
     * Flat = sum (flats)
     */
    expr* theory_str::generate_constraint02(
            std::pair<expr*, int> a,
            std::vector<std::pair<expr*, int>> elementNames,
            int pMax,
            std::map<expr*, int> non_fresh_Variables,
            bool optimizing){

        ast_manager &m = get_manager();
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(a.first, m) << std::endl;);
        for (int i = 0; i < elementNames.size(); ++i)
            STRACE("str", tout << "  " << mk_pp(elementNames[i].first, m););
        STRACE("str", tout <<  std::endl;);

        if (!length_base_split(a.first, elementNames)){
            return nullptr;
        }

        expr_ref_vector result(m);
        expr* extra_assert = nullptr;
        if (!const_vs_str_int(a.first, elementNames, extra_assert)) {
            result.push_back(extra_assert);
        }

        if (!not_contain_check(a.first, elementNames)){
            return nullptr;
        }

        if (a.second < 0 && !is_reg_union(a.first)) { /* const string or regex */
            /* check feasibility */
            if (a.second > REGEX_CODE) {
                zstring value;
                u.str.is_string(a.first, value);
                int max_lhs = value.length();
                int min_rhs = 0;
                for (unsigned i = 0; i < elementNames.size(); ++i) {
                    if (elementNames[i].second % p_bound.get_int64() == -1) {
                        u.str.is_string(elementNames[i].first, value);
                        if (p_bound.get_int64() == 2 && i + 1 < elementNames.size() && elementNames[i + 1].second % p_bound.get_int64() == 0)
                            min_rhs += value.length();
                        else if (p_bound.get_int64() == 1)
                            min_rhs += value.length();
                    }
                    else if (elementNames[i].second <= REGEX_CODE){
                    }
                }
                if (max_lhs < min_rhs) {
                    return nullptr;
                }
            }
            else {
                /* regex */
                // TODO: to be completed
            }

            /* collect */
            /* only handle the case of splitting const string into two parts*/
            expr_ref_vector adds(m);
            for (unsigned i = 0 ; i < elementNames.size(); ++i)
                if (elementNames[i].second <= REGEX_CODE) {
                    expr_ref tmp(getExprVarFlatSize(elementNames[i]), m);
                    adds.push_back(tmp.get());
                }
                else {
                    zstring tmpValue;
                    if (u.str.is_string(elementNames[i].first, tmpValue) && tmpValue.length() == 1)
                        adds.push_back(mk_int(1));
                    else
                        adds.push_back(createMultiplyOperator(getExprVarFlatSize(elementNames[i]),
                                                             getExprVarFlatIter(elementNames[i])));
                }
            expr_ref len_lhs(m);
            if (optimizing)
                result.push_back(createEqualOperator(getExprVarSize(a), createAddOperator(adds)));
            else
                result.push_back(createEqualOperator(getExprVarFlatSize(a), createAddOperator(adds)));

            int splitType = choose_split_type(elementNames, non_fresh_Variables, a.first);
            /*
             * 0: No const, No non_fresh_ var
             * 1: const		No non_fresh_ var
             * 2: no const, non_fresh_ var
             * 3: have both
             */
            STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(a.first, m) << std::endl;);
            std::vector<std::vector<int>> allPossibleSplits;
            expr_ref_vector strSplits(m);
            expr* reg = nullptr;
            switch (splitType) {
                case SIMPLE_CASE:
                    if (isInternalRegexVar(a.first, reg))
                        result.push_back(toConstraint_non_fresh_Var(
                                a, elementNames,
                                non_fresh_Variables,
                                optimizing,
                                pMax));
                    break;
                case NON_FRESH__ONLY:
                    /* handle non_fresh_ var */
                    result.push_back(toConstraint_non_fresh_Var(
                            a, elementNames,
                            non_fresh_Variables,
                            optimizing,
                            pMax));
                    break;
                case CONST_ONLY:
                    /* handle const */
                    allPossibleSplits = collectAllPossibleSplits(a, elementNames, optimizing);
                    for (unsigned i = 0; i < allPossibleSplits.size(); ++i) {
                        expr_ref_vector tmpp(m);
                        tmpp.append(toConstraint_Nonon_fresh_Var(a, elementNames, allPossibleSplits[i], optimizing));
                        strSplits.push_back(createAndOperator(tmpp));
                    }
                    if (strSplits.size() > 0)
                        result.push_back(createOrOperator(strSplits));
                    else
                        return nullptr;
                    break;

                case 3:
                    /* handle non_fresh_ var */
                    /* handle const */
                    allPossibleSplits = collectAllPossibleSplits(a, elementNames, optimizing);
                    for (unsigned i = 0; i < allPossibleSplits.size(); ++i) {
                        /* check feasibility */
                        strSplits.push_back(
                                toConstraint_havingnon_fresh_Var_andConst(
                                        a,
                                        elementNames,
                                        allPossibleSplits[i],
                                        non_fresh_Variables,
                                        optimizing,
                                        pMax));
                    }
                    if (strSplits.size() > 0)
                        result.push_back(createOrOperator(strSplits));
                    else
                        return nullptr;
                    break;
                default:
                    SASSERT (false);
                    break;
            }
        }

        else {
            STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(a.first, m) << std::endl;);

            /* do not need AND */
            /* result = sum (length) */
            expr_ref_vector adds(m);
            for (unsigned i = 0; i < elementNames.size(); ++i) {
                bool skip = false;
                if (i < elementNames.size() - 1) {
                    if (elementNames[i].first == elementNames[i + 1].first &&
                        ((elementNames[i].second >= 0 && elementNames[i].second + 1 == elementNames[i + 1].second) ||
                         (elementNames[i].second < 0 && elementNames[i].second - 1 == elementNames[i + 1].second))) {

                        if (elementNames[i].second < 0) {
                            zstring valueStr;
                            u.str.is_string(elementNames[i].first, valueStr);
                            adds.push_back(mk_int(valueStr.length()));
                        }
                        else {
                            adds.push_back(mk_strlen(elementNames[i].first));
                        }
                        ++i;
                        skip = true;
                    }
                }
                STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(a.first, m) << std::endl;);
                if (!skip) {
                    if (elementNames[i].second <= REGEX_CODE) {
                        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(elementNames[i].first, m) << std::endl;);
                        expr_ref tmp(getExprVarFlatSize(elementNames[i]), m);
                        adds.push_back(tmp);
                    }
                    else {
                        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(elementNames[i].first, m) << ", " << elementNames[i].second << std::endl;);
                        expr* flatsize = getExprVarFlatSize(elementNames[i]);
                        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(flatsize, m) << ", " << elementNames[i].second << std::endl;);
                        expr* flatiter = getExprVarFlatIter(elementNames[i]);
                        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(flatiter, m) << ", " << elementNames[i].second << std::endl;);
                        expr_ref tmp(createMultiplyOperator(getExprVarFlatSize(elementNames[i]),
                                                            getExprVarFlatIter(elementNames[i])), m);
                        adds.push_back(tmp);
                    }
                }

            }

            std::string tmpstr = (non_fresh_Variables.find(a.first) != non_fresh_Variables.end()) ? " non_fresh_" : " not non_fresh_";
            STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(a.first, m) << " " << tmpstr << std::endl;);
            expr_ref addexpr(createAddOperator(adds), m);
            if (optimizing)
                result.push_back(createEqualOperator(getExprVarSize(a), addexpr));
            else
                result.push_back(createEqualOperator(getExprVarFlatSize(a), addexpr));
            /* DO NOT care about empty flats or not*/

            /* handle const for non_fresh_ variables*/
            if (non_fresh_Variables.find(a.first) != non_fresh_Variables.end()) {
                expr* tmp = unroll_non_fresh_variable(
                        a, elementNames,
                        non_fresh_Variables, optimizing);
                result.push_back(tmp);
            }

            /* case 2 */
//            adds.reset();
//            expr_ref_vector ands(m);
//            for (const auto& s : elementNames){
//                ands.push_back(createEqualOperator(getExprVarFlatSize(a), getExprVarFlatSize(s))); /* size = size */
//                adds.push_back(getExprVarFlatIter(s)); /* iter = sum iter*/
//            }
//            ands.push_back(createEqualOperator(getExprVarFlatIter(a), createAddOperator(adds)));
        }

        expr_ref tmp(createAndOperator(result), m);
        return tmp.get();
    }

    bool theory_str::is_reg_union(expr* n){
        expr* reg = nullptr;
        if (isInternalRegexVar(n, reg)){
            std::vector<std::pair<int, int>> charRange = collectCharRange(reg);
            if (charRange.size() == 1 && charRange[0].first == -1){
                return false;
            }
            else
                return true;
        }
        return false;
    }

    /*
	 * Input: split a string
	 * Output: SMT
	 */
    expr* theory_str::toConstraint_havingnon_fresh_Var_andConst(
            std::pair<expr*, int> a, /* const || regex */
            std::vector<std::pair<expr*, int> > elementNames, /* const + non_fresh_ var */
            std::vector<int> split,
            std::map<expr*, int> non_fresh_Variables,
            bool optimizing,
            int pMax){
        ast_manager &m = get_manager();
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(a.first, m) << std::endl;);
        int totalLength = 0;
        for (unsigned j = 0; j < split.size(); ++j)
            if (split[j] > 0 && split[j] != MINUSZERO)
                totalLength = totalLength + split[j];
            else {
                totalLength = -1;
                break;
            }

        expr_ref_vector strAnd(m);
        expr* lhs_length = nullptr;
        if (optimizing)
            lhs_length = getExprVarSize(a);
        else
            lhs_length = getExprVarFlatSize(a);

        if (totalLength > 0) /* only has const, does not have regex */ {
            strAnd.push_back(createEqualOperator(lhs_length, m_autil.mk_int(totalLength)));
        }
        expr_ref_vector addElements(m);

        addElements.reset();
        unsigned splitPos = 0;

        zstring content;
        if (a.second <= REGEX_CODE)
            content = parse_regex_content(a.first);

        for (unsigned i = 0; i < elementNames.size(); ++i){
            if (elementNames[i].second >= 0) /* not const */ {
                addElements.push_back(createMultiplyOperator(getExprVarFlatSize(elementNames[i]),
                                                             getExprVarFlatIter(elementNames[i])));
                splitPos++;
            }
            else { /* const */
                if (addElements.size() > 0){ /* create a sum for previous elements */
                    splitPos--;
                    expr* constraintFornon_fresh_Var = lengthConstraint_tonon_fresh_VarConstraint(
                            a, /* const or regex */
                            elementNames, /* have non_fresh_ var */
                            addElements,
                            i - 1,
                            split[splitPos],
                            non_fresh_Variables,
                            optimizing,
                            pMax);
                    strAnd.push_back(constraintFornon_fresh_Var);
                    if (split[splitPos] == MINUSZERO) {
                        /* looping */
                        SASSERT(a.second <= REGEX_CODE);
                        strAnd.push_back(createEqualOperator(m_autil.mk_int(0), createModOperator(createAddOperator(addElements), m_autil.mk_int(content.length()))));
                    }
                    else if (split[splitPos] < 0) {
                        /* looping */
                        SASSERT(a.second <= REGEX_CODE);
                        strAnd.push_back(createEqualOperator(createModOperator(createAddOperator(addElements), m_autil.mk_int(content.length())),
                                                             m_autil.mk_int(std::abs(split[splitPos]))));
                    }
                    else {
                        strAnd.push_back(createEqualOperator(createAddOperator(addElements), m_autil.mk_int(split[splitPos])));
                    }
                    splitPos++;
                    addElements.reset();

                }
                zstring value;
                if (u.str.is_string(elementNames[i].first, value) && elementNames[i].second % p_bound.get_int64() == -1 && i < elementNames.size() - 1) {
                    if (p_bound.get_int64() == 1 || value.length() == 1) {
                        strAnd.push_back(createEqualOperator(getExprVarFlatSize(elementNames[i]), m_autil.mk_int(split[splitPos])));
                        splitPos++;
                    }
                    else {
                        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(elementNames[i].first, m) << " " << elementNames[i].second << mk_pp(elementNames[i + 1].first, m) << " " << elementNames[i + 1].second <<  std::endl;);
                        SASSERT(elementNames[i + 1].second % p_bound.get_int64() == 0);
                        strAnd.push_back(createEqualOperator(createAddOperator(getExprVarFlatSize(elementNames[i]), getExprVarFlatSize(elementNames[i + 1])),
                                m_autil.mk_int(split[splitPos] + split[splitPos + 1])));
                        i++;
                        splitPos += 2;
                    }
                }
                else {
                    if (split[splitPos] == MINUSZERO) {
                        /* looping at 0 */
                        SASSERT(elementNames[i].second <= REGEX_CODE);
                        SASSERT(a.second <= REGEX_CODE);
                        strAnd.push_back(createEqualOperator(
                                m_autil.mk_int(0),
                                createModOperator(getExprVarFlatSize(elementNames[i]), m_autil.mk_int(content.length()))));
                        splitPos++;
                    }
                    else if (split[splitPos] < 0) {
                        /* looping */
                        SASSERT(elementNames[i].second <= REGEX_CODE);
                        SASSERT(a.second <= REGEX_CODE);
                        strAnd.push_back(createEqualOperator(
                                createModOperator(getExprVarFlatSize(elementNames[i]), m_autil.mk_int(content.length())),
                                m_autil.mk_int(std::abs(split[splitPos++]))));
                    }
                    else {

                        if (is_regex_var(elementNames[i].first)){
                            expr_ref_vector tmp(m);
                            tmp.push_back(elementNames[i].first);
                            STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(elementNames[i].first, m) << std::endl;);
                            expr* constraintFornon_fresh_Var = lengthConstraint_tonon_fresh_VarConstraint(
                                    a, /* const or regex */
                                    elementNames, /* have non_fresh_ var */
                                    tmp,
                                    i,
                                    split[splitPos],
                                    non_fresh_Variables,
                                    optimizing,
                                    pMax);
                            strAnd.push_back(constraintFornon_fresh_Var);
                        }
                        strAnd.push_back(createEqualOperator(
                                getExprVarFlatSize(elementNames[i]),
                                m_autil.mk_int(split[splitPos++])));
                    }
                }
            }
        }

        if (addElements.size() > 0) {
            splitPos--;
            expr* constraintFornon_fresh_Var = lengthConstraint_tonon_fresh_VarConstraint(
                    a, /* const or regex */
                    elementNames, /* have non_fresh_ var */
                    addElements,
                    elementNames.size() - 1,
                    split[splitPos],
                    non_fresh_Variables,
                    optimizing,
                    pMax);
            strAnd.push_back(constraintFornon_fresh_Var);

            /* create a sum for previous elements */
            if (split[splitPos] == MINUSZERO) {
                /* looping */
                SASSERT(a.second <= REGEX_CODE);
                strAnd.push_back(createEqualOperator(
                        m_autil.mk_int(0),
                        createModOperator(createAddOperator(addElements), m_autil.mk_int(content.length()))));
            }
            else if (split[splitPos] < 0) {
                /* looping */
                SASSERT(a.second <= REGEX_CODE);
                strAnd.push_back(createEqualOperator(
                        createModOperator(createAddOperator(addElements), m_autil.mk_int(content.length())),
                        m_autil.mk_int(std::abs(split[splitPos]))));
            }
            else {
                strAnd.push_back(createEqualOperator(createAddOperator(addElements), m_autil.mk_int(split[splitPos])));
            }
            splitPos++;
        }
        SASSERT(splitPos == split.size());
        return createAndOperator(strAnd);
    }

    /*
	 *
	 */
    expr* theory_str::lengthConstraint_tonon_fresh_VarConstraint(
            std::pair<expr*, int> a, /* const || regex */
            std::vector<std::pair<expr*, int> > elementNames,
            expr_ref_vector subElements,
            int currentPos,
            int subLength,
            std::map<expr*, int> non_fresh_Variables,
            bool optimizing,
            int pMax){
        ast_manager &m = get_manager();

        expr_ref_vector constraints(m);
        expr* reg = nullptr;
        for (int i = currentPos - subElements.size() + 1; i <= currentPos; ++i) {
            if (non_fresh_Variables.find(elementNames[i].first) != non_fresh_Variables.end() ||
                isInternalRegexVar(elementNames[i].first, reg)) {
                constraints.push_back(non_fresh_Var_atSpecificLocation(
                        a, /* const or regex */
                        elementNames, /* have non_fresh_ var */
                        i,
                        subLength,
                        non_fresh_Variables,
                        optimizing,
                        pMax));
            }
        }
        return createAndOperator(constraints);

    }

    /*
	 *
	 */
    expr_ref theory_str::non_fresh_Var_atSpecificLocation(
            std::pair<expr*, int> a, /* const or regex */
            std::vector<std::pair<expr*, int>> elementNames, /* have non_fresh_ var */
            int non_fresh_VarPos,
            int non_fresh_VarLength,
            std::map<expr*, int> non_fresh_Variables,
            bool optimizing,
            int pMax){
        bool unrollMode = pMax == PMAX;

        ast_manager &m = get_manager();
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(a.first, m) << " "  << mk_pp(elementNames[non_fresh_VarPos].first, m) << " non_fresh_VarLength: "  << non_fresh_VarLength << std::endl;);
        expr_ref_vector resultParts(m);
        zstring content;
        if (a.second <= REGEX_CODE) {
            content = parse_regex_content(a.first);
            STRACE("str", tout << __LINE__ << " regex value: " << content << std::endl;);
        }
        else {
            u.str.is_string(a.first, content);
        }

        /* how many parts of that non_fresh_ variable are in the const | regex */
        /* sublen = part_1 + part2 + .. */
        int partCnt = 1;
        expr_ref subLen(m);
        if (!is_regex_var(elementNames[non_fresh_VarPos].first))
            subLen = find_partsOfnon_fresh_VariablesInAVector(non_fresh_VarPos, elementNames, partCnt);
        else {
            subLen = getExprVarFlatSize(elementNames[non_fresh_VarPos]);
        }
        expr* prefix_rhs = leng_prefix_rhs(elementNames[non_fresh_VarPos], unrollMode);
        expr* prefix_lhs = leng_prefix_lhs(a, elementNames, non_fresh_VarPos, optimizing, false);

        expr* arrayRhs = getExprVarFlatArray(elementNames[non_fresh_VarPos]);
        expr* arrayLhs = getExprVarFlatArray(a);
        if (non_fresh_VarLength >= 0 && non_fresh_VarLength != MINUSZERO) {
            /* sublen = non_fresh_VarLength */
            /* at_0 = x && at_1 == y && ..*/
            int considerLength = non_fresh_VarLength;
            expr* reg = nullptr;
            if (non_fresh_Variables[elementNames[non_fresh_VarPos].first] >= 0 &&
                    !isInternalRegexVar(elementNames[non_fresh_VarPos].first, reg))
                considerLength = std::min(non_fresh_Variables[elementNames[non_fresh_VarPos].first], considerLength);

            for (int k = 0; k < considerLength; ++k){
                expr* atRhs = createAddOperator(m_autil.mk_int(k), prefix_rhs);
                expr* regex = nullptr;
//                if (isInternalRegexVar(elementNames[non_fresh_VarPos].first, regex)) {
//                    if (u.re.is_plus(regex) || u.re.is_star(regex)) {
//                        atRhs = createModOperator(atRhs, m_autil.mk_int(
//                                non_fresh_Variables[elementNames[non_fresh_VarPos].first]));
//                    }
//                }
                resultParts.push_back(createEqualOperator(
                        createSelectOperator(arrayLhs, createAddOperator(m_autil.mk_int(k), prefix_lhs)),
                        createSelectOperator(arrayRhs, atRhs)));
            }
        }
        else {

            /* at_0 = x && at_1 == y && ..*/
            expr* len_non_fresh_Var = getExprVarFlatSize(elementNames[non_fresh_VarPos]);
            STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(len_non_fresh_Var, m) << std::endl;);
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
                STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: content : " << content << std::endl;);
                for (int i = 0; i < (int)content.length(); ++i){
                    expr_ref_vector ors(m);
                    expr* at = createAddOperator(m_autil.mk_int(i), prefix_lhs);
                    if (!u.str.is_string(a.first))
                        at = createModOperator(at, m_autil.mk_int(content.length()));
                    expr* eq01 = createEqualOperator(
                            createSelectOperator(arrayRhs, m_autil.mk_int(i)),
                            createSelectOperator(arrayLhs, at));
                    expr* less = createLessEqOperator(len_non_fresh_Var, m_autil.mk_int(i - 1));
                    ors.push_back(eq01);
                    ors.push_back(less);
                    resultParts.push_back(createOrOperator(ors));
                }
                resultParts.push_back(rewrite_implication(
                        createLessEqOperator(len_non_fresh_Var, m_autil.mk_int(content.length() - 1)),
                        createEqualOperator(getExprVarFlatIter(elementNames[non_fresh_VarPos]), m_autil.mk_int(1))));
            }
            else {
                expr* lenConstraint = createLessEqOperator(subLen, m_autil.mk_int(non_fresh_Variables[elementNames[non_fresh_VarPos].first]));
                resultParts.push_back(lenConstraint);

                for (int i = 0; i < std::min(non_fresh_Variables[elementNames[non_fresh_VarPos].first], std::min(connectingSize, 50)); ++i) {
                    expr_ref_vector ors(m);
                    expr* rhsSelect = createSelectOperator(arrayRhs, createAddOperator(m_autil.mk_int(i), prefix_rhs));
                    expr* at = createAddOperator(m_autil.mk_int(i), prefix_lhs);

                    if (!u.str.is_string(a.first))
                        at = createModOperator(at, m_autil.mk_int(content.length()));
                    expr* lhsSelect = createSelectOperator(arrayLhs, at);
                    expr* eq01 = createEqualOperator(
                            rhsSelect,
                            lhsSelect);
                    expr* less = createLessEqOperator(len_non_fresh_Var, m_autil.mk_int(i - 1));
                    ors.push_back(eq01);
                    ors.push_back(less);
                    resultParts.push_back(createOrOperator(ors));
                }
            }
#endif
        }

        expr_ref ret(createAndOperator(resultParts), m);
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(ret.get(), m) << std::endl;);
        return ret;
    }

    /*
	 * Input: split a string
	 * Output: SMT
	 */
    expr_ref_vector theory_str::toConstraint_Nonon_fresh_Var(
            std::pair<expr*, int> a, /* const || regex */
            std::vector<std::pair<expr*, int> > elementNames, /* no non_fresh_ var */
            std::vector<int> split,
            bool optimizing){
        STRACE("str", tout << __LINE__ <<  " const|regex = const + ..." << std::endl;);
        ast_manager &m = get_manager();
        int totalLength = 0;
        for (unsigned j = 0; j < split.size(); ++j)
            if (split[j] > 0 && split[j] != MINUSZERO)
                totalLength = totalLength + split[j];
            else {
                totalLength = -1;
                break;
            }

        expr_ref_vector strAnd(m);
        expr_ref lenLhs(m);
        if (optimizing)
            lenLhs = getExprVarSize(a);
        else
            lenLhs = getExprVarFlatSize(a);

        if (totalLength > 0) /* only has const, does not have regex */
            strAnd.push_back(createEqualOperator(lenLhs, m_autil.mk_int(totalLength)));

        expr_ref_vector addElements(m);

        /* simple case: check if size of all consts = 0 */
        bool sumConst_0 = true, metVar = false;
        unsigned splitPos = 0;
        for (unsigned i = 0; i < elementNames.size(); ++i) {
            zstring value;
            if (u.str.is_string(elementNames[i].first, value)) {
                if (value.length() == 1) {
                    sumConst_0 = false;
                    break;
                }
            }

            if (elementNames[i].second < 0) {
                if (metVar)
                    splitPos++;
                if (split[splitPos++] > 0){
                    sumConst_0 = false;
                    break;
                }
                addElements.push_back(createMultiplyOperator(
                        getExprVarFlatSize(elementNames[i]),
                        getExprVarFlatIter(elementNames[i])));
                metVar = false;
            }
            else
                metVar = true;
        }

        if (sumConst_0 == true) {
            STRACE("str", tout << __LINE__ <<  " const|regex = const + ...: short path" << std::endl;);
            strAnd.push_back(createEqualOperator(m_autil.mk_int(0), createAddOperator(addElements)));
            return strAnd;
        }

        /* work as usual */
        STRACE("str", tout << __LINE__ <<  " const|regex = const + ...: work as usual" << std::endl;);
        addElements.reset();
        splitPos = 0;
        zstring content;
        if (a.second <= REGEX_CODE)
            content = parse_regex_content(a.first);
        else
            u.str.is_string(a.first, content);

        for (unsigned i = 0; i < elementNames.size(); ++i){
            if (elementNames[i].second >= 0) /* not const */ {
                addElements.push_back(createMultiplyOperator(getExprVarFlatSize(elementNames[i]),
                                                             getExprVarFlatIter(elementNames[i])));

                splitPos++;
            }
            else { /* const */
                STRACE("str", tout << __LINE__ <<  " const|regex = const + ...: work as usual " << mk_pp(elementNames[i].first, m) << std::endl;);
                if (addElements.size() > 0){ /* create a sum for previous elements */
                    splitPos--;
                    if (split[splitPos] == MINUSZERO) {
                        /* looping */
                        SASSERT(a.second <= REGEX_CODE);
                        strAnd.push_back(createEqualOperator(m_autil.mk_int(0), createModOperator(createAddOperator(addElements), m_autil.mk_int(content.length()))));
                    }
                    else if (split[splitPos] < 0) {
                        /* looping */
                        SASSERT(a.second <= REGEX_CODE);
                        strAnd.push_back(createEqualOperator(createModOperator(createAddOperator(addElements), m_autil.mk_int(content.length())), m_autil.mk_int(std::abs(split[splitPos]))));
                    }
                    else {
                        strAnd.push_back(createEqualOperator(createAddOperator(addElements), m_autil.mk_int(split[splitPos])));
                    }

                    addElements.reset();
                    splitPos++;
                }

                STRACE("str", tout << __LINE__ <<  " const|regex = const + ...: work as usual" << std::endl;);
                if (elementNames[i].second % p_bound.get_int64() == -1 && i < elementNames.size() - 1 && elementNames[i].second > REGEX_CODE) {
                    zstring value;
                    u.str.is_string(elementNames[i].first, value);
                    if (p_bound.get_int64() == 1 || value.length() == 1) {
                        splitPos++;
                    }
                    else {
                        SASSERT(elementNames[i + 1].second % p_bound.get_int64() == 0);
                        i++;
                        splitPos += 2;
                    }
                }
                else {
                    STRACE("str", tout << __LINE__ <<  " const|regex = const + ...: work as usual" << std::endl;);
                    if (split[splitPos] == MINUSZERO) {
                        /* looping at 0 */
                        SASSERT(elementNames[i].second <= REGEX_CODE);
                        SASSERT(a.second <= REGEX_CODE);
                        strAnd.push_back(createEqualOperator(
                                m_autil.mk_int(0),
                                createModOperator(getExprVarFlatSize(elementNames[i]), m_autil.mk_int(content.length()))));
                        splitPos++;
                    }
                    else if (split[splitPos] < 0) {
                        /* looping */
                        SASSERT(elementNames[i].second <= REGEX_CODE);
                        SASSERT(a.second <= REGEX_CODE);
                        strAnd.push_back(createEqualOperator(
                                createModOperator(getExprVarFlatSize(elementNames[i]), m_autil.mk_int(content.length())),
                                m_autil.mk_int(std::abs(split[splitPos++]))));
                    }
                    else {
                        strAnd.push_back(createEqualOperator(getExprVarFlatSize(elementNames[i]),
                                                             m_autil.mk_int(split[splitPos++])));
                    }
                }
            }
        }

        if (addElements.size() > 0) {
            /* create a sum for previous elements */
            splitPos--;
            if (split[splitPos] == MINUSZERO) {
                /* looping */
                SASSERT(a.second <= REGEX_CODE);
                strAnd.push_back(createEqualOperator(m_autil.mk_int(0), createModOperator(createAddOperator(addElements), m_autil.mk_int(content.length()))));
            }
            else if (split[splitPos] < 0) {
                /* looping */
                SASSERT(a.second <= REGEX_CODE);
                strAnd.push_back(createEqualOperator(
                        createModOperator(createAddOperator(addElements), m_autil.mk_int(content.length())),
                        m_autil.mk_int(std::abs(split[splitPos]))));
            }
            else {
                strAnd.push_back(createEqualOperator(createAddOperator(addElements), m_autil.mk_int(split[splitPos])));
            }
            splitPos++;
        }

        expr_ref tmp(createAndOperator(strAnd), m);
        STRACE("str", tout << __LINE__ << " return *** " << __FUNCTION__ << " ***" << mk_pp(tmp, m) << std::endl;);
        return strAnd;
    }

    /*
	 *
	 */
    expr* theory_str::unroll_non_fresh_variable(
            std::pair<expr*, int> a, /* non_fresh_ variable */
            std::vector<std::pair<expr*, int> > elementNames, /* contain const */
            std::map<expr*, int> non_fresh_Variables,
            bool optimizing,
            int pMax){
        ast_manager &m = get_manager();
        STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " ***" << mk_pp(a.first, m) << std::endl;);
        /* (and ...) */

        expr_ref_vector possibleCases(m);

        for (unsigned i = 0 ; i < elementNames.size(); ++i){
            STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " *** " << mk_pp(elementNames[i].first, m) << ", " << elementNames[i].second << " " << elementNames[i].second % p_bound.get_int64() << std::endl;);
            if (elementNames[i].second < 0){ /* const || regex */
                /* |lhs| = 1 vs |rhs| = 1*/
                if (elementNames.size() == 1 && p_bound.get_int64() > 1) {
                    possibleCases.push_back(
                            handle_SubConst_WithPosition_array(
                                    a, elementNames,
                                    i,
                                    optimizing,
                                    pMax));
                }
                else if (elementNames[i].second <= REGEX_CODE) {
                    STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " ***"  << std::endl;);
                    expr_ref e(handle_SubConst_WithPosition_array(
                            a, elementNames,
                            i,
                            optimizing,
                            pMax), m);
                    possibleCases.push_back(e);
                    STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " ***" << mk_pp(e.get(), m) << std::endl;);
                }
                    /* tail of string, head of elements*/
                else if (i == 0 && elementNames[i].second % p_bound.get_int64() == 0 && p_bound.get_int64() > 1) {
                    possibleCases.push_back(handle_SubConst_WithPosition_array(
                            a, elementNames,
                            i,
                            optimizing,
                            pMax));
                }
                    /* head of string, tail of elements */
                else if (i == elementNames.size() - 1 && elementNames[i].second % p_bound.get_int64() == -1 && p_bound.get_int64() > 1)  {
                    possibleCases.push_back(handle_SubConst_WithPosition_array(
                            a, elementNames,
                            i,
                            optimizing,
                            pMax));
                }
                    /* only care about first element */
                else if (elementNames[i].second % p_bound.get_int64() == -1)  {
                    STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " ***"  << std::endl;);
                    zstring value;
                    u.str.is_string(elementNames[i].first, value);
                    possibleCases.push_back(
                            handle_Const_WithPosition_array(
                                    a, elementNames,
                                    i, value, 0,
                                    value.length(),
                                    optimizing,
                                    pMax));
                }
            }
            else if (elementNames[i].second >= 0 &&
                     non_fresh_Variables.find(elementNames[i].first) != non_fresh_Variables.end()){
                if (elementNames[i].second % p_bound.get_int64() == 1 && i > 0)
                    continue;
                int bound = std::max(non_fresh_Variables[elementNames[i].first], non_fresh_Variables[a.first]);
                if (bound >= connectingSize)
                    bound = std::min(non_fresh_Variables[elementNames[i].first], non_fresh_Variables[a.first]);
                possibleCases.push_back(
                        handle_non_fresh__non_fresh__array(
                                a, elementNames, i,
                                std::min(non_fresh_Variables[elementNames[i].first], non_fresh_Variables[a.first]),
                                optimizing,
                                pMax));

            }
        }

        STRACE("str", tout << __LINE__ << " return *** " << __FUNCTION__ << " ***" << std::endl;);
        expr_ref ret(createAndOperator(possibleCases), m);
        return ret.get();
    }

    /*
	 * Generate constraints for the case
	 * X = T . "abc" . Y . Z
	 * constPos: position of const element
	 * return: (or (and length header = i && X_i = a && X_[i+1] = b && X_[i+2] = c))
	 */
    expr_ref theory_str::handle_SubConst_WithPosition_array(
            std::pair<expr*, int> a, // non_fresh_ var
            std::vector<std::pair<expr*, int>> elementNames,
            int constPos,
            bool optimizing,
            int pMax) {
        ast_manager &m = get_manager();
        STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " ***" << mk_pp(a.first, m) << std::endl;);
        SASSERT (elementNames[constPos].second < 0);
        bool unrollMode = pMax == PMAX;

        /* regex */
        zstring content;
        if (elementNames[constPos].second > REGEX_CODE)
            u.str.is_string(elementNames[constPos].first, content);
        else
            content = "";

        expr_ref startPos(leng_prefix_lhs(a, elementNames, constPos, optimizing, unrollMode), m);
        expr_ref flatArrayName(getExprVarFlatArray(a), m);

        expr_ref_vector possibleCases(m);
        if (elementNames[constPos].second <= REGEX_CODE && !u.re.is_union(elementNames[constPos].first)) {
            possibleCases.push_back(
                    handle_Regex_WithPosition_array(
                            a, elementNames,
                            constPos,
                            optimizing,
                            pMax));
        }
        else {
            STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " ***" << mk_pp(a.first, m) << std::endl;);
            std::vector<zstring> components = {content};
            if (u.re.is_union(elementNames[constPos].first)) {
                components.clear();
                collect_alternative_components(elementNames[constPos].first, components);
            }

            STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " ***" << mk_pp(a.first, m) << std::endl;);

            bool is_str_int = false;
            if (string_int_vars.find(a.first) != string_int_vars.end()){
                is_str_int = true;
            }

            for (const auto& v : components) {
                if (elementNames[constPos].second % p_bound.get_int64() == -1 || elementNames[constPos].second <= REGEX_CODE) {
                    STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " ***" << mk_pp(a.first, m) << std::endl;);
                    /* head of const */
                    expr_ref_vector oneCase(m);
                    if (components.size() != 1)
                        for (int i = 1; i <= std::min(LOCALSPLITMAX, (int)v.length()); ++i) {
                            expr_ref_vector locationConstraint(m);
                            /*length = i*/
                            locationConstraint.push_back(
                                    createLessEqOperator(
                                            getExprVarFlatSize(elementNames[constPos]),
                                            m_autil.mk_int(i - 1)));
                            unrollMode ?
                            locationConstraint.push_back(
                                    createEqualOperator(
                                            createSelectOperator(flatArrayName, createAddOperator(m_autil.mk_int(i - 1), startPos)),
                                            m_autil.mk_int(v[i - 1]))) /* arr value */
                                       :
                            locationConstraint.push_back(
                                    createEqualOperator(
                                            createSelectOperator(flatArrayName,
                                                                   createModOperator(
                                                                           createAddOperator(m_autil.mk_int(i - 1), startPos),
                                                                           m_autil.mk_int(pMax))),
                                            m_autil.mk_int(v[i - 1])));
                            oneCase.push_back(createOrOperator(locationConstraint));
                        }
                    else
                        for (int i = 1; i <= std::min(LOCALSPLITMAX, (int)v.length()); ++i) {
                            if (is_str_int && (v[i - 1] < '0' || v[i - 1] > '9')) {
                                oneCase.reset();
                                break;
                            }
                            expr_ref_vector locationConstraint(m);
                            /*length = i*/
                            locationConstraint.push_back(
                                    createLessEqOperator(getExprVarFlatSize(elementNames[constPos]),
                                                         m_autil.mk_int(i - 1)));
                            unrollMode ?
                            locationConstraint.push_back(
                                    createEqualOperator(
                                            createSelectOperator(flatArrayName, createAddOperator(m_autil.mk_int(i - 1), startPos)),
                                            m_autil.mk_int(v[i - 1]))) /* direct value */
                                       :
                            locationConstraint.push_back(
                                    createEqualOperator(
                                            createSelectOperator(flatArrayName,
                                                                   createModOperator(
                                                                           createAddOperator(m_autil.mk_int(i - 1), startPos),
                                                                           m_autil.mk_int(pMax))),
                                            m_autil.mk_int(v[i - 1]))) /* direct value */;

                            oneCase.push_back(createOrOperator(locationConstraint));
                        }
                    possibleCases.push_back(createAndOperator(oneCase));
                }
                else {
                    for (int i = 0; i <= std::min(LOCALSPLITMAX, (int)v.length()); ++i) {
                        /* length = i */
                        expr_ref tmp(createEqualOperator(getExprVarFlatSize(elementNames[constPos]),
                                                                m_autil.mk_int(v.length() - i)), m);
                        possibleCases.push_back(
                                handle_Const_WithPosition_array(
                                        a, elementNames,
                                        constPos, v, i, v.length(),
                                        optimizing,
                                        pMax,
                                        tmp));
                    }
                }
                STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " ***" << mk_pp(a.first, m) << std::endl;);
            }
        }

        expr_ref ret(createOrOperator(possibleCases), m);
        return ret;
    }

    /*
	 * non_fresh_ = a + non_fresh_ + b
	 */
    expr* theory_str::handle_non_fresh__non_fresh__array(
            std::pair<expr*, int> a,
            std::vector<std::pair<expr*, int>> elementNames,
            int pos,
            int bound,
            bool optimizing,
            int pMax){

        ast_manager &m = get_manager();
        STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " ***: " << mk_pp(a.first, m) << std::endl;);
        bool unrollMode = pMax == PMAX;

        /* find the start position --> */
        expr_ref startLhs(leng_prefix_lhs(a, elementNames, pos, optimizing, unrollMode), m);
        expr_ref startRhs(leng_prefix_rhs(elementNames[pos], unrollMode), m);
        /* optimize length of generated string */
        expr* arrLhs = getExprVarFlatArray(a);
        expr* arrRhs = getExprVarFlatArray(elementNames[pos]);

        expr* lenA = getExprVarFlatSize(a);
        expr* lenB = getExprVarFlatSize(elementNames[pos]);

        expr* iterB = getExprVarFlatIter(elementNames[pos]);

        expr_ref_vector andConstraints(m);
        expr* lenRhs = nullptr;
        /* combine two parts if it is possible */
        bool can_combine = false;
        if (elementNames[pos].second % p_bound.get_int64() == 0 &&
            pos < (int)elementNames.size() - 1 &&
                p_bound.get_int64() > 1 && elementNames[pos].second >= 0) {
            SASSERT(elementNames[pos + 1].second % p_bound.get_int64() == 1);
            SASSERT(p_bound.get_int64() == 2);
            lenRhs = getExprVarSize(elementNames[pos]);
            can_combine = true;
        }
        else {
            lenRhs = getExprVarFlatSize(elementNames[pos]);
            can_combine = false;
        }

        expr* lenLhs = nullptr;
        if (optimizing)
            lenLhs = getExprVarSize(a);
        else
            lenLhs = getExprVarFlatSize(a);


        STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " ***: " << mk_pp(a.first, m) << std::endl;);
        if (!unrollMode){
            for (int i = 1; i <= pMax; ++i){
                expr_ref_vector orConstraints(m);
                orConstraints.push_back(
                        createEqualOperator(
                                createSelectOperator(arrLhs,
                                                       createModOperator(
                                                               createAddOperator(m_autil.mk_int(i - 1), startLhs),
                                                               m_autil.mk_int(pMax))),

                                createSelectOperator(arrRhs,
                                                       createModOperator(
                                                               createAddOperator(m_autil.mk_int(i - 1), startRhs),
                                                               m_autil.mk_int(pMax)))));

                orConstraints.push_back(createLessEqOperator(lenRhs, m_autil.mk_int(i - 1)));
                andConstraints.push_back(createOrOperator(orConstraints));
            }

            andConstraints.push_back(
                    rewrite_implication(
                            createLessOperator(lenB, lenA),
                            createEqualOperator(iterB, m_autil.mk_int(1))));
        }
        else {
            int consideredSize = bound;
            STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " ***: " << mk_pp(a.first, m) << "; size: " << consideredSize << std::endl;);
            STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " ***: " << mk_pp(a.first, m) << "; connectingSize size: " << connectingSize << std::endl;);
            if (!flat_enabled) {
                for (int i = 1; i <= consideredSize; ++i) {
                    expr_ref_vector orConstraints(m);
                    orConstraints.push_back(createEqualOperator(
                            createSelectOperator(arrLhs, createAddOperator(m_autil.mk_int(i - 1), startLhs)),
                            createSelectOperator(arrRhs, createAddOperator(m_autil.mk_int(i - 1), startRhs))));
                    orConstraints.push_back(createLessEqOperator(lenRhs, m_autil.mk_int(i - 1)));
                    andConstraints.push_back(createOrOperator(orConstraints));
                }


                STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " ***: " << consideredSize
                                   << "; connectingSize size: " << connectingSize << std::endl;);
                if (consideredSize >= connectingSize) {
                    andConstraints.push_back(createLessEqOperator(lenRhs, mk_int(connectingSize)));
                    andConstraints.push_back(createLessEqOperator(lenLhs, mk_int(connectingSize)));
                }
            }
            else {
                if (optimizing) {
                    if (can_combine && elementNames.size() == p_bound.get_int64()) {
                        andConstraints.push_back(generate_constraint_var_var(a, elementNames[0], pMax, q_bound));
                    }
                    else {
                        if (can_combine) {
                            NOT_IMPLEMENTED_YET();
                        }
                        else
                            NOT_IMPLEMENTED_YET();
                    }
                }
                else {
                    if (can_combine) {
                        andConstraints.push_back(generate_constraint_flat_var(a, elementNames, pos, pMax, q_bound));
                    }
                    else
                        andConstraints.push_back(generate_constraint_flat_flat(a, elementNames, pos, pMax, q_bound));
                }

            }
        }
        STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " ***: " << mk_pp(createAndOperator(andConstraints), m) << std::endl;);
        return createAndOperator(andConstraints);
    }

    /*
	 * Generate constraints for the case
	 * X = T . "abc"* . Y . Z
	 * regexPos: position of regex element
	 * return: forAll (i Int) and (i < |abc*|) (y[i + |T|] == a | b | c)
	 */
    expr_ref theory_str::handle_Regex_WithPosition_array(
            std::pair<expr*, int> a, // non_fresh_ var
            std::vector<std::pair<expr*, int>> elementNames,
            int regexPos,
            bool optimizing,
            int pMax,
            expr* extraConstraint /* length = ? */
    ) {
        ast_manager &m = get_manager();
        STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " ***" << mk_pp(a.first, m) << std::endl;);

        SASSERT (elementNames[regexPos].second <= REGEX_CODE);
        bool unrollMode = pMax == PMAX;

        expr_ref_vector locationConstraint(m);
        if (extraConstraint != nullptr)
            locationConstraint.push_back(extraConstraint);

        /* find the start position --> */
        expr* pre_lhs = leng_prefix_lhs(a, elementNames, regexPos, optimizing, unrollMode);

        /* optimize length of generated string */
        expr* lhs_array = getExprVarFlatArray(a);

        expr* regex_length = getExprVarFlatSize(elementNames[regexPos]);


#if 0
        char strTmp[5000];
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
        expr_ref_vector andConstraints(m);
        andConstraints.push_back(createLessEqOperator(regex_length, m_autil.mk_int(connectingSize)));
        STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " ***" << mk_pp(a.first, m) << std::endl;);
        std::vector<std::pair<int, int>> charRange = collectCharRange(elementNames[regexPos].first);

        STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " ***" << charRange[0].first << std::endl;);
        if (charRange[0].first != -1) {
            if (!unrollMode) {
                for (int i = 0; i < pMax; ++i) {
                    expr_ref_vector ors(m);
                    expr_ref_vector ors_range(m);
                    for (int j = 0; j < charRange.size(); ++j) {
                        expr_ref_vector ands(m);
                        ands.push_back(createGreaterEqOperator(
                                createSelectOperator(lhs_array, createAddOperator(m_autil.mk_int(i), pre_lhs)),
                                m_autil.mk_int(charRange[j].first)));
                        ands.push_back(createLessEqOperator(
                                createSelectOperator(lhs_array, createAddOperator(m_autil.mk_int(i), pre_lhs)),
                                m_autil.mk_int(charRange[j].second)));
                        ors_range.push_back(createAndOperator(ands));
                    }

                    ors.push_back(createOrOperator(ors_range));
                    ors.push_back(createGreaterOperator(m_autil.mk_int(i + 1), getExprVarFlatSize(elementNames[regexPos])));
                    andConstraints.push_back(createOrOperator(ors));
                }
            }
            else {
                STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " ***" << std::endl;);
                int bound = std::min(connectingSize, 50);
                if (flat_enabled)
                    bound = q_bound.get_int64();
                for (int i = 0; i < bound; ++i) {
                    expr_ref_vector ors(m);
                    expr_ref_vector ors_range(m);
                    for (int j = 0; j < charRange.size(); ++j) {
                        expr_ref_vector ands(m);
                        ands.push_back(createGreaterEqOperator(
                                createSelectOperator(lhs_array, createAddOperator(m_autil.mk_int(i), pre_lhs)),
                                m_autil.mk_int(charRange[j].first)));
                        ands.push_back(createLessEqOperator(
                                createSelectOperator(lhs_array, createAddOperator(m_autil.mk_int(i), pre_lhs)),
                                m_autil.mk_int(charRange[j].second)));
                        ors_range.push_back(createAndOperator(ands));
                    }
                    ors.push_back(createOrOperator(ors_range));
                    ors.push_back(createGreaterOperator(m_autil.mk_int(i + 1), getExprVarFlatSize(elementNames[regexPos])));
                    andConstraints.push_back(createOrOperator(ors));
                }
            }
        }
        else {
            zstring strTmp = parse_regex_content(elementNames[regexPos].first);
            unsigned tmpNum = strTmp.length();
            if (strTmp.length() == 0) {
                expr_ref tmp(m.mk_true(), m);
                return tmp;
            }

            if (!unrollMode){
                for (int i = 0; i < pMax; ++i) {
                    expr_ref_vector ors(m);
                    ors.push_back(createEqualOperator(createSelectOperator(lhs_array, createAddOperator(m_autil.mk_int(i), pre_lhs)),
                                                      mk_int(strTmp[i % tmpNum])));
                    ors.push_back(createGreaterOperator(m_autil.mk_int(i + 1), getExprVarFlatSize(elementNames[regexPos])));
                    andConstraints.push_back(createOrOperator(ors));
                }
            }
            else {
                STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " ***" << strTmp << std::endl;);
                for (int i = 0; i < std::min(connectingSize, 50); ++i) {
                    expr_ref_vector ors(m);
                    ors.push_back(createEqualOperator(createSelectOperator(lhs_array, createAddOperator(m_autil.mk_int(i), pre_lhs)),
                            mk_int(strTmp[i % tmpNum])));
                    ors.push_back(createGreaterOperator(m_autil.mk_int(i + 1), getExprVarFlatSize(elementNames[regexPos])));
                    andConstraints.push_back(createOrOperator(ors));
                }
            }
        }

        expr_ref ret(createAndOperator(andConstraints), m);
        return ret;
#endif
    };

    /*
	 * Generate constraints for the case
	 * X = T . "abc" . Y . Z
	 * constPos: position of const element
	 * return: (or (and length header = i && X_i = a && X_[i+1] = b && X_[i+2] = c))
	 */
    expr_ref theory_str::handle_Const_WithPosition_array(
            std::pair<expr*, int> a,
            std::vector<std::pair<expr*, int>> elementNames,
            int constPos,
            zstring value, /* value of regex */
            int start, int finish,
            bool optimizing,
            int pMax,
            expr* extraConstraint /* length = ? */) {
        ast_manager &m = get_manager();
        STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " ***"  << std::endl;);
        SASSERT (elementNames[constPos].second < 0);
        bool unrollMode = pMax == PMAX;
        expr_ref_vector locationConstraint(m);
        if (extraConstraint != nullptr)
            locationConstraint.push_back(extraConstraint);

        /* find the start position --> */
        expr_ref startPos(leng_prefix_lhs(a, elementNames, constPos, optimizing, unrollMode), m);

        /* optimize length of generated string */
        expr_ref tmp01(getExprVarFlatArray(a), m);
        expr_ref tmp02(getExprVarFlatArray(elementNames[constPos]), m);

        std::vector<zstring> components = {value};
        if (u.re.is_union(elementNames[constPos].first)) {
            components.clear();
            collect_alternative_components(elementNames[constPos].first, components);
        }

        expr_ref_vector orConstraints(m);
        bool is_str_int = false;
        if (string_int_vars.find(a.first) != string_int_vars.end())
            is_str_int = true;
        for (const auto &v : components) {
            if (components.size() != 1)
                for (int i = start; i < finish; ++i) {
                    unrollMode ?
                    locationConstraint.push_back(createEqualOperator(
                            createSelectOperator(tmp01,
                                                 createAddOperator(m_autil.mk_int(i - start), startPos)),
                            createSelectOperator(tmp02, m_autil.mk_int(i))))
                               :
                    locationConstraint.push_back(createEqualOperator(
                            createSelectOperator(tmp01,
                                                 createModOperator(
                                                         createAddOperator(m_autil.mk_int(i - start), startPos),
                                                         m_autil.mk_int(pMax))),
                            createSelectOperator(tmp02, m_autil.mk_int(i))));
                }
            else
                for (int i = start; i < finish; ++i) {
                    if (is_str_int && (v[i] < '0' || v[i] > '9')) {
                        locationConstraint.reset();
                        break;
                    }
                    unrollMode ?
                    locationConstraint.push_back(createEqualOperator(
                            createSelectOperator(tmp01,
                                                 createAddOperator(m_autil.mk_int(i - start), startPos)),
                            m_autil.mk_int(v[i]))) :
                    locationConstraint.push_back(createEqualOperator(
                            createSelectOperator(tmp01,
                                                 createModOperator(
                                                         createAddOperator(m_autil.mk_int(i - start), startPos),
                                                         m_autil.mk_int(pMax))),
                            m_autil.mk_int(v[i])));
                }
            orConstraints.push_back(createAndOperator(locationConstraint));
        }

        expr_ref ret(createOrOperator(orConstraints), m);
        STRACE("str", tout << __LINE__ << " return *** " << __FUNCTION__ << " ***" << mk_pp(ret.get(), m) << std::endl;);
        return ret;
    }

    /*
	 *
	 */
    expr* theory_str::toConstraint_non_fresh_Var(
            std::pair<expr*, int> a, /* const or regex */
            std::vector<std::pair<expr*, int>> elementNames, /* have non_fresh_ var, do not have const */
            std::map<expr*, int> non_fresh_Variables,
            bool optimizing,
            int pMax){
        ast_manager &m = get_manager();
        STRACE("str", tout << __LINE__ << " const|regex = non_fresh_ var + ..." << std::endl;);
        expr_ref arrayLhs(getExprVarFlatArray(a), m);
        expr_ref_vector resultParts(m);

        zstring content;
        if (a.second <= REGEX_CODE) {
            content = parse_regex_content(a.first);
        }
        else
            u.str.is_string(a.first, content);

        bool unrollMode = PMAX == pMax;
        for (unsigned i = 0; i < elementNames.size(); ++i){
            if (elementNames[i].second >= 0) /* not const */ {

                /* non_fresh_ variable */
                if (non_fresh_Variables.find(elementNames[i].first) != non_fresh_Variables.end()) {
                    STRACE("str", tout << __LINE__ << " const|regex = non_fresh_ var + ..." << std::endl;);
                    /* sublen = part_1 + part2 + .. */
                    int partCnt = 1;
                    expr_ref subLen(find_partsOfnon_fresh_VariablesInAVector(i, elementNames, partCnt), m);

                    expr_ref prefix_rhs(leng_prefix_rhs(elementNames[i], unrollMode), m);
                    expr_ref prefix_lhs(leng_prefix_lhs(a, elementNames, i, optimizing, false), m);

                    if (a.second == REGEX_CODE) {
                        if (content.length() == 0)
                            continue;
                        STRACE("str", tout << __LINE__ << " const|regex = non_fresh_; content = " << content << std::endl;);
                        expr_ref_vector conditions(m);
                        if (partCnt == 1) {
                            STRACE("str", tout << __LINE__ << " const|regex = non_fresh_ var partCnt = 1. NOT TESTED" << std::endl;);
                            /* this part = regex */
                            /* prefix mod lenth = 0 */
                            if (content != zstring("uNkNoWn")) {
                                conditions.push_back(createEqualOperator(m_autil.mk_int(0),
                                                                         createModOperator(prefix_rhs, m_autil.mk_int(
                                                                                 content.length()))));
                                conditions.push_back(createEqualOperator(m_autil.mk_int(0), createModOperator(subLen,
                                                                                                              m_autil.mk_int(
                                                                                                                      content.length()))));

#if 0
                                std::string partArray = generateFlatArray_forComponent(elementNames[i], rhs);
                                for (unsigned int j = 0; j < content.length(); ++j)
                                    subcase.emplace_back(createEqualConstraint(createSelectConstraint(partArray, std::to_string(j)), std::to_string(content[j])));

#else
                                expr_ref arrName(getExprVarFlatArray(elementNames[i]), m);
                                expr_ref prefix(leng_prefix_rhs(elementNames[i], unrollMode), m);

                                expr_ref_vector cases(m);
                                for (unsigned iter = 0; iter < connectingSize / content.length(); ++iter) {
                                    expr_ref_vector subcase(m);
                                    subcase.push_back(
                                            createEqualOperator(subLen, m_autil.mk_int(iter * content.length())));
                                    for (unsigned j = 0; j < iter * content.length(); ++j) {
                                        subcase.push_back(createEqualOperator(createSelectOperator(arrName,
                                                                                                   createAddOperator(
                                                                                                           prefix,
                                                                                                           m_autil.mk_int(
                                                                                                                   j))),
                                                                              m_autil.mk_int(
                                                                                      content[j % content.length()])));
                                    }
                                    cases.push_back(createAndOperator(subcase));
                                }
                                conditions.push_back(createOrOperator(cases));
#endif
                                resultParts.push_back(createAndOperator(conditions));
                            }
                            else {
                                expr* to_assert = generate_constraint_flat_flat(a, elementNames, i, pMax, q_bound);
                                resultParts.push_back(to_assert);
                            }
                        }
                        else {
                            STRACE("str", tout << __LINE__ << " const|regex = non_fresh_ var partCnt = 2." << std::endl;);
                            SASSERT(partCnt == 2);
                            if (content != zstring("uNkNoWn")) {
                                /* this part = regex */
                                /* prefix mod length = 0 */
                                conditions.push_back(createEqualOperator(m_autil.mk_int(0),
                                                                         createModOperator(prefix_rhs, m_autil.mk_int(
                                                                                 content.length()))));
                                conditions.push_back(createEqualOperator(m_autil.mk_int(0), createModOperator(subLen,
                                                                                                              m_autil.mk_int(
                                                                                                                      content.length()))));

                                expr_ref arrName(getExprVarFlatArray(elementNames[i]), m);
                                for (unsigned iter = 0; iter < connectingSize / content.length(); ++iter) {
                                    for (unsigned j = 0; j < content.length(); ++j)
                                        conditions.push_back(createEqualOperator(createSelectOperator(arrName,
                                                                                                      m_autil.mk_int(j +
                                                                                                                     iter *
                                                                                                                     content.length())),
                                                                                 m_autil.mk_int(content[j])));
                                }
                                resultParts.push_back(createAndOperator(conditions));
                            }
                            else {
                                expr* to_assert = generate_constraint_flat_flat(a, elementNames, i, pMax, q_bound);
                                resultParts.push_back(to_assert);
                                to_assert = generate_constraint_flat_flat(a, elementNames, i + 1, pMax, q_bound);
                                resultParts.push_back(to_assert);
                            }
                        }
                    }
                    else {
                        expr_ref arrayRhs(getExprVarFlatArray(elementNames[i]), m);

                        if (p_bound.get_int64() == 1) {
                            resultParts.push_back(createEqualOperator(subLen, m_autil.mk_int(content.length())));
                            for (unsigned k = 0; k < content.length(); ++k){
                                expr* at = createAddOperator(m_autil.mk_int(k), prefix_lhs);

                                resultParts.push_back(createEqualOperator(
                                        createSelectOperator(arrayLhs, at),
                                        createSelectOperator(arrayRhs, createAddOperator(m_autil.mk_int(k), prefix_rhs))));
                            }
                        }
                        else {

                            STRACE("str", tout << __LINE__ << " const|regex = non_fresh_ var + ...: " << content << " " << mk_pp(subLen, m) << std::endl;);
                            int localSplit = non_fresh_Variables[elementNames[i].first];
                            expr_ref_vector possibleCases(m); /* sublen = 0 || sublen = 1 || .. */
                            if (!unrollMode) {
                                STRACE("str", tout << __LINE__ << " const|regex = non_fresh_ var + ..." << std::endl;);
                                for (int j = 0; j <= std::min(localSplit, (int)content.length()); j++){
                                    expr_ref_vector subpossibleCases(m); /*at_0 = x && at_1 == y && ..*/
                                    subpossibleCases.push_back(createEqualOperator(subLen, m_autil.mk_int(j)));
                                    for (int k = 0; k < j; ++k){
                                        subpossibleCases.push_back(createEqualOperator(
                                                createSelectOperator(arrayLhs, createAddOperator(m_autil.mk_int(k), prefix_lhs)),
                                                createSelectOperator(arrayRhs, createModOperator(createAddOperator(m_autil.mk_int(k), prefix_rhs), m_autil.mk_int(pMax))
                                                )));
                                    }
                                    possibleCases.push_back(createAndOperator(subpossibleCases));
                                }
                            }
                            else {
                                if (content != zstring("uNkNoWn")) {
                                    for (int j = 0; j <= std::min(localSplit, (int) content.length()); j++) {
                                        expr_ref_vector subpossibleCases(m); /*at_0 = x && at_1 == y && ..*/
                                        subpossibleCases.push_back(createEqualOperator(subLen, m_autil.mk_int(j)));
                                        for (int k = 0; k < j; ++k) {
                                            expr *at = createAddOperator(m_autil.mk_int(k), prefix_lhs);
                                            rational atValue;
                                            expr *lhsExpr = nullptr;
                                            if (!m_autil.is_numeral(at, atValue))
                                                lhsExpr = createSelectOperator(arrayLhs, at);
                                            else {
                                                if (is_str_int_var(elementNames[i].first) &&
                                                    (content[atValue.get_int64()] < '0' ||
                                                     content[atValue.get_int64()] > '9')) {
                                                    STRACE("str", tout << __LINE__ << " break because of str-int"
                                                            << std::endl;);
                                                    subpossibleCases.reset();
                                                    break;
                                                }
                                                lhsExpr = mk_int(content[atValue.get_int64()]);
                                            }

                                            subpossibleCases.push_back(createEqualOperator(
                                                    lhsExpr,
                                                    createSelectOperator(arrayRhs, createAddOperator(m_autil.mk_int(k),
                                                                                                     prefix_rhs))));
                                        }
                                        if (subpossibleCases.size() > 0)
                                            possibleCases.push_back(createAndOperator(subpossibleCases));
                                    }
                                    STRACE("str", tout << __LINE__ << " "
                                                       << std::endl;);
                                    if (is_str_int_var(elementNames[i].first)) {
                                        // must be 0
                                        for (int j = std::min(localSplit, (int) content.length()) + 1;
                                             j < (int) content.length(); ++j) {
                                            STRACE("str", tout << __LINE__ << " "
                                                               << std::endl;);
                                            expr_ref_vector subpossibleCases(m); /*at_0 = x && at_1 == y && ..*/
                                            subpossibleCases.push_back(createEqualOperator(subLen, m_autil.mk_int(j)));

                                            // zero part: [0, j - bound)
                                            for (int k = 0; k < j - str_int_bound.get_int64(); ++k) {
                                                STRACE("str", tout << __LINE__ << " "
                                                                   << std::endl;);
                                                expr *at = createAddOperator(m_autil.mk_int(k), prefix_lhs);
                                                rational atValue;
                                                expr *lhsExpr = nullptr;
                                                if (!m_autil.is_numeral(at, atValue))
                                                    lhsExpr = createSelectOperator(arrayLhs, at);
                                                else {
                                                    if (content[atValue.get_int64()] != '0') {
                                                        STRACE("str", tout << __LINE__
                                                                           << " break because of str-int: first part = 0"
                                                                           << std::endl;);
                                                        subpossibleCases.reset();
                                                        break;
                                                    }
                                                    lhsExpr = mk_int(content[atValue.get_int64()]);
                                                }

                                                subpossibleCases.push_back(createEqualOperator(
                                                        lhsExpr,
                                                        createSelectOperator(arrayRhs,
                                                                             createAddOperator(m_autil.mk_int(k),
                                                                                               prefix_rhs))));
                                                subpossibleCases.push_back(createEqualOperator(
                                                        lhsExpr,
                                                        mk_int('0')));
                                            }
                                            STRACE("str", tout << __LINE__ << " "
                                                               << std::endl;);
                                            if (subpossibleCases.size() == 0)
                                                break;
                                            STRACE("str", tout << __LINE__ << " " << content
                                                               << std::endl;);
                                            // bounded part [j - bound, j)
                                            int start_pos = 0;
                                            if (j - str_int_bound.get_int64() > 0)
                                                start_pos = j - str_int_bound.get_int64();
                                            for (int k = start_pos; k < j; ++k) {
                                                STRACE("str", tout << __LINE__ << " "
                                                                   << std::endl;);
                                                expr *at = createAddOperator(m_autil.mk_int(k), prefix_lhs);
                                                rational atValue;
                                                expr *lhsExpr = nullptr;
                                                if (!m_autil.is_numeral(at, atValue))
                                                    lhsExpr = createSelectOperator(arrayLhs, at);
                                                else {
                                                    STRACE("str", tout << __LINE__
                                                                       << " " << atValue.get_int64() << " " << mk_pp(at, m)
                                                                       << std::endl;);
                                                    if (content[atValue.get_int64()] < '0' ||
                                                        content[atValue.get_int64()] > '9') {
                                                        STRACE("str", tout << __LINE__
                                                                           << " break because of str-int: first part = 0"
                                                                           << std::endl;);
                                                        subpossibleCases.reset();
                                                        break;
                                                    }
                                                    STRACE("str", tout << __LINE__ << " " << content << " " << atValue.get_int64()
                                                                       << std::endl;);
                                                    lhsExpr = mk_int(content[atValue.get_int64()]);
                                                }

                                                subpossibleCases.push_back(createEqualOperator(
                                                        lhsExpr,
                                                        createSelectOperator(arrayRhs,
                                                                             createAddOperator(m_autil.mk_int(k),
                                                                                               prefix_rhs))));
                                            }
                                            STRACE("str", tout << __LINE__ << " "
                                                               << std::endl;);
                                            if (subpossibleCases.size() > 0)
                                                possibleCases.push_back(createAndOperator(subpossibleCases));
                                        }
                                    }
                                    STRACE("str", tout << __LINE__ << " "
                                                       << std::endl;);
                                }
                                else {
                                    expr_ref_vector parts(m);
                                    parts.push_back(generate_constraint_flat_flat(a, elementNames, i, pMax, q_bound));
                                    if (partCnt == 2) {
                                        parts.push_back(generate_constraint_flat_flat(a, elementNames, i + 1, pMax,
                                                                                  q_bound));
                                    }
                                    possibleCases.push_back(createAndOperator(parts));
                                }
                            }

                            if (!is_str_int_var(elementNames[i].first))
                                possibleCases.push_back(createLessEqOperator(m_autil.mk_int(std::min(localSplit, (int)content.length()) + 1 ), subLen));
                            else {
                                // dont bound
                            }
                            resultParts.push_back(createOrOperator(possibleCases));
                        }
                    }
                    i += (partCnt - 1);
                }
            }
            else {
                // handling regex vs const && regex vs regex
                expr* reg = nullptr;
                SASSERT(isInternalRegexVar(a.first, reg));
                zstring val;
                expr *to_assert = nullptr;
                STRACE("str", tout << __LINE__
                                   << mk_pp(a.first, m) << " "
                                   << mk_pp(elementNames[i].first, m) << " "<< std::endl;);
                if (u.str.is_string(elementNames[i].first, val)) {
                    to_assert = generate_constraint_flat_flat(a, elementNames, i, pMax, rational(val.length()));
                }
                else
                    to_assert = generate_constraint_flat_flat(a, elementNames, i, pMax, q_bound);
                resultParts.push_back(to_assert);
            }
        }
        return createAndOperator(resultParts);
    }

    /*
     * elementNames[pos] is a non_fresh_.
     * how many parts of that non_fresh_ variable are in the const | regex
     */
    expr* theory_str::find_partsOfnon_fresh_VariablesInAVector(
            int pos,
            std::vector<std::pair<expr*, int>> elementNames,
            int &partCnt){
        partCnt = 1;
        ast_manager &m = get_manager();
        expr_ref_vector addElements(m);
        addElements.push_back(createMultiplyOperator(getExprVarFlatSize(elementNames[pos]), getExprVarFlatIter(elementNames[pos])));
        unsigned int j = pos + 1;
        for (j = pos + 1; j < elementNames.size(); ++j)
            if (elementNames[j].second > elementNames[j - 1].second &&
                elementNames[j].second > 0 &&
                elementNames[j].first == elementNames[j - 1].first &&
                elementNames[j].second % p_bound.get_int64() != 0 &&
                elementNames[j].second != REGEX_CODE) {
                partCnt++;
                addElements.push_back(createMultiplyOperator(getExprVarFlatSize(elementNames[j]),
                                                             getExprVarFlatIter(elementNames[j])));
            }
            else
                break;

        /* sublen = part_1 + part2 + .. */
        return createAddOperator(addElements);
    }

    /*
     * pre elements + pre fix of itself
     */
    expr* theory_str::leng_prefix_lhs(std::pair<expr*, int> a,
                                std::vector<std::pair<expr*, int>> elementNames,
                                int pos,
                                bool optimizing,
                                bool unrollMode) {

        ast_manager &m = get_manager();
        expr_ref_vector addElements(m);

        if (a.second > REGEX_CODE && !optimizing && unrollMode) {
            if (a.second % p_bound.get_int64() != -1)
                for (int i = a.second + 1; i < 0; ++i){ /* prefix of a - const */
                    addElements.push_back(
                            createMultiplyOperator(
                                    getExprVarFlatSize(std::make_pair(a.first, i)),
                                    getExprVarFlatIter(std::make_pair(a.first, i))));
                    if (i % p_bound.get_int64() == -1)
                        break;
                }

            if (a.second % p_bound.get_int64() != 0)
                for (int i = a.second - 1; i >= 0; --i){ /* a is var */
                    addElements.push_back(
                            createMultiplyOperator(
                                    getExprVarFlatSize(std::make_pair(a.first, i)),
                                    getExprVarFlatIter(std::make_pair(a.first, i))));
                    if (i % p_bound.get_int64() == 0)
                        break;
                }
        }

        expr* reg = nullptr;
        for (int i = pos - 1; i >= 0; --i) { /* pre-elements */
            zstring value;
            if (u.str.is_string(elementNames[i].first, value) && i > 0 && elementNames[i].second + 1 == elementNames[i - 1].second && (elementNames[i].second % p_bound.get_int64()) == 0) {
                addElements.push_back(mk_int(value.length()));
                i--;
            }
            else if (u.re.is_union(elementNames[i].first) || u.re.is_star(elementNames[i].first) ||
                u.re.is_plus(elementNames[i].first) || isInternalRegexVar(elementNames[i].first, reg)) {
                addElements.push_back(getExprVarFlatSize(elementNames[i]));
            }
            else if (i > 0 && elementNames[i].second - 1 == elementNames[i - 1].second && (elementNames[i].second % p_bound.get_int64()) == p_bound.get_int64() - 1) {
                addElements.push_back(mk_strlen(elementNames[i].first));
                i--;
            }
            else addElements.push_back(
                    createMultiplyOperator(
                            getExprVarFlatSize(elementNames[i]),
                            getExprVarFlatIter(elementNames[i])));
        }
        return createAddOperator(addElements);
    }

    /*
     *  pre fix of itself
     */
    expr* theory_str::leng_prefix_rhs(
            std::pair<expr*, int> a, /* var */
            bool unrollMode) {
        ast_manager &m = get_manager();
        expr_ref_vector addElements(m);
        if (a.second > REGEX_CODE && unrollMode) {
            if (a.second % p_bound.get_int64() != -1)
                for (int i = a.second + 1; i < 0; ++i){ /* a is const */
                    addElements.push_back(createMultiplyOperator(getExprVarFlatSize(std::make_pair(a.first, i)), getExprVarFlatIter(std::make_pair(a.first, i))));
                    if (i % p_bound.get_int64() == -1)
                        break;
                }

            if (a.second % p_bound.get_int64() != 0)
                for (int i = a.second - 1; i >= 0; --i){ /* a is var */
                    addElements.push_back(createMultiplyOperator(getExprVarFlatSize(std::make_pair(a.first, i)), getExprVarFlatIter(std::make_pair(a.first, i))));
                    if (i % p_bound.get_int64() == 0)
                        break;
                }
        }
        else {
            // skip
        }

        return createAddOperator(addElements);
    }

    /*
	 * Input: constA and a number of flats
	 * Output: all possible ways to split constA
	 */
    std::vector<std::vector<int> > theory_str::collectAllPossibleSplits(
            std::pair<expr*, int> lhs,
            std::vector<std::pair<expr*, int> > elementNames,
            bool optimizing){

        /* use alias instead of elementNames */
        std::vector<std::vector<int> > allPossibleSplits;
        SASSERT(lhs.second < 0);

        zstring value;
        u.str.is_string(lhs.first, value);
        if (lhs.second <= REGEX_CODE) /* regex */ {
            expr* reg = nullptr;
            if (isInternalRegexVar(lhs.first, reg)) {
                if (!const_vs_regex(reg, elementNames)) {
                    return {};
                }
            }
            return {};
            NOT_IMPLEMENTED_YET();
//            std::vector<int> curr;
//            zstring regexContent = parse_regex_content(lhs.first);
//            collectAllPossibleSplits_regex(0, regexContent, 10, alias, curr, allPossibleSplits);
        }
        else if (lhs.second % p_bound.get_int64() == 0) /* tail */ {
            if (optimizing){
                std::vector<int> curr;
                collectAllPossibleSplits_const(0, value, 10, elementNames, curr, allPossibleSplits);
            }
            else for (unsigned i = 0; i <= value.length(); ++i) {
                    std::vector<int> curr;
                    collectAllPossibleSplits_const(0, value.extract(i, value.length() - i), 10, elementNames, curr, allPossibleSplits);
                }
        }
        else if (lhs.second % p_bound.get_int64() == -1) /* head */ {
            if (p_bound.get_int64() == 1 || optimizing) {
                std::vector<int> curr;
                collectAllPossibleSplits_const(0, value, 10, elementNames, curr, allPossibleSplits);
            }
            else for (unsigned i = 0; i <= value.length(); ++i) {
                    std::vector<int> curr;

                    collectAllPossibleSplits_const(0, value.extract(0, i), 10, elementNames, curr, allPossibleSplits);

                }
        }
        else {
            SASSERT(false);
        }

        /* print test */
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(lhs.first, get_manager()) << std::endl;);
        for (unsigned int i = 0; i < allPossibleSplits.size(); ++i){
            for (unsigned int j = 0; j < allPossibleSplits[i].size(); ++j)
                STRACE("str", tout << allPossibleSplits[i][j] << " - ";);
            STRACE("str", tout << std::endl;);
        }

        return allPossibleSplits;
    }

//    void theory_str::collectAllPossibleSplits_regex(
//            int pos,
//            std::string str, /* regex */
//            int pMax,
//            std::vector<std::pair<std::string, int> > elementNames,
//            std::vector<int> currentSplit,
//            std::vector<std::vector<int> > &allPossibleSplits) {
//
//        /* reach end */
//        if (currentSplit.size() == elementNames.size() &&
//            (pos == 0 || pos == MINUSZERO)) {
//
//            allPossibleSplits.emplace_back(currentSplit);
//            return;
//        }
//        else if (currentSplit.size() >= elementNames.size()) {
//            return;
//        }
//
//        unsigned int regexLen = str.length();
//        if (isRegexAll(str) || isRegexChar(str))
//            regexLen = 1;
//        /* special case for const: regex = .* const .* */
//        if (elementNames[currentSplit.size()].second == -1 && p_bound.get_int64() == 1) {
//            /* compare text, check whether the string can start from the location pos in text */
//            if (const_in_regex_at_pos(str, elementNames[currentSplit.size()].first, pos)) {
//                currentSplit.emplace_back(elementNames[currentSplit.size()].first.length());
//                collectAllPossibleSplits_regex((pos + elementNames[currentSplit.size() - 1].first.length()) % regexLen, str, pMax, elementNames, currentSplit, allPossibleSplits);
//                currentSplit.pop_back();
//            }
//        }
//
//            /* special case for const tail, when we know the length of const head */
//        else if (elementNames[currentSplit.size()]p_bound.get_int64() p_bound.get_int64() == 0 &&
//                 elementNames[currentSplit.size()].second < 0 &&
//                 elementNames[currentSplit.size()].second > REGEX_CODE &&
//                 currentSplit.size() > 0) /* tail, not the first */ {
//            assert (elementNames[currentSplit.size() - 1].second - 1 == elementNames[currentSplit.size()].second);
//            int length = elementNames[currentSplit.size()].first.length() - currentSplit[currentSplit.size() - 1]; /* this part gets all const string remaining */
//
//            currentSplit.emplace_back(length);
//            collectAllPossibleSplits_regex((pos + length) % regexLen, str, pMax, elementNames, currentSplit, allPossibleSplits);
//            currentSplit.pop_back();
//        }
//
//        else if (elementNames[currentSplit.size()].second % p_bound.get_int64() == 0 &&
//                 elementNames[currentSplit.size()].second < 0 &&
//                 elementNames[currentSplit.size()].second > REGEX_CODE &&
//                 currentSplit.size() == 0) /* tail, first */ {
//            /* find all possible start points */
//            std::vector<int> tail = tail_in_regex_at_pos(str, elementNames[currentSplit.size()].first, pos);
//            for (unsigned i = 0 ; i < tail.size(); ++i) {
//                currentSplit.emplace_back(tail[i]);
//                collectAllPossibleSplits_regex((pos + tail[i]) % regexLen, str, pMax, elementNames, currentSplit, allPossibleSplits);
//                currentSplit.pop_back();
//            }
//        }
//
//        else if (elementNames[currentSplit.size()].second % p_bound.get_int64() == -1 &&
//                 elementNames[currentSplit.size()].second < 0 &&
//                 elementNames[currentSplit.size()].second > REGEX_CODE &&
//                 currentSplit.size() + 1 == elementNames.size() &&
//                 p_bound.get_int64() == 2) /* head, the last element */ {
//            /* find all possible start points */
//            std::vector<int> head = head_in_regex_at_pos(str, elementNames[currentSplit.size()].first, pos);
//            for (unsigned i = 0 ; i < head.size(); ++i) {
//                currentSplit.emplace_back(head[i]);
//                collectAllPossibleSplits_regex((pos + head[i]) % regexLen, str, pMax, elementNames, currentSplit, allPossibleSplits);
//                currentSplit.pop_back();
//            }
//        }
//
//        else if (elementNames[currentSplit.size()].second % p_bound.get_int64() == -1 &&
//                 elementNames[currentSplit.size()].second < 0 &&
//                 elementNames[currentSplit.size()].second > REGEX_CODE &&
//                 currentSplit.size() + 1 < elementNames.size() &&
//                 p_bound.get_int64() == 2) /* head, not the last element */ {
//            /* check full string */
//            bool canProcess;
//            if (isUnionStr(str))
//                canProcess = true;
//            else
//                canProcess = const_in_regex_at_pos(str, elementNames[currentSplit.size()].first, pos);
//            if (elementNames[currentSplit.size() + 1].second == elementNames[currentSplit.size()].second - 1){
//                if (canProcess) {
//                    for (unsigned i = 1 ; i <= elementNames[currentSplit.size()].first.length(); ++i) { /* cannot be empty */
//                        currentSplit.emplace_back(i);
//                        currentSplit.emplace_back(elementNames[currentSplit.size()].first.length() - i);
//                        collectAllPossibleSplits_regex((pos + elementNames[currentSplit.size()].first.length()) % regexLen, str, pMax, elementNames, currentSplit, allPossibleSplits);
//                        currentSplit.pop_back();
//                        currentSplit.pop_back();
//                    }
//                }
//            }
//            else {
//                /* this const only has 1 part */
//                if (canProcess) {
//                    for (unsigned i = 1 ; i <= elementNames[currentSplit.size()].first.length(); ++i) { /* cannot be empty */
//                        currentSplit.emplace_back(i);
//                        collectAllPossibleSplits_regex((pos + i) % regexLen, str, pMax, elementNames, currentSplit, allPossibleSplits);
//                        currentSplit.pop_back();
//                    }
//                }
//            }
//        }
//
//        else if (elementNames[currentSplit.size()].second == REGEX_CODE) /* regex */ {
//            std::string content = parse_regex_content(elementNames[currentSplit.size()].first);
//            int contentLength = (int)content.length();
//
//            std::vector<std::string> components = {content};
//            if (isUnionStr(content)) {
//                components = collect_alternative_components(content);
//                for (const auto& s : components)
//                    contentLength = std::min(contentLength, (int)s.length());
//            }
//            std::vector<int> regexPos = regex_in_regex_at_pos(str, elementNames[currentSplit.size()].first, pos);
//            /* loop ? */
//            bool loop = false;
//            if (regexPos.size() > 0 &&
//                regexPos[regexPos.size() - 1] * contentLength % regexLen == 0) {
//                loop = true;
//            }
//            __debugPrint(logFile, "%d loop = %d, regexPos size = %ld, contentLength = %d\n", __LINE__, loop ? 1 : 0, regexPos.size(), contentLength);
//
//            if (regexPos.size() == 0) {
//                currentSplit.emplace_back(0);
//                collectAllPossibleSplits_regex(pos, str, pMax, elementNames, currentSplit, allPossibleSplits);
//                currentSplit.pop_back();
//            }
//            else {
//                if (loop == true) /* assign value < 0 */
//                    for (unsigned i = 0 ; i < regexPos.size(); ++i) {
//                        /* because of loop, do not care about 0 iteration */
//                        int tmp = (contentLength * regexPos[i]) % regexLen;
//                        if (tmp == 0)
//                            currentSplit.emplace_back(MINUSZERO);
//                        else
//                            currentSplit.emplace_back(-tmp);
//                        collectAllPossibleSplits_regex((pos + contentLength * regexPos[i]) % regexLen, str, pMax, elementNames, currentSplit, allPossibleSplits);
//                        currentSplit.pop_back();
//                    }
//                else
//                    for (unsigned i = 0 ; i < regexPos.size(); ++i) { /* assign value >= 0 */
//                        int tmp = (pos + contentLength * regexPos[i]) % regexLen;
//                        currentSplit.emplace_back(contentLength * regexPos[i]);
//                        collectAllPossibleSplits_regex(tmp, str, pMax, elementNames, currentSplit, allPossibleSplits);
//                        currentSplit.pop_back();
//                    }
//            }
//        }
//
//        else {
//            for (unsigned i = 0; i < regexLen; ++i) { /* assign value < 0 because it can iterate many times */
//                int length = i;
//                if (length == 0)
//                    currentSplit.emplace_back(MINUSZERO);
//                else
//                    currentSplit.emplace_back(- length);
//                collectAllPossibleSplits_regex((pos + length) % regexLen, str, pMax, elementNames, currentSplit, allPossibleSplits);
//                currentSplit.pop_back();
//            }
//        }
//    }

    bool theory_str::not_contain_check(expr* e, std::vector<std::pair<expr*, int> > elementNames){
        zstring value;
        if (u.str.is_string(e, value)) {
            for (int i = 0; i < elementNames.size(); ++i) {
                zstring subVar;
                if  (u.str.is_string(elementNames[i].first, subVar) &&
                        ((elementNames[i].second % p_bound.get_int64() == -1 && i + 1 < elementNames.size()) ||
                        subVar.length() == 1)) {
                    if (!value.contains(subVar)) {
                        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: skip quickly because of " << value << " not contain " << subVar << std::endl;);
                        return false;
                    }
                }
            }
        }

        for (int i = 0; i < elementNames.size(); ++i) {
            zstring subVar;
            if  (u.str.is_string(elementNames[i].first, subVar) &&
                 ((elementNames[i].second % p_bound.get_int64() == -1 && i + 1 < elementNames.size()) ||
                  subVar.length() == 1)) {
                expr* real_haystack = nullptr;
                if (not_contain(e, elementNames[i].first, real_haystack)) {
                    STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: skip quickly because of " << mk_pp(e, get_manager()) << " not contain " << subVar << std::endl;);
                    return false;
                }
            }
        }
        return true;
    }

//    bool theory_str::const_vs_regex(expr* reg, std::vector<std::pair<expr*, int> > elementNames){
//        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(reg, get_manager()) << std::endl;);
//        if (u.re.is_union(reg)) {
//            std::vector<zstring> components = collect_alternative_components(reg);
//            zstring tmp;
//            for (int i = 0; i < elementNames.size(); ++i)
//                if (u.str.is_string(elementNames[i].first, tmp) &&
//                        ((tmp.length() == 1) || (i + 1 < elementNames.size() && elementNames[i].first == elementNames[i + 1].first))) {
//                    bool found = false;
//                    bool reverse = false;
//                    for (const auto& s : components) {
//                        if (s.contains(tmp)) {
//                            found = true;
//                            break;
//                        }
//
//                        if (tmp.contains(s)) {
//                            reverse = true;
//                        }
//                    }
//                    if ((!found && components.size() == 1) || (!found && components.size() > 1 && !reverse)) {
//                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(reg, get_manager()) << " cannot contain " << mk_pp(elementNames[i].first, get_manager())<< std::endl;);
//                        return false;
//                    }
//                }
//        }
//        else if (u.re.is_star(reg) || u.re.is_plus(reg)) {
//            return const_vs_regex(to_app(reg)->get_arg(0), elementNames);
//        }
//        return true;
//    }

    bool theory_str::const_vs_regex(expr* reg, std::vector<std::pair<expr*, int> > elementNames){
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(reg, get_manager()) << std::endl;);
        zstring tmp;
        for (int i = 0; i < elementNames.size(); ++i)
            if (u.str.is_string(elementNames[i].first, tmp) &&
                ((tmp.length() == 1) || (i < elementNames.size() - 1 && elementNames[i].second % p_bound.get_int64() == -1))) {
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(reg, get_manager()) << " vs " << tmp << std::endl;);
                if (!matchRegex(reg, tmp))
                    return false;
            }
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(reg, get_manager()) << std::endl;);
        return true;
    }

    bool theory_str::length_base_split(expr* e, std::vector<std::pair<expr*, int> > elementNames){
        for (const auto& n : elementNames){
            if (length_relation.find(std::make_pair(n.first, e)) != length_relation.end()){
                STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " " << mk_pp(e, get_manager()) << " cannot contain because of length based split" << mk_pp(n.first, get_manager())<< std::endl;);
                return false;
            }
        }
        return true;
    }

    bool theory_str::const_vs_str_int(expr* e, std::vector<std::pair<expr*, int> > elementNames, expr* &extra_assert){
        if (string_int_vars.contains(e)){
            for (int i = 0; i < elementNames.size(); ++i) {
                zstring val;
                if (u.str.is_string(elementNames[i].first, val)) {
                    for (int j = 0; j < val.length(); ++j)
                        if ((val[j] < '0' || val[j] > '9') &&
                            (val.length() == 1 ||
                             (j == 0 && elementNames[i].second % p_bound.get_int64() == -1) ||
                             (j == val.length() - 1 && elementNames[i].second % p_bound.get_int64() == 0))) {
                            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(e, get_manager())
                                               << " cannot contain because of str-int" << mk_pp(elementNames[i].first, get_manager())
                                               << std::endl;);
                            extra_assert = createEqualOperator(u.str.mk_stoi(e), mk_int(-1));
                            return false;
                        }
                }
            }
        }
        return true;
    }

    /*
	 * textLeft: length of string
	 * nMax: number of flats
	 *
	 * Pre-Condition: 1st flat and n-th flat must be greater than 0
	 * Output: of the form 1 * 1 + 1 * 0 + 1 * 0 + 1 * 0 + 1 * 0 + 1 * 0 + 1 * 0 + 1 * 0 + 1 * 3 + 2 * 3 = 10
	 */
    void theory_str::collectAllPossibleSplits_const(
            int pos,
            zstring str, /* const */
            int pMax,
            std::vector<std::pair<expr*, int> > elementNames,
            std::vector<int> currentSplit,
            std::vector<std::vector<int> > &allPossibleSplits
    ) {

        /* reach end */
        if (currentSplit.size() == elementNames.size()){
            if (pos == (int)str.length() &&
                feasibleSplit_const(str, elementNames, currentSplit, p_bound.get_int64())) {
                allPossibleSplits.emplace_back(currentSplit);
            }
            else {
            }
            return;
        }

        unsigned textLeft = str.length() - pos;
        zstring value("");
        u.str.is_string(elementNames[currentSplit.size()].first, value);
//        if (value.length() > 0)
//            STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << str << " vs " << value << " " << elementNames[currentSplit.size()].second << std::endl;);
        /* special case for const: leng = leng */
        if (p_bound.get_int64() == 1 || value.length() == 1) {
            if (value.length() <= textLeft) {
                zstring constValue = str.extract(pos, value.length());

                if (constValue == value ) {
                    currentSplit.emplace_back(value.length());
                    collectAllPossibleSplits_const(pos + value.length(), str, pMax, elementNames, currentSplit, allPossibleSplits);
                    currentSplit.pop_back();
                }
            }
        }

        /* const head */
        else if (elementNames[currentSplit.size()].second % p_bound.get_int64() == -1 &&
                elementNames[currentSplit.size()].second < 0 &&
                elementNames[currentSplit.size()].second > REGEX_CODE &&
                p_bound.get_int64() == 2) {
            STRACE("str", tout << __LINE__ << " checking str: " << value << std::endl;);
            if (value.length() <= textLeft) {
                std::set<zstring> values;
                values.insert(value);

                for (const auto& v : values) {
                    zstring constValue = str.extract(pos, v.length());
                    if (constValue == v) {
                        if (values.size() > 1) {
                            STRACE("str", tout << __LINE__ << " passed value: " << value << std::endl;);
                        }
                        currentSplit.emplace_back(v.length());
                        collectAllPossibleSplits_const(pos + v.length(), str, pMax, elementNames, currentSplit, allPossibleSplits);
                        currentSplit.pop_back();

//                        for (int i = 0; i < std::min(7, (int)v.length()); ++i) {
//                            currentSplit.emplace_back(i);
//                            collectAllPossibleSplits_const(pos + i, str, pMax, elementNames, currentSplit, allPossibleSplits);
//                            currentSplit.pop_back();
//                        }
                    }
                }
            }
        }

        /* special case for const tail, when we know the length of const head */
        else if (currentSplit.size() > 0 &&
                 elementNames[currentSplit.size()].second % p_bound.get_int64() == 0 &&
                 elementNames[currentSplit.size()].second < 0 &&
                 elementNames[currentSplit.size()].second > REGEX_CODE &&
                p_bound.get_int64() == 2) /* const */ {
            SASSERT (elementNames[currentSplit.size() - 1].second % p_bound.get_int64() == -1);
            std::set<zstring> values;
            values.insert(value);
            for (const auto& v : values) {
                zstring constValue = str.extract(pos - currentSplit[currentSplit.size() - 1], v.length());
                unsigned length = (unsigned)v.length() - currentSplit[currentSplit.size() - 1]; /* this part gets all const string remaining */

                if (constValue == v) {
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
                 elementNames[0].second % p_bound.get_int64() == 0 &&
                 elementNames[0].second < 0 &&
                 elementNames[0].second > REGEX_CODE &&
                p_bound.get_int64() == 2) /* const */ {
            std::set<zstring> values;
            if (isUnionStr(value)){
                values = extendComponent(value);
            }
            else
                values.emplace(value);
            for (const auto& v : values)
                for (unsigned i = 0; i < std::min(value.length(), str.length()); ++i) {

                    zstring tmp00 = v.extract(v.length() - i, i);
                    zstring tmp01 = str.extract(0, i);
                    if (tmp00 == tmp01){
                        if (v.length() > 1)
                            STRACE("str", tout << __LINE__ << " passed value: " << v << std::endl;);
                        currentSplit.emplace_back(tmp00.length());
                        collectAllPossibleSplits_const(pos + tmp00.length(), str, pMax, elementNames, currentSplit, allPossibleSplits);
                        currentSplit.pop_back();
                    }
                }
        }

        else {
            SASSERT(!(elementNames[currentSplit.size()].second < 0 && elementNames[currentSplit.size()].second > REGEX_CODE));

            std::string regexContent = "";
            expr* re = nullptr;
            isInternalRegexVar(elementNames[currentSplit.size()].first, re);
            if (currentSplit.size() + 1 == elementNames.size() && elementNames[currentSplit.size()].second >= 0) {
                // end by vars
                currentSplit.emplace_back(textLeft);
                collectAllPossibleSplits_const(pos + textLeft, str, pMax, elementNames, currentSplit, allPossibleSplits);
                currentSplit.pop_back();
            }
            else if (currentSplit.size() + 1 <= elementNames.size() && elementNames[currentSplit.size()].second >= 0 && elementNames[currentSplit.size() + 1].second >= 0) {
                // next element is also a var
                currentSplit.emplace_back(0);
                collectAllPossibleSplits_const(pos, str, pMax, elementNames, currentSplit, allPossibleSplits);
                currentSplit.pop_back();
            }
            else {
                for (unsigned i = 0; i <= textLeft; ++i) {
                    unsigned length = i;
                    if (elementNames[currentSplit.size()].second <= REGEX_CODE) /* regex */ {
                        STRACE("str", tout << __LINE__ << " regex: " << mk_pp(elementNames[currentSplit.size()].first, get_manager()) << " " <<  elementNames[currentSplit.size()].second << std::endl;);
                        SASSERT(re);
                        zstring regexValue = str.extract(pos, length);
                        bool matchRes = matchRegex(re, regexValue);
                        if (matchRes) {
                            currentSplit.emplace_back(length);
                            collectAllPossibleSplits_const(pos + length, str, pMax, elementNames, currentSplit,
                                                           allPossibleSplits);
                            currentSplit.pop_back();
                        }
                    } else {
                        currentSplit.emplace_back(length);
                        collectAllPossibleSplits_const(pos + length, str, pMax, elementNames, currentSplit,
                                                       allPossibleSplits);
                        currentSplit.pop_back();
                    }
                }
            }
        }
    }

    /*
	 * (a|b|c)*_xxx --> range <a, c>
	 */
    std::vector<std::pair<int, int>> theory_str::collectCharRange(expr* a){
        std::vector<bool> chars;
        for (int i = 0; i <= 256; ++i)
            chars.push_back(false);
        collectCharRange(a, chars);
        if (chars[255])
            return {std::make_pair(-1, -1)};
        else {
            std::vector<std::pair<int, int>> ret;

            while (true) {
                int start = -1;
                for (int i = 0; i < 255; ++i) {
                    if (chars[i]) {
                        start = i;
                        break;
                    }
                }

                if (start == -1)
                    break;

                int finish = -1;
                for (int i = start; i < 255; ++i) {
                    if (!chars[i]) {
                        finish = i;
                        break;
                    }
                    chars[i] = false;
                }
                ret.push_back(std::make_pair(start, finish - 1));
            }

            SASSERT(ret.size() > 0);
            return ret;
        }

    }

    void theory_str::collectCharRange(expr* a, std::vector<bool> &chars){
        if (chars[255])
            return;
        if (u.re.is_plus(a) || u.re.is_star(a)){
            expr* tmp = to_app(a)->get_arg(0);
            collectCharRange(tmp, chars);
        }
        else if (u.re.is_to_re(a)){
            zstring value;
            u.str.is_string(to_app(a)->get_arg(0), value);
            if (value.length() != 1) {
                STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " ***: give up because " << mk_pp(a, get_manager()) << " " << value << "; len " << value.length() << std::endl;);
                chars[255] = true;
            }
            else
                chars[value[0]] = true;
        }
        else if (u.re.is_union(a)){
            expr* arg0 = to_app(a)->get_arg(0);
            collectCharRange(arg0, chars);

            expr* arg1 = to_app(a)->get_arg(1);
            collectCharRange(arg1, chars);
        }
        else if (u.re.is_range(a)) {
            expr* arg0 = to_app(a)->get_arg(0);
            expr* arg1 = to_app(a)->get_arg(1);
            zstring start;
            zstring finish;
            u.str.is_string(arg0, start);
            u.str.is_string(arg1, finish);

            SASSERT(start.length() == 1);
            SASSERT(finish.length() == 1);
            zstring ret;
            for (unsigned i = start[0]; i <= (unsigned)finish[0]; ++i){
                chars[i] = true;
            }
        }
        else {
            expr* reg = nullptr;
            if (isInternalRegexVar(a, reg)){
                collectCharRange(reg, chars);
            }
            else {
                STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " ***: " << mk_pp(a, get_manager())
                                   << std::endl;);
                NOT_IMPLEMENTED_YET();
            }
        }
    }

    bool theory_str::feasibleSplit_const(
            zstring str,
            std::vector<std::pair<expr*, int> > elementNames,
            std::vector<int> currentSplit,
            int bound){
        /* check feasible const split */
        int pos = 0;
        for (unsigned i = 0; i < currentSplit.size(); ++i) {
            if (elementNames[i].second <= REGEX_CODE) {
            }

            else if (elementNames[i].second < 0) { /* const */
                zstring value;
                u.str.is_string(elementNames[i].first, value);
                if (currentSplit[i] > (int)value.length()) {
                }
                SASSERT ((int)value.length() >= currentSplit[i]);

                zstring lhs = str.extract(pos, currentSplit[i]);
                zstring rhs = "";
                if (elementNames[i].second % p_bound.get_int64() == -1) /* head */ {
                    rhs = value.extract(0, currentSplit[i]);

                    if (i + 1 < elementNames.size()) {
                        if (p_bound.get_int64() == 1 || value.length() == 1) {
                            SASSERT (currentSplit[i] == (int)value.length()); /* const length must be equal to length of const */
                        }
                        else {
                            SASSERT (elementNames[i + 1].second % p_bound.get_int64() == 0);
                            SASSERT ((currentSplit[i] + currentSplit[i + 1] == (int)value.length())); /* sum of all const parts must be equal to length of const */
                        }
                    }
                }
                else { /* tail */
                    rhs = value.extract(value.length() - currentSplit[i], currentSplit[i]);
                }

                if (lhs != rhs){
                    SASSERT(false);
                    return false;
                }
            }
            pos += currentSplit[i];
        }
        return true;
    }

    /*
	 * 0: No const, No non_fresh_ var
	 * 1: const		No non_fresh_ var
	 * 2: no const, non_fresh_ var
	 * 3: have both
	 */
    int theory_str::choose_split_type(
            std::vector<std::pair<expr*, int>> elementNames,
            std::map<expr*, int> non_fresh_Variables,
            expr* lhs){

        bool havingConst = false;
        bool havingnon_fresh_Var = false;
        expr* reg = nullptr;
        if (lhs != nullptr) {
            isInternalRegexVar(lhs, reg);
        }
        /* check if containing const */
        for (unsigned i = 0 ; i < elementNames.size(); ++i)
            if (elementNames[i].second < 0) {
                bool skip = false;
                if (reg != nullptr){
                    zstring val;
                    expr* regTmp = nullptr;
                    if (u.str.is_string(elementNames[i].first, val)){
                        if (matchRegex(reg, val)){
                            skip = true;
                        }
                    }
                    else if (isInternalRegexVar(elementNames[i].first, regTmp)){
                        if (matchRegex(reg, regTmp)){
                            skip = true;
                        }
                    }
                }

                if (!skip) {
                    havingConst = true;
                    break;
                }
            }

        /* check if containing non_fresh_ vars */
        for (unsigned i = 0 ; i < elementNames.size(); ++i)
            if (non_fresh_Variables.find(elementNames[i].first) != non_fresh_Variables.end() || elementNames[i].second <= REGEX_CODE) {
                havingnon_fresh_Var = true;
                break;
            }

        if (!havingnon_fresh_Var && !havingConst)
            return SIMPLE_CASE;
        else if (!havingnon_fresh_Var && havingConst)
            return CONST_ONLY;
        else if (havingnon_fresh_Var && !havingConst)
            return NON_FRESH__ONLY;
        else
            return CONST_NON_FRESH;
    }

    /*
	 * Given a flat,
	 * generate its size constraint
	 */
    std::string theory_str::generateVarSize(std::pair<expr*, int> a, std::string l_r_hs){
        std::string result = "";
        if (a.second >= 0) {
            /* simpler version */
            result += LENPREFIX;
            result += expr2str(a.first);
        }
        else {
            /* const string */
            zstring value;
            SASSERT(u.str.is_string(a.first, value));
            result += LENPREFIX;
            result += ("\"" + value.encode() + "\"");
        }
        return result;
    }

    expr* theory_str::getExprVarSize(std::pair<expr*, int> a){
        zstring val;
        if (u.str.is_string(a.first, val)){
            return m_autil.mk_int(val.length());
        }
        else {
            return mk_strlen(a.first);
        }
    }

    /*
     *
     */
    std::string theory_str::generateFlatIter(std::pair<expr*, int> a){

        std::string result = "";
        if (a.second >= 0) {
            std::string tmp = expr2str(a.first);
            /* simpler version */
            result += tmp;
            result += "_";
            result += std::to_string(a.second);
            result += ITERSUFFIX;
        }
        else if (a.second <= REGEX_CODE) {
            std::string tmp = expr2str(a.first);
            /* simpler version */
            result += tmp;
            result += "_";
            result += std::to_string(std::abs(a.second));
            result += ITERSUFFIX;
        }
        else {
            /* const string */
            result = "1";
        }
        return result;
    }

    expr* theory_str::getExprVarFlatIter(std::pair<expr*, int> a){
        if (u.str.is_string(a.first)){
            return mk_int(1);
        }
        else if (a.second <= REGEX_CODE) {
            return iterMap[a.first][std::abs(a.second - REGEX_CODE)];
        }
        else {
            return mk_int(1);
            return iterMap[a.first][a.second];
        }
    }

    /*
     * Given a flat,
     * generate its size constraint
     */
    std::string theory_str::generateFlatSize(std::pair<expr*, int> a, std::string l_r_hs){
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(a.first, get_manager()) << "," << a.second << std::endl;);
        std::string result = "";
        if (a.second >= 0) {
            std::string tmp = expr2str(a.first);
            /* simpler version */
            result += LENPREFIX;
            result += tmp;
            result += "_";
            result += std::to_string(a.second);
        }
        else {
            if (a.second > REGEX_CODE) {
                /* const string */
                zstring value;
                SASSERT(u.str.is_string(a.first, value));
                result += LENPREFIX;
                result += ("\"" + value.encode() + "\"");
                result += "_";
                result += std::to_string(std::abs(a.second));
            }
            else {
                /* regex */
                result += LENPREFIX;
                std::string value = expr2str(a.first);
                result += value;
                result += "_";
                result += std::to_string(std::abs(a.second));
            }
        }
        return result;
    }

    expr* theory_str::getExprVarFlatSize(std::pair<expr*, int> a){
        zstring val;
        if (!u.str.is_string(a.first, val)) {
            if (a.second <= REGEX_CODE)
                return mk_strlen(a.first);
//                return lenMap[a.first][std::abs(a.second - REGEX_CODE)];
            else
                return lenMap[a.first][std::abs(a.second)];
        }
        else {
            if (val.length() == 1)
                return mk_int(1);
            else
                return lenMap[a.first][std::abs(a.second) - 1];
        }
    }

    /*
	 * Given a flat,
	 * generate its array name
	 */
    std::string theory_str::generateFlatArray(std::pair<expr*, int> a){
        std::string result = "";
        if (a.second >= 0) {
            std::string tmp = expr2str(a.first);
            /* simpler version */
            result += ARRPREFIX;
            result += tmp;
        }
        else {
            /* const string */
            zstring value;
            SASSERT(u.str.is_string(a.first, value));
            result += ARRPREFIX;
            result += ("\"" + expr2str(a.first) + "\"");
        }
        return result;
    }

    expr* theory_str::getExprVarFlatArray(std::pair<expr*, int> a){
        return getExprVarFlatArray(a.first);
    }

    expr* theory_str::getExprVarFlatArray(expr* e){
        ensure_enode(e);
        if (arrMap.find(e) != arrMap.end())
            return arrMap[e];
        expr_ref_vector eqNodeSet(get_manager());
        collect_eq_nodes(e, eqNodeSet);
        for (int i = 0; i < eqNodeSet.size(); ++i){
            if (arrMap.find(eqNodeSet[i].get()) != arrMap.end()) {
                STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(e, get_manager()) << " == " << mk_pp(eqNodeSet[i].get(), get_manager()) << std::endl;);
                return arrMap[eqNodeSet[i].get()];
            }
        }
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(e, get_manager()) << " " << mk_pp(e, get_manager()) << std::endl;);
        return nullptr;
    }

    expr* theory_str::get_bound_str_int_control_var(){
        return str_int_bound_expr;
    }

    expr* theory_str::get_bound_p_control_var(){
        return p_bound_expr;
    }

    expr* theory_str::get_bound_q_control_var(){
        return q_bound_expr;
    }

    app* theory_str::createITEOperator(expr* c, expr* t, expr* e){
        context & ctx   = get_context();
        if (t == e)
            return to_app(t);
        app* tmp = get_manager().mk_ite(c, t, e);
        ctx.internalize(tmp, false);
        return tmp;
    }

    /*
     *
     */
    app* theory_str::createEqualOperator(expr* x, expr* y){
        context & ctx   = get_context();
        if (x == y)
            return get_manager().mk_true();
        app* tmp = ctx.mk_eq_atom(x, y);
        ctx.internalize(tmp, false);
        return tmp;
    }

    /*
     *
     */
    app* theory_str::createMultiplyOperator(expr* x, expr* y){
        if (m_autil.is_numeral(y)){
            rational val;
            if (y == mk_int(1)){
                return to_app(x);
            }
            else if (y == mk_int(0)){
                return to_app(y);
            }
        }
        else if (m_autil.is_numeral(x)) {
            rational val;
            if (x == mk_int(1)){
                return to_app(y);
            }
            else if (x == mk_int(0)){
                return to_app(x);
            }
        }
        if (m_autil.is_numeral(y)){
            return m_autil.mk_mul(y, x);
        }
        else
            return m_autil.mk_mul(x, y);
    }

    /*
     *
     */
    app* theory_str::createModOperator(expr* x, expr* y){
        app* tmp = m_autil.mk_mod(x, y);
        return tmp;
    }


    /*
     *
     */
    app* theory_str::createMinusOperator(expr* x, expr* y){
        rational tmpValue0, tmpValue1;
        if (m_autil.is_numeral(x, tmpValue0) && m_autil.is_numeral(y, tmpValue1))
            return m_autil.mk_int(tmpValue0 - tmpValue1);

        expr* mul = createMultiplyOperator(mk_int(-1), y);
        context & ctx   = get_context();
        app* tmp = m_autil.mk_add(x, mul);
        ctx.internalize(tmp, false);
        return tmp;
    }

    /*
     *
     */
    app* theory_str::createAddOperator(expr* x, expr* y){
        rational tmpValue0, tmpValue1;
        if (m_autil.is_numeral(x, tmpValue0) && m_autil.is_numeral(y, tmpValue1))
            return m_autil.mk_int(tmpValue0 + tmpValue1);
        else if (x == mk_int(0))
            return to_app(y);
        else if (y == mk_int(0))
            return to_app(x);
        context & ctx   = get_context();
        app* tmp = m_autil.mk_add(x, y);
        ctx.internalize(tmp, false);
        return tmp;
    }

    /*
     *
     */
    app* theory_str::createAddOperator(expr_ref_vector adds){

        if (adds.size() == 0)
            return m_autil.mk_int(0);
        context & ctx   = get_context();
        app* tmp = m_autil.mk_add(adds.size(), adds.c_ptr());
        ctx.internalize(tmp, false);
        return tmp;
    }

    /*
     *
     */
    app* theory_str::createLessOperator(expr* x, expr* y){
        if (!m_autil.is_numeral(y)) {
            if (m_autil.is_numeral(x)) {
                rational tmp;
                get_arith_value(x, tmp);
                tmp = tmp + 1;
                return m_autil.mk_ge(y, mk_int(tmp));
            }
            else
                return m_autil.mk_ge(y, createAddOperator(x, mk_int(1)));
        }
        else {
            rational tmp;
            get_arith_value(y, tmp);
            tmp = tmp - 1;
            STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << tmp << std::endl;);
            return m_autil.mk_le(x, mk_int(tmp));
        }
    }

    /*
     *
     */
    app* theory_str::createLessEqOperator(expr* x, expr* y){
        if (!m_autil.is_numeral(y))
            return m_autil.mk_ge(y, x);
        else
            return m_autil.mk_le(x, y);
    }

    /*
     *
     */
    app* theory_str::createGreaterOperator(expr* x, expr* y){
        if (!m_autil.is_numeral(y)) {
            if (m_autil.is_numeral(x)) {
                rational tmp;
                get_arith_value(x, tmp);
                tmp = tmp - 1;
                return m_autil.mk_le(y, mk_int(tmp));
            }
            else
                return m_autil.mk_le(createAddOperator(y, mk_int(1)), x);
        }
        else {
            rational tmp;
            get_arith_value(y, tmp);
            tmp = tmp + 1;
            return m_autil.mk_ge(x, createAddOperator(y, mk_int(tmp)));
        }
    }

    /*
     *
     */
    app* theory_str::createGreaterEqOperator(expr* x, expr* y){
        if (!m_autil.is_numeral(y))
            return m_autil.mk_le(y, x);
        else
            return m_autil.mk_ge(x, y);
    }

    /*
     *
     */
    app* theory_str::createAndOperator(expr_ref_vector ands){
        ast_manager &m = get_manager();
        context & ctx   = get_context();
        if (ands.size() == 0)
            return m.mk_true();
        else if (ands.size() == 1) {
            ctx.internalize(ands[0].get(), false);
            return to_app(ands[0].get());
        }
        else if (ands.size() == 2 && ands[0].get() == ands[1].get()) {
            ands.pop_back();
        }

        app* tmp = m.mk_and(ands.size(), ands.c_ptr());
        ctx.internalize(tmp, false);
        return tmp;
    }

    /*
     *
     */
    app* theory_str::createOrOperator(expr_ref_vector ors){
        ast_manager &m = get_manager();
        context & ctx   = get_context();
        if (ors.size() == 0)
            return m.mk_false();
        else if (ors.size() == 1) {
            ctx.internalize(ors[0].get(), false);
            return to_app(ors[0].get());
        }

        app* tmp = m.mk_or(ors.size(), ors.c_ptr());
        ctx.internalize(tmp, false);
        return tmp;
    }

    /*
     *
     */
    expr* theory_str::createNotOperator(const expr_ref x){
        return ::mk_not(x);
    }

    /*
     *
     */
    expr* theory_str::createImpliesOperator(expr* a, expr* b){
        ast_manager &m = get_manager();
        expr_ref_vector ors(m);
        expr_ref tmp(a, m);
        ors.push_back(mk_not(tmp));
        ors.push_back(b);
        return createOrOperator(ors);
    }


    /*
     *
     */
    app* theory_str::createSelectOperator(expr* x, expr* y){
        ptr_vector<expr> sel_args;
        sel_args.push_back(x);
        sel_args.push_back(y);
        context & ctx   = get_context();
        app* tmp = m_arrayUtil.mk_select(sel_args.size(), sel_args.c_ptr());
        ctx.internalize(tmp, false);
        ctx.mark_as_relevant(tmp);
        return tmp;
    }



    int theory_str::canBeOptimized_LHS(
            int i, int startPos, int j,
            std::vector<int> left_arr,
            std::vector<int> right_arr,
            std::vector<std::pair<std::string, int>> lhs_elements,
            std::vector<std::pair<std::string, int>> rhs_elements){
        if (left_arr[i] == SUMFLAT && right_arr[j] == i){
            /* check forward */
            if (i < (int)lhs_elements.size() - 1)
                if (lhs_elements[i + 1].first.compare(lhs_elements[i].first) == 0) {

                    if (left_arr[i + 1] == EMPTYFLAT){
                        return RIGHT_EMPTY;
                    }
                    else if (left_arr[i + 1] == SUMFLAT){
                        return RIGHT_SUM;
                    }
                    else if (j + 1 < (int)rhs_elements.size()){
                        if (left_arr[i + 1] == j + 1 &&
                            right_arr[j + 1] == i + 1 &&
                            lhs_elements[i + 1].first.compare(lhs_elements[i + 1].first) == 0){
                            return RIGHT_EQUAL;
                        }
                    }
            }
            /* check backward */
            if (i > 0)
                if (lhs_elements[i - 1].first.compare(lhs_elements[i].first) == 0) {
                    if (left_arr[i - 1] == EMPTYFLAT){
                        return LEFT_EMPTY;
                    }
                    else if (left_arr[i - 1] == SUMFLAT)
                        return LEFT_SUM;
                    else if (startPos > 0 && i > 0){
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
            if (i < (int)lhs_elements.size() - 1 &&
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

    int theory_str::canBeOptimized_RHS(
            int i, int startPos, int j,
            std::vector<int> left_arr,
            std::vector<int> right_arr,
            std::vector<std::pair<std::string, int>> lhs_elements,
            std::vector<std::pair<std::string, int>> rhs_elements){
        if (right_arr[j] == SUMFLAT && left_arr[i] == j){
            /* check forward */
            if (j < (int)rhs_elements.size() - 1) {
                if (rhs_elements[j + 1].first.compare(rhs_elements[j].first) == 0) {
                    if (right_arr[j + 1] == EMPTYFLAT) {
                        return RIGHT_EMPTY;
                    } else if (right_arr[j + 1] == SUMFLAT)
                        return RIGHT_SUM;

                    else if (i + 1 < (int) lhs_elements.size()) {
                        if (left_arr[i + 1] == j + 1 &&
                            right_arr[j + 1] == i + 1 &&
                            rhs_elements[j + 1].first.compare(rhs_elements[j].first) == 0) {
                            return RIGHT_EQUAL;
                        }
                    }
                }
            }
            /* check backward */
            if (j > 0)
                if (rhs_elements[j - 1].first.compare(rhs_elements[j].first) == 0) {
                    if (right_arr[j - 1] == EMPTYFLAT){
                        return LEFT_EMPTY;
                    }
                    else if (right_arr[j - 1] == SUMFLAT)
                        return LEFT_SUM;
                    else if (startPos > 0){
                        if (left_arr[startPos - 1] == j - 1 &&
                            right_arr[j - 1] == startPos - 1 &&
                            rhs_elements[j - 1].first.compare(rhs_elements[j].first) == 0){
                            return LEFT_EQUAL;
                        }
                    }
            }
        }
        else if (left_arr[i] == j && right_arr[j] == i){
            /* check forward */
            if (i < (int)lhs_elements.size() - 1 &&
                left_arr[i + 1] != SUMFLAT &&
                lhs_elements[i + 1].first.compare(lhs_elements[i].first) == 0) {
                if (left_arr[i + 1] == EMPTYFLAT){
                    return RIGHT_EMPTY;
                }
                else if (j + 1 < rhs_elements.size()){
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
                    if (left_arr[startPos - 1] == j - 1 &&
                        right_arr[j - 1] == startPos - 1 &&
                        rhs_elements[startPos - 1].first.compare(rhs_elements[startPos].first) == 0){
                        return LEFT_EQUAL;
                    }
                }
            }
        }
        return NONE;
    }
    /*
     * First base case
     */
    void theory_str::setup_0_0_general(){
        std::vector<int> tmpLeft;
        std::vector<int> tmpRight;

        if (arrangements[std::make_pair(0, 0)].size() == 0) {
            /* left = right */
            tmpLeft.emplace_back(0);
            tmpRight.emplace_back(0);
            arrangements[std::make_pair(0, 0)].emplace_back(Arrangment(tmpLeft, tmpRight));
        }
    }

    /*
     * 2nd base case [0] = (sum rhs...)
     */
    void theory_str::setup_0_n_general(int lhs, int rhs){

        /* left always has SUMFLAT */
        std::vector<int> tmpLeft;
        tmpLeft.emplace_back(SUMFLAT);

        /* right has i number of 0 */
        std::vector<int> tmpRight;
        tmpRight.emplace_back(0);

        for (int i = 1 ; i < rhs; ++i){
            tmpRight.emplace_back(0);

            std::vector<Arrangment> tmp04;
            tmp04.emplace_back(Arrangment(tmpLeft, tmpRight));

            /* update */
            /* add directly without checking */
            if (arrangements[std::make_pair(0, i)].size() == 0) {
                arrangements[std::make_pair(0, i)] = tmp04;
            }
        }
    }

    /*
     * 2nd base case (sum lhs...) = [0]
     */
    void theory_str::setup_n_0_general(int lhs, int rhs){

        /* right always has SUMFLAT */
        std::vector<int> tmpRight;
        tmpRight.emplace_back(SUMFLAT);

        /* left has i number of 0 */
        std::vector<int> tmpLeft;
        tmpLeft.emplace_back(0);

        for (int i = 1; i < lhs; ++i) {
            tmpLeft.emplace_back(0);

            std::vector<Arrangment> tmp04;
            tmp04.emplace_back(Arrangment(tmpLeft, tmpRight));

            /* add directly without checking */
            if (arrangements[std::make_pair(i, 0)].size() == 0) {
                arrangements[std::make_pair(i, 0)] = tmp04;
            }
        }
    }

    /*
     * general case
     */
    void theory_str::setup_n_n_general(
            int lhs,
            int rhs){

        for (int i = 0 ; i < lhs; ++i)
            for (int j = 0; j < rhs; ++j)
                if (arrangements.find(std::make_pair(i,j)) == arrangements.end()){
                    /* 2.0 [i] = empty */
                    std::vector<Arrangment> tmp01_ext = arrangements[std::make_pair(i - 1, j)];
                    for (unsigned int t = 0 ; t < tmp01_ext.size(); ++t) {
                        tmp01_ext[t].addLeft(EMPTYFLAT);
                    }

                    /* 2.1 [j] = empty */
                    std::vector<Arrangment> tmp02_ext = arrangements[std::make_pair(i, j - 1)];
                    for (unsigned int t = 0 ; t < tmp02_ext.size(); ++t) {
                        tmp02_ext[t].addRight(EMPTYFLAT);
                    }

                    /* 3.1 [i] = sum(k...j) */
                    std::vector<Arrangment> tmp03;

                    {
                        /* [i] = sum (0..j) */
                        std::vector<int> tmpLeft;
                        for (int k = 0; k < i; ++k)
                            tmpLeft.emplace_back(EMPTYFLAT);
                        tmpLeft.emplace_back(SUMFLAT);

                        std::vector<int> tmpRight;
                        for (int k = 0 ; k <= j; ++k)
                            tmpRight.emplace_back(i);

                        SASSERT ((int)tmpLeft.size() == i + 1);
                        SASSERT ((int)tmpRight.size() == j + 1);
                        tmp03.emplace_back(Arrangment(tmpLeft, tmpRight));
                    }

                    /* [i] = sum (k..j) */
                    for (int k = 1; k < j; ++k) {
                        std::vector<Arrangment> tmp03_ext = arrangements[std::make_pair(i - 1, k - 1)];
                        for (unsigned int t = 0; t < tmp03_ext.size(); ++t) {

                            tmp03_ext[t].addLeft(SUMFLAT);
                            for (int tt = k; tt <= j; ++tt)
                                tmp03_ext[t].addRight(i);


                            SASSERT ((int)tmp03_ext[t].left_arr.size() == i + 1);
                            SASSERT ((int)tmp03_ext[t].right_arr.size() == j + 1);
                        }

                        tmp03.insert(tmp03.end(), tmp03_ext.begin(), tmp03_ext.end());
                    }

                    /* 3.2 right = sum(...left) */
                    std::vector<Arrangment> tmp04;

                    /* sum (k..i)  = [j] */
                    for (int k = 1; k < i; ++k) {
                        std::vector<Arrangment> tmp04_ext = arrangements[std::make_pair(k - 1, j - 1)];
                        for (unsigned int t = 0; t < tmp04_ext.size(); ++t) {
                            tmp04_ext[t].addRight(SUMFLAT);
                            for (int tt = k; tt <= i; ++tt)
                                tmp04_ext[t].addLeft(j);

                            SASSERT ((int)tmp04_ext[t].left_arr.size() == i + 1);
                            SASSERT ((int)tmp04_ext[t].right_arr.size() == j + 1);
                        }

                        tmp04.insert(tmp04.end(), tmp04_ext.begin(), tmp04_ext.end());
                    }

                    {
                        /* sum (0..i)  = [j] */
                        std::vector<int> tmpLeft;
                        for (int k = 0 ; k <= i; ++k)
                            tmpLeft.emplace_back(j);

                        std::vector<int> tmpRight;
                        for (int k = 0; k < j; ++k)
                            tmpRight.emplace_back(EMPTYFLAT);
                        tmpRight.emplace_back(SUMFLAT);

                        SASSERT ((int)tmpLeft.size() == i + 1);
                        SASSERT ((int)tmpRight.size() == j + 1);
                        tmp04.emplace_back(Arrangment(tmpLeft, tmpRight));
                    }

                    /* fourth case: left = right */
                    std::vector<Arrangment> tmp05 = arrangements[std::make_pair(i - 1, j - 1)];
                    for (unsigned int k = 0; k < tmp05.size(); ++k) {
                        tmp05[k].addRight(i);
                        tmp05[k].addLeft(j);
                    }

                    /* update */
                    /* add directly */
                    std::vector<Arrangment> possibleCases;
                    possibleCases.insert(possibleCases.end(), tmp03.begin(), tmp03.end());
                    possibleCases.insert(possibleCases.end(), tmp04.begin(), tmp04.end());
                    possibleCases.insert(possibleCases.end(), tmp05.begin(), tmp05.end());
                    arrangements[std::make_pair(i, j)] = possibleCases;
                }
    }

    std::vector<std::pair<std::string, int>> theory_str::vectorExpr2vectorStr(std::vector<std::pair<expr*, int>> v){
        std::vector<std::pair<std::string, int>> ret;
        for (unsigned i = 0; i < v.size(); ++i)
            ret.push_back(std::make_pair(expr2str(v[i].first), v[i].second));
        return ret;
    }

    std::string theory_str::expr2str(expr* node){
        std::stringstream ss;
        ast_manager &m = get_manager();
        ss << mk_pp(node, m);
        return ss.str();
    }

    /*
     * Create a general value that the component belongs to
     */
    std::string theory_str::sumStringVector(expr* node){
        if (is_app(node)) {
            app *ap = to_app(node);
            if (u.str.is_concat(ap)){
                ptr_vector<expr> list;
                get_nodes_in_concat(node, list);
                return sumStringVector(list);
            }
        }
        std::vector<expr*> list;
        list.push_back(node);
        return sumStringVector(list);
    }

    std::string theory_str::sumStringVector(ptr_vector<expr> list){
        std::string value = "";
        /* create a general value that the component belongs to */
        for (unsigned k = 0; k < list.size(); ++k)
            value = value + expr2str(list[k]) + " ";
        return value;
    }

    std::string theory_str::sumStringVector(std::vector<expr*> list){
        std::string value = "";
        /* create a general value that the component belongs to */
        for (unsigned k = 0; k < list.size(); ++k)
            value = value + expr2str(list[k]) + " ";
        return value;
    }

    /*
     * extra variables
     */
    std::vector<expr*> theory_str::create_set_of_flat_variables(int flatP, std::map<expr*, int> &non_fresh_vars, expr* root) {
        ast_manager &m = get_manager();
        std::vector<expr*> result;
        context & ctx   = get_context();

        for (int i = 0 ; i < flatP; ++i) {
            std::string varName = FLATPREFIX + std::to_string(noFlatVariables + i);
            expr_ref newVar(m);
            if (varMap_reverse.find(varName) == varMap_reverse.end()) {
                newVar = mk_str_var(varName);
                non_fresh_vars[newVar] = connectingSize;
                varMap_reverse[varName] = newVar;

                non_fresh_vars[root] = connectingSize;
            }
            else {
                newVar = varMap_reverse[varName];
                non_fresh_vars[newVar] = connectingSize;

                non_fresh_vars[root] = connectingSize;
            }

            result.emplace_back(newVar);

            std::string flatArr = generateFlatArray(std::make_pair(newVar.get(), 0));
            expr_ref v1(m);
            if (arrMap_reverse.find(flatArr) != arrMap_reverse.end()) {
                v1 = arrMap_reverse[flatArr];

                if (!ctx.e_internalized(v1.get())) {
                    ctx.internalize(v1, false);
                }
            }
            else {
                expr* arr_root = getExprVarFlatArray(root);
                if (arr_root != nullptr) {
                    v1 = arr_root;
                    arrMap_reverse[flatArr] = v1;
                }
                else {
                    v1 = mk_arr_var(flatArr);
                    arrMap_reverse[flatArr] = v1;
                }
            }

            arrMap[newVar.get()] = v1;

        }
        noFlatVariables = noFlatVariables + flatP;
        return result;
    }

    std::vector<std::pair<expr*, int>> theory_str::create_equality(expr* node, bool unfold){
        if (is_app(node)) {
            app *ap = to_app(node);
            if (u.str.is_concat(ap) && unfold){
                ptr_vector<expr> list;
                get_nodes_in_concat(node, list);
                return create_equality(list);
            }

        }
        std::vector<expr*> list;
        list.push_back(node);
        return create_equality(list, unfold);
    }

    std::vector<std::pair<expr*, int>> theory_str::create_equality(ptr_vector<expr> list, bool unfold){
        std::vector<expr*> l;
        expr* reg;
        for (unsigned i = 0; i < list.size(); ++i)
            if (!isInternalRegexVar(list[i], reg)){
                l.push_back(list[i]);
            }
            else {
                expr_ref_vector eqNodeSet(get_manager());
                collect_eq_nodes(list[i], eqNodeSet);
                bool found = false;

                for (int j = 0; j < eqNodeSet.size(); ++j) {
                    if (isInternalRegexVar(eqNodeSet[j].get(), reg)) {
                        l.push_back(eqNodeSet[j].get());
                        found = true;
                        break;
                    }
                }
                SASSERT(found);
            }
        return create_equality(l);
    }

    /*
     * Input: x . y
     * Output: flat . flat . flat . flat . flat . flat
     */
    std::vector<std::pair<expr*, int>> theory_str::create_equality(std::vector<expr*> list, bool unfold){
        std::vector<std::pair<expr*, int>> elements;
        expr* reg = nullptr;
        for (unsigned k = 0; k < list.size(); ++k) {
            STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(list[k], get_manager()) << std::endl;);
            zstring content;
            if (u.str.is_string(list[k], content)) {
                if (content.length() > 1) /* const string */ {
                    if (currVarPieces.find(list[k]) == currVarPieces.end())
                        currVarPieces[list[k]] = 0;
                    for (int j = currVarPieces[list[k]]; j < currVarPieces[list[k]] + p_bound.get_int64(); ++j) { /* split variables into p_bound.get_int64() parts */
                        elements.emplace_back(std::make_pair(list[k], -(j + 1)));
                    }
                    if (varPieces.find(list[k]) == varPieces.end() ||
                            (currVarPieces.find(list[k]) != currVarPieces.end() &&
                            currVarPieces[list[k]] >= varPieces[list[k]])){
                        create_internal_int_vars(list[k]);
                        varPieces[list[k]] += p_bound.get_int64();
                    }
                    else {
                        reuse_internal_int_vars(list[k]);
                    }
                    currVarPieces[list[k]] += p_bound.get_int64();
                }
                else if (content.length() == 1)
                    elements.emplace_back(std::make_pair(list[k], -1));
            }
            else if (u.re.is_star(list[k]) || u.re.is_plus(list[k]) || u.re.is_union(list[k]) ||
                (isInternalRegexVar(list[k], reg))){
                STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(list[k], get_manager()) << std::endl;);
                if (varPieces.find(list[k]) == varPieces.end() ||
                    (currVarPieces.find(list[k]) != currVarPieces.end() &&
                     currVarPieces[list[k]] >= varPieces[list[k]])){
                    create_internal_int_vars(list[k]);
                    varPieces[list[k]] += 1;
                }
                else {
                    reuse_internal_int_vars(list[k]);
                }
                elements.emplace_back(list[k], REGEX_CODE - currVarPieces[list[k]]);
                currVarPieces[list[k]] += 1;
            }
            else {
                STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(list[k], get_manager()) << "; bound = " << p_bound.get_int64() << std::endl;);
                // check if it is a regex var
                if (currVarPieces.find(list[k]) == currVarPieces.end())
                    currVarPieces[list[k]] = 0;
                for (int j = currVarPieces[list[k]]; j < currVarPieces[list[k]] + p_bound.get_int64(); ++j) { /* split variables into p_bound.get_int64() parts */
                    elements.emplace_back(std::make_pair(list[k], j));
                }

                if (varPieces.find(list[k]) == varPieces.end() ||
                    (currVarPieces.find(list[k]) != currVarPieces.end() &&
                     currVarPieces[list[k]] >= varPieces[list[k]])) {
                    create_internal_int_vars(list[k]);
                    varPieces[list[k]] += p_bound.get_int64();
                }
                else {
                    reuse_internal_int_vars(list[k]);
                }
                currVarPieces[list[k]] += p_bound.get_int64();
            }
        }
        return elements;
    }

    void theory_str::create_internal_int_vars(expr* v){
        ast_manager &m = get_manager();
        int start = varPieces[v];
        int end = varPieces[v] + p_bound.get_int64();
        expr* regex = nullptr;
        if (u.str.is_string(v)){
            start ++;
            end ++;
        }
        else {
            if (isInternalRegexVar(v, regex)) {
                STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " " << mk_pp(v, m)
                                   << std::endl;);
                if (u.re.is_union(regex)) {
                    start = REGEX_CODE - start;

                    std::string flatSize = generateFlatSize(std::make_pair(v, start), "");

                    expr_ref v1(mk_int_var(flatSize), m);
                    lenMap[v].push_back(v1);
                    std::vector<zstring> tmp;
                    collect_alternative_components(regex, tmp);
                    expr_ref_vector lenConstraints(m);
                    std::set<int> sizes;
                    for (int i = 0; i < tmp.size(); ++i) {
                        sizes.insert(tmp[i].length());
                    }
                    for (const auto& num : sizes)
                        lenConstraints.push_back(createEqualOperator(v1, mk_int(num)));

                    expr_ref ors(createOrOperator(lenConstraints), m);
                    assert_axiom(ors.get());
                    impliedFacts.push_back(ors);
                    return;
                } else if (u.re.is_star(regex) || u.re.is_plus(regex)) {
                    start = REGEX_CODE - start;

                    std::string flatIter = generateFlatIter(std::make_pair(v, start));

                    expr_ref v1(mk_strlen(v), m);
                    expr_ref v2(mk_int_var(flatIter), m);
                    lenMap[v].push_back(v1.get());
                    iterMap[v].push_back(v2.get());
                    zstring tmp = parse_regex_content(regex);
                    expr_ref_vector constraints(m);


                    if (u.re.is_star(v)) {
                        constraints.push_back(createGreaterEqOperator(v1, mk_int(0)));
                        constraints.push_back(createGreaterEqOperator(v2, mk_int(0)));
                    } else {
                        constraints.push_back(createGreaterEqOperator(v1, mk_int(1)));
                        constraints.push_back(createGreaterEqOperator(v2, mk_int(1)));
                    }

                    if (tmp.length() == 0)
                        constraints.push_back(createEqualOperator(v1, mk_int(0)));
                    else if (tmp.length() != 1 && tmp.encode().compare("uNkNoWn") != 0)
                        constraints.push_back(
                                createEqualOperator(v1, createMultiplyOperator(mk_int(tmp.length()), v2)));

                    expr_ref ands(createAndOperator(constraints), m);

                    assert_axiom(ands.get());
                    impliedFacts.push_back(ands);
                    return;
                }
            }
        }

        expr_ref_vector adds(m);
        for (int i = start; i < end; ++i) {
            std::string flatSize = generateFlatSize(std::make_pair(v, i), "");
            std::string flatIter = generateFlatIter(std::make_pair(v, i));

            expr_ref v1(mk_int_var(flatSize), m);
            expr_ref lenConstraint(createGreaterEqOperator(v1, m_autil.mk_int(0)), m);
            assert_axiom(lenConstraint.get());
            impliedFacts.push_back(lenConstraint);
            lenMap[v].push_back(v1);

            expr_ref v2(m);
            if (u.str.is_string(v))
                v2 = mk_int(1);
            else {
                v2 = mk_int_var(flatIter);
//                assert_axiom(createGreaterEqOperator(v2, m_autil.mk_int(0)));
                expr_ref iteConstraint(createEqualOperator(v2, m_autil.mk_int(1)), m);
                assert_axiom(iteConstraint.get());
                impliedFacts.push_back(iteConstraint);
                iterMap[v].push_back(v2);
            }
            adds.push_back(v1);
//            adds.push_back(createMultiplyOperator(v1, v2));
        }

        zstring val;
        if (u.str.is_string(v, val)){
            expr_ref sumConstraint(createEqualOperator(createAddOperator(adds), mk_int(val.length())), m);
            assert_axiom(sumConstraint.get());
            impliedFacts.push_back(sumConstraint);
        }
        else {
            expr_ref sumConstraint(createEqualOperator(createAddOperator(adds), u.str.mk_length(v)), m);
            assert_axiom(sumConstraint.get());
            impliedFacts.push_back(sumConstraint);

            if (string_int_vars.find(v) != string_int_vars.end()){
                setup_str_int_len(v, start);
            }
        }
    }

    void theory_str::setup_str_int_len(expr* e, int start){
        STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " " << mk_pp(e, get_manager() )
                           << std::endl;);
        expr* part1 = getExprVarFlatSize(std::make_pair(e, start));
        expr* part2 = getExprVarFlatSize(std::make_pair(e, start + 1));
        expr* len = mk_strlen(e);

        // len <= bound --> part 1 = 0
        expr* premise = createLessEqOperator(len, mk_int(str_int_bound));
        expr* conclusion = createEqualOperator(part1, mk_int(0));
        expr_ref to_assert(rewrite_implication(premise, conclusion), get_manager());
//        assert_axiom(to_assert);
//        impliedFacts.push_back(to_assert);

        // len >= bound --> part 2 = bound
        rational bound_1 = str_int_bound + rational(1);
        premise = createGreaterEqOperator(len, mk_int(bound_1));
        conclusion = createEqualOperator(part2, mk_int(str_int_bound));
        to_assert = rewrite_implication(premise, conclusion);
        assert_axiom(to_assert);
        impliedFacts.push_back(to_assert);
    }

    void theory_str::reuse_internal_int_vars(expr* v){
        ast_manager &m = get_manager();

        int start = currVarPieces[v];
        int end = currVarPieces[v] + p_bound.get_int64();
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(v, get_manager()) << " " << start << " " << end << std::endl;);
        if (u.str.is_string(v)){
            start ++;
            end ++;
        }
        else {
            expr* regex = nullptr;
            if (isInternalRegexVar(v, regex)) {
                STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " " << mk_pp(v, m)
                                   << std::endl;);
                if (u.re.is_union(regex)) {
                    start = REGEX_CODE - start;

                    expr_ref v1(getExprVarFlatSize(std::make_pair(v, start)), m);
                    std::vector<zstring> tmp_strs;
                    collect_alternative_components(regex, tmp_strs);
                    expr_ref_vector lenConstraints(m);
                    std::set<int> sizes;
                    for (int i = 0; i < tmp_strs.size(); ++i) {
                        sizes.insert(tmp_strs[i].length());
                    }

                    for (const auto& num : sizes)
                        lenConstraints.push_back(createEqualOperator(v1, mk_int(num)));

                    expr_ref ors(createOrOperator(lenConstraints), m);
                    assert_axiom(ors.get());
                    impliedFacts.push_back(ors);
                    return;
                } else if (u.re.is_star(regex) || u.re.is_plus(regex)) {
                    start = REGEX_CODE - start;

                    zstring tmp = parse_regex_content(regex);
                    STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " " << tmp << std::endl;);
                    expr_ref_vector constraints(m);

                    expr_ref v1(getExprVarFlatSize(std::make_pair(v, start)), m);
                    expr_ref v2(getExprVarFlatIter(std::make_pair(v, start)), m);
                    if (u.re.is_star(v)) {
                        constraints.push_back(createGreaterEqOperator(v1, mk_int(0)));
                        constraints.push_back(createGreaterEqOperator(v2, mk_int(0)));
                    } else {
                        constraints.push_back(createGreaterEqOperator(v1, mk_int(1)));
                        constraints.push_back(createGreaterEqOperator(v2, mk_int(1)));
                    }

                    if (tmp.length() == 0)
                        constraints.push_back(createEqualOperator(v1, mk_int(0)));
                    else if (tmp.length() != 1 && tmp.encode().compare("uNkNoWn") != 0)
                        constraints.push_back(
                                createEqualOperator(v1, createMultiplyOperator(mk_int(tmp.length()), v2)));

                    expr_ref ands(createAndOperator(constraints), m);

                    assert_axiom(ands.get());
                    impliedFacts.push_back(ands);
                    return;
                }
            }
        }

        expr_ref_vector adds(m);
        for (int i = start; i < end; ++i) {
            expr_ref v1(getExprVarFlatSize(std::make_pair(v, i)), m);
            expr_ref lenConstraint(createGreaterEqOperator(v1, m_autil.mk_int(0)), m);
            assert_axiom(lenConstraint.get());
            impliedFacts.push_back(lenConstraint);
            expr_ref v2(m);
            if (u.str.is_string(v))
                v2 = mk_int(1);
            else {
                v2 = iterMap[v][i];
                expr_ref iteConstraint(createEqualOperator(v2, m_autil.mk_int(1)), m);
                assert_axiom(iteConstraint.get());
                impliedFacts.push_back(iteConstraint);
            }
            adds.push_back(v1);
        }

        zstring val;
        if (u.str.is_string(v, val)){
            expr_ref sumConstraint(createEqualOperator(createAddOperator(adds), mk_int(val.length())), m);
            assert_axiom(sumConstraint.get());
            impliedFacts.push_back(sumConstraint);
        }
        else {
            expr_ref sumConstraint(createEqualOperator(createAddOperator(adds), u.str.mk_length(v)), m);
            assert_axiom(sumConstraint.get());
            impliedFacts.push_back(sumConstraint);
            if (string_int_vars.find(v) != string_int_vars.end()){
                setup_str_int_len(v, start);
            }
        }
    }

    std::vector<expr*> theory_str::set2vector(std::set<expr*> s){
        std::vector<expr*> v;
        v.insert(v.end(), s.begin(), s.end());
        return v;
    }

    /*
     *generateConstraint02
     */
    unsigned theory_str::findMaxP(std::vector<expr*> v){
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << std::endl;);
        unsigned maxLocal = 0;

        for (unsigned i = 0; i < v.size(); ++i)
            for (unsigned j = i + 1; j < v.size(); ++j){

                /* optimize: find longest common prefix and posfix */
                ptr_vector<expr> lhs;
                ptr_vector<expr> rhs;
                optimize_equality(v[i], v[j], lhs, rhs);

                unsigned cnt = 0;
                for (unsigned i = 0; i < lhs.size(); ++i) {
                    zstring value;
                    if (u.str.is_string(lhs[i], value)) {
                        if (value.length() > 0)
                            cnt++;
                    }
                    else
                        cnt++;
                }
                maxLocal = cnt > maxLocal ? cnt : maxLocal;

                cnt = 0;
                for (unsigned i = 0; i < rhs.size(); ++i) {
                    zstring value;
                    if (u.str.is_string(rhs[i], value)) {
                        if (value.length() > 0)
                            cnt++;
                    }
                    else
                        cnt++;
                }
                maxLocal = cnt > maxLocal ? cnt : maxLocal;
            }

        return maxLocal;
    }

    /*
     * cut the same prefix and suffix and check if var is still there
     */
    bool theory_str::check_var_after_optimizing(
            expr* lhs,
            expr* rhs,
            expr* var){
        /* cut prefix */
        ptr_vector<expr> lhsVec;
        get_nodes_in_concat(lhs, lhsVec);

        ptr_vector<expr> rhsVec;
        get_nodes_in_concat(rhs, rhsVec);

        /* cut prefix */
        int prefix = -1;
        for (int i = 0; i < std::min(lhsVec.size(), rhsVec.size()); ++i)
            if (are_equal_exprs(lhsVec[i], rhsVec[i]))
                prefix = i;
            else
                break;

        /* cut suffix */
        int suffix = -1;
        for (int i = 0; i < std::min(lhsVec.size(), rhsVec.size()); ++i)
            if (are_equal_exprs(lhsVec[lhsVec.size() - 1 - i], rhsVec[rhsVec.size() - 1 - i]))
                suffix = i;
            else
                break;

        for (int i = prefix + 1; i < (int)lhsVec.size() - suffix - 1; ++i)
            if (var == lhsVec[i])
                return true;

        for (int i = prefix + 1; i < (int)rhsVec.size() - suffix - 1; ++i)
            if (var == rhsVec[i])
                return true;

        return false;
    }

    /*
     * cut the same prefix and suffix
     */
    void theory_str::optimize_equality(
            expr* lhs,
            expr* rhs,
            ptr_vector<expr> &new_lhs,
            ptr_vector<expr> &new_rhs){
        ast_manager &m = get_manager();
        /* cut prefix */
        ptr_vector<expr> lhsVec;
        get_nodes_in_concat(lhs, lhsVec);

        ptr_vector<expr> rhsVec;
        get_nodes_in_concat(rhs, rhsVec);

        /* cut prefix */
        int prefix = -1;
        for (int i = 0; i < (int)std::min(lhsVec.size(), rhsVec.size()); ++i)
            if (are_equal_exprs(lhsVec[i], rhsVec[i]))
                prefix = i;
            else
                break;

        /* cut suffix */
        int suffix = -1;
        for (int i = 0; i < (int)std::min(lhsVec.size(), rhsVec.size()); ++i)
            if (are_equal_exprs(lhsVec[lhsVec.size() - 1 - i], rhsVec[rhsVec.size() - 1 - i]))
                suffix = i;
            else
                break;

        // create new concats
        for (int i = prefix + 1; i < (int)lhsVec.size() - suffix - 1; ++i)
            new_lhs.push_back(lhsVec[i]);

        for (int i = prefix + 1; i < (int)rhsVec.size() - suffix - 1; ++i)
            new_rhs.push_back(rhsVec[i]);
    }

    /*
     * cut the same prefix and suffix
     * return false if some inconsistence found
     */
    bool theory_str::propagate_equality(
            expr* lhs,
            expr* rhs,
            expr_ref_vector &impliedEqualities){
        ast_manager &m = get_manager();
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " \n" << mk_pp(lhs, m) << "\n" << mk_pp(rhs, m) <<std::endl;);
        /* cut prefix */
        ptr_vector<expr> lhsVec;
        get_nodes_in_concat(lhs, lhsVec);

        ptr_vector<expr> rhsVec;
        get_nodes_in_concat(rhs, rhsVec);

        expr_ref_vector andLhs(m);
        expr_ref_vector andRhs(m);
        /* cut prefix */
        int prefix = -1;

        zstring lValue, rValue;
        rational lenTmp;
        for (int i = 0; i < (int)std::min(lhsVec.size(), rhsVec.size()); ++i)
            if (are_equal_exprs(lhsVec[i], rhsVec[i])) {
                if (lhsVec[i] != rhsVec[i]) {
                    andLhs.push_back(createEqualOperator(lhsVec[i], rhsVec[i]));
                }
                prefix = i;
            }
            else if (u.str.is_string(lhsVec[i], lValue) && u.str.is_string(rhsVec[i], rValue)) {
                if (!lValue.prefixof(rValue) && !rValue.prefixof(lValue)) {
                    // thing goes wrong
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " goes wrong " << mk_pp(lhsVec[i], m) << " == " << mk_pp(rhsVec[i], m) << std::endl;);
                    negate_context(andLhs);
                    return false;
                }

                if (lValue == rValue)
                    prefix = i;
                else
                    break;
            }
            else if (have_same_len(lhsVec[i], rhsVec[i])){
                rational lenValue;
                get_len_value(lhsVec[i], lenValue);
                if (!u.str.is_string(lhsVec[i]))
                    andLhs.push_back(createEqualOperator(mk_strlen(lhsVec[i]), mk_int(lenValue)));
                if (!u.str.is_string(rhsVec[i]))
                    andLhs.push_back(createEqualOperator(mk_strlen(rhsVec[i]), mk_int(lenValue)));
                prefix = i;
                expr* tmp = rewrite_implication(createAndOperator(andLhs), createEqualOperator(lhsVec[i], rhsVec[i]));
                if (!impliedEqualities.contains(tmp))
                    impliedEqualities.push_back(tmp);
            }
            else if (u.str.is_string(lhsVec[i], lValue) && get_len_value(rhsVec[i], lenTmp) && lenTmp.get_int64() > 0){
                if (lValue.length() == lenTmp.get_int64()){
                    SASSERT(false);
                }
                else {
                    if (lValue.length() > lenTmp.get_int64()){
                        expr* const_str = mk_string(lValue.extract(0, lenTmp.get_int64()));
                        if (!are_equal_exprs(rhsVec[i], const_str)) {
                            andLhs.push_back(createEqualOperator(mk_strlen(rhsVec[i]), mk_int(lenTmp)));
                            expr *tmp_assert = rewrite_implication(
                                    createEqualOperator(mk_strlen(rhsVec[i]), mk_int(lenTmp)),
                                    createEqualOperator(rhsVec[i], const_str));
                            impliedEqualities.push_back(tmp_assert);
                            return true;
                        }
                        else
                            break;
                    }
                    else
                        break;
                }
            }
            else if (u.str.is_string(rhsVec[i], lValue) && get_len_value(lhsVec[i], lenTmp) && lenTmp.get_int64() > 0){
                if (lValue.length() == lenTmp.get_int64()){
                    SASSERT(false);
                }
                else {
                    if (lValue.length() > lenTmp.get_int64()){
                        expr* const_str = mk_string(lValue.extract(0, lenTmp.get_int64()));
                        if (!are_equal_exprs(lhsVec[i], const_str)) {
                            andLhs.push_back(createEqualOperator(mk_strlen(lhsVec[i]), mk_int(lenTmp)));
                            expr *tmp_assert = rewrite_implication(
                                    createEqualOperator(mk_strlen(lhsVec[i]), mk_int(lenTmp)),
                                    createEqualOperator(lhsVec[i], const_str));
                            impliedEqualities.push_back(tmp_assert);
                            return true;
                        }
                        else
                            break;
                    }
                    else
                        break;
                }
            }
            else
                break;

        /* cut suffix */
        int suffix = -1;
        for (int i = 0; i < (int)std::min(lhsVec.size(), rhsVec.size()); ++i)
            if (are_equal_exprs(lhsVec[lhsVec.size() - 1 - i], rhsVec[rhsVec.size() - 1 - i])) {
                if (lhsVec[lhsVec.size() - 1 - i] != rhsVec[rhsVec.size() - 1 - i])
                    andRhs.push_back(createEqualOperator(lhsVec[lhsVec.size() - 1 - i], rhsVec[rhsVec.size() - 1 - i]));
                suffix = i;
            }
            else if (u.str.is_string(lhsVec[lhsVec.size() - 1 - i], lValue) && u.str.is_string(rhsVec[rhsVec.size() - 1 - i], rValue)) {
                if (!lValue.suffixof(rValue) && !rValue.suffixof(lValue)) {
                    // thing goes wrong
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " goes wrong " << mk_pp(lhsVec[lhsVec.size() - 1 - i], m) << " == " << mk_pp(rhsVec[rhsVec.size() - 1 - i], m) << std::endl;);
                    negate_context(andRhs);
                    return false;
                }

                if (lValue == rValue)
                    suffix = i;
                else
                    break;
            }
            else if (have_same_len(lhsVec[lhsVec.size() - 1 - i], rhsVec[rhsVec.size() - 1 - i])){
                rational lenValue;
                get_len_value(lhsVec[lhsVec.size() - 1 - i], lenValue);
                if (!u.str.is_string(lhsVec[lhsVec.size() - 1 - i]))
                    andRhs.push_back(createEqualOperator(mk_strlen(lhsVec[lhsVec.size() - 1 - i]), mk_int(lenValue)));
                if (!u.str.is_string(rhsVec[rhsVec.size() - 1 - i]))
                    andRhs.push_back(createEqualOperator(mk_strlen(rhsVec[rhsVec.size() - 1 - i]), mk_int(lenValue)));
                suffix = i;
                expr* tmp = rewrite_implication(createAndOperator(andRhs), createEqualOperator(lhsVec[lhsVec.size() - 1 - i], rhsVec[rhsVec.size() - 1 - i]));
                if (!impliedEqualities.contains(tmp))
                    impliedEqualities.push_back(tmp);
            }
            else if (u.str.is_string(lhsVec[lhsVec.size() - 1 - i], lValue) && get_len_value(rhsVec[rhsVec.size() - 1 - i], lenTmp) && lenTmp.get_int64() > 0){
                if (lValue.length() == lenTmp.get_int64()){
                    SASSERT(false);
                }
                else {
                    if (lValue.length() > lenTmp.get_int64()){
                        expr* const_str = mk_string(lValue.extract(lValue.length() - lenTmp.get_int64(), lenTmp.get_int64()));
                        if (!are_equal_exprs(rhsVec[rhsVec.size() - 1 - i], const_str)) {
                            andLhs.push_back(
                                    createEqualOperator(mk_strlen(rhsVec[rhsVec.size() - 1 - i]), mk_int(lenTmp)));
                            expr *tmp_assert = rewrite_implication(
                                    createEqualOperator(mk_strlen(rhsVec[rhsVec.size() - 1 - i]), mk_int(lenTmp)),
                                    createEqualOperator(rhsVec[rhsVec.size() - 1 - i], const_str));
                            impliedEqualities.push_back(tmp_assert);
                            return true;
                        }
                        else
                            break;
                    }
                    else
                        break;
                }
            }
            else if (u.str.is_string(rhsVec[rhsVec.size() - 1 - i], lValue) && get_len_value(lhsVec[lhsVec.size() - 1 - i], lenTmp) && lenTmp.get_int64() > 0){
                if (lValue.length() == lenTmp.get_int64()){
                    SASSERT(false);
                }
                else {
                    if (lValue.length() > lenTmp.get_int64()){
                        expr* const_str = mk_string(lValue.extract(lValue.length() - lenTmp.get_int64(), lenTmp.get_int64()));
                        if (are_equal_exprs(lhsVec[lhsVec.size() - 1 - i], const_str)) {
                            andLhs.push_back(
                                    createEqualOperator(mk_strlen(lhsVec[lhsVec.size() - 1 - i]), mk_int(lenTmp)));
                            expr *tmp_assert = rewrite_implication(
                                    createEqualOperator(mk_strlen(lhsVec[lhsVec.size() - 1 - i]), mk_int(lenTmp)),
                                    createEqualOperator(lhsVec[lhsVec.size() - 1 - i], const_str));
                            impliedEqualities.push_back(tmp_assert);
                            return true;
                        }
                        else
                            break;
                    }
                    else
                        break;
                }
            }
            else
                break;

        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << std::endl;);

        // reach the end of equality
        if (prefix == std::min(lhsVec.size(), rhsVec.size()) - 1 || suffix == std::min(lhsVec.size(), rhsVec.size()) - 1)
            return true;

        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " prefix " << prefix << ", suffix " << suffix << ", len " << lhsVec.size() << std::endl;);
        andLhs.append(andRhs);

        if (lhsVec.size() == rhsVec.size()) {
            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " prefix " << prefix << ", suffix " << suffix << ", len " << lhsVec.size() << std::endl;);
            // only 1 var left
            if (prefix + 1 == (int)lhsVec.size() - suffix - 2)
                if (!are_equal_exprs(lhsVec[prefix + 1], rhsVec[prefix + 1])) {
                    expr* tmp = rewrite_implication(createAndOperator(andLhs), createEqualOperator(lhsVec[prefix + 1], rhsVec[prefix + 1]));
                    if (!impliedEqualities.contains(tmp))
                        impliedEqualities.push_back(tmp);
                }
        }
        else if (prefix >= 0 && prefix == (int)lhsVec.size() - 2 && prefix <= (int)rhsVec.size() - 3){
            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " prefix " << prefix << ", suffix " << suffix << ", len " << lhsVec.size() << std::endl;);
            // only 1 var left
            expr* concatTmp = create_concat_from_vector(rhsVec, prefix);
            if (!are_equal_exprs(lhsVec[prefix + 1], concatTmp)) {
                expr* tmp = rewrite_implication(createAndOperator(andLhs), createEqualOperator(lhsVec[prefix + 1], concatTmp));
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(tmp , m) << std::endl;);
                if (!impliedEqualities.contains(tmp))
                    impliedEqualities.push_back(tmp);
            }
        }
        else if (prefix >= 0 && prefix <= (int)lhsVec.size() - 3 && prefix == (int)rhsVec.size() - 2){
            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " prefix " << prefix << ", suffix " << suffix << ", len " << lhsVec.size() << std::endl;);
            // only 1 var left
            expr* concatTmp = create_concat_from_vector(lhsVec, prefix);
            if (!are_equal_exprs(rhsVec[prefix + 1], concatTmp)) {
                expr* tmp = rewrite_implication(createAndOperator(andLhs), createEqualOperator(rhsVec[prefix + 1], concatTmp));
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(tmp , m) << std::endl;);
                if (!impliedEqualities.contains(tmp))
                    impliedEqualities.push_back(tmp);
            }
        }
        return true;
    }


    expr* theory_str::create_concat_from_vector(ptr_vector<expr> v, int from_pos){
        expr* ret = v[v.size() - 1];
        for (int i = v.size() - 2; i > from_pos; --i) {
            ret = u.str.mk_concat(v[i], ret);
        }
        return ret;
    }

    bool theory_str::have_same_len(expr* lhs, expr* rhs){
        ast_manager &m = get_manager();
        rational lhsLen;
        if (get_len_value(lhs, lhsLen)) {
            rational rhsLen;
            if (get_len_value(rhs, rhsLen))
                if (rhsLen == lhsLen) {
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << mk_pp(lhs, m) << " = " << mk_pp(rhs, m) << std::endl;);
                    return true;
                }
        }
        return false;
    }

    /*
     * cut the same prefix and suffix
     */
    void theory_str::optimize_equality(
            expr* lhs,
            ptr_vector<expr> rhs,
            ptr_vector<expr> &new_lhs,
            ptr_vector<expr> &new_rhs){
        ast_manager &m = get_manager();
        /* cut prefix */
        ptr_vector<expr> lhsVec;
        get_nodes_in_concat(lhs, lhsVec);

        ptr_vector<expr> rhsVec;
        for (int i = 0; i < rhs.size(); ++i)
            rhsVec.push_back(rhs[i]);

        /* cut prefix */
        int prefix = -1;
        for (unsigned i = 0; i < std::min(lhsVec.size(), rhsVec.size()); ++i)
            if (are_equal_exprs(lhsVec[i], rhsVec[i]))
                prefix = i;
            else
                break;

        /* cut suffix */
        int suffix = -1;
        for (unsigned i = 0; i < std::min(lhsVec.size(), rhsVec.size()); ++i)
            if (are_equal_exprs(lhsVec[lhsVec.size() - 1 - i], rhsVec[rhsVec.size() - 1 - i]))
                suffix = i;
            else
                break;

        // create new concats
        for (unsigned i = prefix + 1; i < lhsVec.size() - suffix - 1; ++i)
            new_lhs.push_back(lhsVec[i]);

        for (unsigned i = prefix + 1; i < rhsVec.size() - suffix - 1; ++i)
            new_rhs.push_back(rhsVec[i]);
    }

    std::set<std::pair<expr*, int>> theory_str::collect_important_vars(){
        clock_t t = clock();
        ast_manager &m = get_manager();
        std::set<expr*> eqc_roots = get_eqc_roots();
        std::map<expr*, int> tmpResult;
        std::map<expr*, int> occurrences = countOccurrences_from_root(eqc_roots);
        for (const auto& nn : eqc_roots) {
            expr_ref_vector eqList(m);
            expr *value = collect_eq_nodes(nn, eqList);
            if (value == nullptr) {
                bool imp = false;
                int maxLen = 0;
                for (expr_ref_vector::iterator it = eqList.begin(); it != eqList.end(); ++it) {
                    int len = -1;
                    if (is_importantVar(*it, occurrences, len)) {
                        STRACE("str", tout << __LINE__ << "\t " << mk_pp(*it, m) << ": " << len << std::endl;);
                        imp = true;
                        maxLen = (maxLen == -1 || len == -1) ? -1 : (maxLen < len ? len : maxLen);
                    }
                }

                if (imp)
                    for (expr_ref_vector::iterator itor = eqList.begin(); itor != eqList.end(); ++itor) {
                        STRACE("str",
                               tout << __LINE__ << "\t \t" << mk_pp(nn, m) << " == " << mk_pp(*itor, m) << std::endl;);
                        tmpResult[*itor] = maxLen;
                    }
            }
        }

        collect_important_vars_str_int(tmpResult);

        for (const auto& nn : tmpResult)
            STRACE("str", tout << "\t "<< mk_pp(nn.first, m) << ": " << nn.second << std::endl;);

        std::set<std::pair<expr*, int>> ret;
        for (const auto& p : tmpResult)
            ret.insert(std::pair<expr *, int>(p.first, p.second));
        STRACE("str", tout << __LINE__ <<  " time: " << __FUNCTION__ << ":  " << ((float)(clock() - t))/CLOCKS_PER_SEC << std::endl;);
        return ret;
    }

    void theory_str::collect_important_vars_str_int(std::map<expr*, int> &vars){
        TRACE("str", tout << __LINE__ << " " << __FUNCTION__ << std::endl;);
        flat_enabled = false;
        if (string_int_conversion_terms.size() > 0) {
            string_int_vars.reset();
            int_string_vars.reset();
            ast_manager &m = get_manager();
            expr_ref_vector guessedEqs(m), guessedDisEqs(m);
            fetch_guessed_str_int_with_scopes(guessedEqs, guessedDisEqs);
            for (const auto &e : guessedEqs) {
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(e, get_manager())<< std::endl;);
                app* a = to_app(e);
                if (u.str.is_stoi(a->get_arg(0))){
                    expr* s = to_app(a->get_arg(0))->get_arg(0);
                    vars[s] = str_int_bound.get_int64();
                    update_string_int_vars(s, string_int_vars);
                    update_string_int_vars(a->get_arg(1), int_string_vars);
                }
                else if (u.str.is_itos(a->get_arg(0))){
                    expr* num = to_app(a->get_arg(0))->get_arg(0);
                    vars[a->get_arg(1)] = str_int_bound.get_int64();
                    update_string_int_vars(a->get_arg(1), string_int_vars);
                    update_string_int_vars(num, int_string_vars);
                }
                else if (u.str.is_stoi(a->get_arg(1))){
                    expr* s = to_app(a->get_arg(1))->get_arg(0);
                    vars[s] = str_int_bound.get_int64();
                    update_string_int_vars(s, string_int_vars);
                    update_string_int_vars(a->get_arg(0), int_string_vars);
                }
                else if (u.str.is_itos(a->get_arg(1))){
                    expr* num = to_app(a->get_arg(1))->get_arg(0);
                    vars[a->get_arg(0)] = str_int_bound.get_int64();
                    update_string_int_vars(a->get_arg(0), string_int_vars);
                    update_string_int_vars(num, int_string_vars);
                }
            }

            for (const auto &e : guessedDisEqs) {
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(e, get_manager())<< std::endl;);

                app* a = to_app(to_app(e)->get_arg(0));
                if (u.str.is_stoi(a->get_arg(0))){
                    expr* s = to_app(a->get_arg(0))->get_arg(0);
                    vars[s] = str_int_bound.get_int64();
                    update_string_int_vars(s, string_int_vars);
                    update_string_int_vars(a->get_arg(1), int_string_vars);
                }
                else if (u.str.is_itos(a->get_arg(0))){
                    expr* num = to_app(a->get_arg(0))->get_arg(0);
                    vars[a->get_arg(1)] = str_int_bound.get_int64();
                    update_string_int_vars(a->get_arg(1), string_int_vars);
                    update_string_int_vars(num, int_string_vars);
                }
                else if (u.str.is_stoi(a->get_arg(1))){
                    expr* s = to_app(a->get_arg(1))->get_arg(0);
                    vars[s] = str_int_bound.get_int64();
                    update_string_int_vars(s, string_int_vars);
                    update_string_int_vars(a->get_arg(0), int_string_vars);
                }
                else if (u.str.is_itos(a->get_arg(1))){
                    expr* num = to_app(a->get_arg(1))->get_arg(0);
                    vars[a->get_arg(0)] = str_int_bound.get_int64();
                    update_string_int_vars(a->get_arg(0), string_int_vars);
                    update_string_int_vars(num, int_string_vars);
                }
            }
        }

        if (vars.size() > 0)
            flat_enabled = true;
    }

    void theory_str::update_string_int_vars(expr* v, obj_hashtable<expr> &s){
        expr_ref_vector eqs(get_manager());
        collect_eq_nodes(v, eqs);
        for (const auto& n : eqs) {
            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << mk_pp(v, get_manager()) << " = " << mk_pp(n, get_manager()) << std::endl;);
            s.insert(n);
        }
    }

    bool theory_str::is_str_int_var(expr* e){
        return string_int_vars.contains(e);
    }

    void theory_str::refine_important_vars(
            std::set<std::pair<expr *, int>> &non_fresh_vars,
            std::set<expr*> &notImportant,
            std::map<expr *, std::set<expr *>> eq_combination) {
        std::map<expr *, int> retTmp;
        ast_manager & m = get_manager();
        context& ctx = get_context();
        notImportant.clear();
        for (const auto& nn : non_fresh_vars)
            STRACE("str", tout << __LINE__ << "\t "<< mk_pp(nn.first, m) << ": " << nn.second << std::endl;);

        std::map<expr*, int> str_int_vars;
        collect_important_vars_str_int(str_int_vars);

        for (const auto& nn : non_fresh_vars) {
            if (retTmp.find(nn.first) == retTmp.end()) {
                if (is_importantVar_recheck(nn.first, nn.second, eq_combination) || str_int_vars.find(nn.first) != str_int_vars.end()) {
                    expr_ref_vector eqs(m);
                    collect_eq_nodes(nn.first, eqs);
                    for (int i = 0; i < eqs.size(); ++i) {
                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(nn.first, m) << " --> "
                                           << mk_pp(eqs[i].get(), m) << std::endl;);
                        retTmp[eqs[i].get()] = nn.second;
                    }
                }
            }
        }

        for (const auto& nn : non_fresh_vars)
            if (retTmp.find(nn.first) == retTmp.end()){
                expr_ref_vector eqList(m);
                collect_eq_nodes(nn.first, eqList);
                for (int i = 0; i < eqList.size(); ++i) {
                    notImportant.insert(eqList[i].get());
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " not important " << mk_pp(eqList[i].get(), m) << std::endl;);
                }
            }

        std::map<expr*, int> occurrences = countOccurrences_from_combination(eq_combination);

        std::set<std::pair<expr *, int>> non_fresh_varsTmp;
        for (const auto& v : retTmp)
            if (notImportant.find(v.first) == notImportant.end() || str_int_vars.find(v.first) != str_int_vars.end()) {
                if (v.second == -1) {
                    expr* rootTmp = ctx.get_enode(v.first)->get_root()->get_owner();
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " consiering " << mk_pp(v.first, m) << " eq_combination size: " << eq_combination[rootTmp].size()
                                       << std::endl;);
                    if (!more_than_two_occurrences(rootTmp, occurrences) &&
                        eq_combination[rootTmp].size() <= 20 &&
                        !is_contain_equality(v.first) &&
                            str_int_vars.find(v.first) == str_int_vars.end()) {
                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " remove " << mk_pp(v.first, m)
                                           << std::endl;);
                        expr_ref_vector eqList(m);
                        collect_eq_nodes(v.first, eqList);
                        for (int i = 0; i < eqList.size(); ++i) {
                            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " not important " << mk_pp(eqList[i].get(), m) << std::endl;);
                            notImportant.insert(eqList[i].get());
                        }
                    } else
                        non_fresh_varsTmp.insert(std::make_pair(v.first, v.second));
                } else {
                    non_fresh_varsTmp.insert(std::make_pair(v.first, v.second));
                }
            }

        non_fresh_vars.clear();
        for (const auto& v : non_fresh_varsTmp)
            if (notImportant.find(v.first) == notImportant.end() || str_int_vars.find(v.first) != str_int_vars.end())
                non_fresh_vars.insert(std::make_pair(v.first, v.second));

        for (const auto& v : eq_combination)
            if (v.second.size() >= 6) {
                expr_ref_vector eqList(m);
                collect_eq_nodes(v.first, eqList);
                for (int i = 0; i < eqList.size(); ++i)
                    non_fresh_vars.insert(std::make_pair(eqList[i].get(), -1));
            }

        TRACE("str", tout << __LINE__ << __FUNCTION__ << std::endl;);
        for (const auto& nn : non_fresh_vars)
            STRACE("str", tout << "\t "<< mk_pp(nn.first, m) << ": " << nn.second << std::endl;);
    }

    bool theory_str::more_than_two_occurrences(expr* n, std::map<expr*, int> occurrences){
        expr_ref_vector eqs(get_manager());
        collect_eq_nodes(n, eqs);
        for (const auto& nn : eqs)
            if (occurrences[nn] >= 2)
                return true;

        return false;
    }

    /**
     * true if it is disequality, (non)membership
     * @param nn
     * @param len
     * @return
     */
    bool theory_str::is_importantVar(
            expr* nn,
            std::map<expr*, int> occurrences,
            int &len){
        ast_manager &m = get_manager();
        len = -1;
        // not equal to any concat/const
        expr_ref_vector eqList(m);
        expr *value = collect_eq_nodes(nn, eqList);
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": " << mk_pp(nn, m) << std::endl;);
        if (value != nullptr)
            return false;
        if (checkIfVarInUnionMembership(nn, len))
            return true;
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": " << mk_pp(nn, m) << std::endl;);
        if (collect_not_contains(nn))
            return true;
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": " << mk_pp(nn, m) << std::endl;);
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": " << mk_pp(nn, m) << " == " << len << std::endl;);
        std::vector<zstring> maxDiffStrs = collect_all_inequalities(nn);
        if (maxDiffStrs.size() > 0)
            len = maxDiffStrs[0].length();
        int maxCharAt = 0;
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": " << mk_pp(nn, m) << " == " << len << std::endl;);
//        if (collect_not_charAt(nn, maxCharAt)) {
//            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": " << mk_pp(nn, m) << " == " << len << std::endl;);
//            if (maxCharAt == -1) {
//                len = -1;
//                return true;
//            }
//            else if (maxCharAt > len){
//                len = maxCharAt;
//            }
//        }
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": " << mk_pp(nn, m) << " == " << len << std::endl;);
        if (len > 0) {
            zstring constPart = "";
            for (int i = 0; i < eqList.size(); ++i) {
                if (u.str.is_concat(eqList[i].get())) {
                    STRACE("str", tout << __LINE__ <<  "\t " << mk_pp(nn, m) << "  " << mk_pp(eqList[i].get(), m) << std::endl;);
                    ptr_vector<expr> nodeList;
                    get_nodes_in_concat(eqList[i].get(), nodeList);
                    zstring constPartTmp = "";
                    for (int j = 0; j < nodeList.size(); ++j) {
                        zstring valueStr;
                        bool has_eqc_value = false;
                        expr *constValue = get_eqc_value(nodeList[j], has_eqc_value);
                        if (has_eqc_value) {
                            u.str.is_string(constValue, valueStr);
                            constPartTmp = constPartTmp + valueStr;
                        }
                    }

                    if (constPartTmp.length() > constPart.length()) {
                        constPart = constPartTmp;
                    }
                }
            }

            STRACE("str", tout << __LINE__ <<  "\t " << mk_pp(nn, m) << " != " << len << std::endl;);
            STRACE("str", tout << __LINE__ <<  "\t " << constPart << " != " << std::endl;);
            bool allEqual = true;
            for (const auto& s : maxDiffStrs) {
                if (constPart != s) {
                    allEqual = false;
                }
            }

            if ((len > constPart.length() || (len == constPart.length() && allEqual)))
                return true;
        }

        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": " << mk_pp(nn, m) << " == " << len << std::endl;);
        len = -1;
        for (expr_ref_vector::iterator it = eqList.begin(); it != eqList.end(); ++it)
            if (u.str.is_concat(*it))
                return false;
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": " << mk_pp(nn, m) << " == " << len << std::endl;);
        // now we know it is a leaf node
        // --> check if their parents are fresh
        if (occurrences.find(nn) != occurrences.end())
            if (occurrences[nn] >= 2) {
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": " << mk_pp(nn, m) << " == " << len << std::endl;);
                return true;
            }
        return false;
    }

    std::map<expr*, int> theory_str::countOccurrences_from_root(std::set<expr*> eqc_roots){
        std::map<expr*, int> ret;
        for (const auto& n : concat_astNode_map){
            expr* arg0 = n.get_key1();
            expr* arg1 = n.get_key2();
            if (arg0 == arg1)
                ret[arg0] = 2;
            else {
                if (ret.find(arg0) != ret.end() && !isInternalVar(arg0))
                    ret[arg0]++;
                else
                    ret[arg0] = 1;
                if (ret.find(arg1) != ret.end() && !isInternalVar(arg0))
                    ret[arg1]++;
                else
                    ret[arg1] = 1;
            }
        }
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << std::endl;);
        for (const auto& p : ret)
            if (p.second >= 2)
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << mk_pp(p.first, get_manager()) << std::endl;);

        return ret;
    }

    std::map<expr*, int> theory_str::countOccurrences_from_combination(std::map<expr *, std::set<expr *>> eq_combination) {
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << std::endl;);
        std::map<expr*, int> ret;

        for (const auto& v : eq_combination){
            // inside one variable
            std::map<expr*, expr*> occurrenceLocation;
            if (!(v.second.size() >= 2 || u.str.is_string(v.first)))
                continue;

            for (const auto& e : v.second)
                if (u.str.is_concat(e)){
                    {
                        ptr_vector<expr> nodes;
                        get_nodes_in_concat(e, nodes);
                        for (int i  = 0; i < nodes.size(); ++i)
                            if (!u.str.is_string(nodes[i])){
                                if (ret.find(nodes[i]) != ret.end()){
                                    if (occurrenceLocation.find(nodes[i]) == occurrenceLocation.end()) {
                                        ret[nodes[i]]++;
                                        if (ret[nodes[i]] >= 2){
                                            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " var: " << mk_pp(nodes[i], get_manager()) <<  " @ " << mk_pp(e, get_manager()) << std::endl;);
                                        }
                                    }
                                    else {
                                        // compare two equalities
                                        if (check_var_after_optimizing(e, occurrenceLocation[nodes[i]], nodes[i])){
                                            ret[nodes[i]]++;
                                            if (ret[nodes[i]] >= 2){
                                                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " var: " << mk_pp(nodes[i], get_manager()) <<  " @ " << mk_pp(occurrenceLocation[nodes[i]], get_manager()) << " and @ " << mk_pp(e, get_manager()) << std::endl;);
                                            }
                                        }
                                    }

                                }

                                else {
                                    ret[nodes[i]] = 1;
                                    occurrenceLocation[nodes[i]] = e;
                                }
                            }
                    }
                }
        }
        return ret;
    }

    bool theory_str::checkIfVarInUnionMembership(expr* nn, int &len){
        for (const auto& we : membership_memo)
            if (we.first.get() == nn){
                if (u.re.is_star(we.second.get()) || u.re.is_star(we.second.get())) {
                    len = q_bound.get_int64();
                    return true;
                }
                else {
                    std::vector<expr*> components = collect_alternative_components(we.second);
                    int maxLenTmp = 0;
                    if (components.size() > 0) {
                        for (const auto &s : components) {
                            SASSERT(u.re.is_to_re(s));
                            zstring value;
                            u.str.is_string(to_app(s)->get_arg(0), value);
                            maxLenTmp = std::max((int) value.length(), maxLenTmp);
                        }
                        len = maxLenTmp;
                        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " " << mk_pp(nn, get_manager()) << " len: " << len << std::endl;);
                        return true;
                    }
                }
            }
        return false;
    }

    std::vector<zstring> theory_str::collect_all_inequalities(expr* nn){
        ast_manager &m = get_manager();
        int diffLen = 0;
        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " " << mk_pp(nn, m) << std::endl;);
        std::vector<zstring> maxDiffStrs;
        expr_ref_vector eqNodeSet(m);
        collect_eq_nodes(nn, eqNodeSet);
        for (const auto& we : m_wi_expr_memo){
            if (eqNodeSet.contains(we.first.get())){
                zstring value;
                if (u.str.is_string(we.second.get(), value))
                    if (!is_trivial_inequality(we.first.get(), value)){
                        if (diffLen < (int)value.length()) {
                            diffLen = (int) value.length();
                            maxDiffStrs.clear();
                            maxDiffStrs.push_back(value);
                            STRACE("str", tout << __LINE__ << "\t " << mk_pp(we.first.get(), m) << " != \"" << value << "\""
                                               << std::endl;);
                        }
                        else if (diffLen == (int)value.length()) {
                            STRACE("str", tout << __LINE__ << "\t " << mk_pp(we.first.get(), m) << " != \"" << value << "\""
                                               << std::endl;);
                            maxDiffStrs.push_back(value);
                        }
                    }
            }
            else if (eqNodeSet.contains(we.second.get())){
                zstring value;
                if (u.str.is_string(we.first.get(), value)) {
                    STRACE("str",
                           tout << __LINE__ << "\t " << mk_pp(we.second.get(), m) << " != \"" << value << "\"" << std::endl;);
                    if (!is_trivial_inequality(we.second.get(), value)) {
                        if (diffLen < (int) value.length()) {
                            diffLen = (int) value.length();
                            maxDiffStrs.clear();
                            maxDiffStrs.push_back(value);
                            STRACE("str",
                                   tout << __LINE__ << "\t " << mk_pp(we.second.get(), m) << " != \"" << value << "\""
                                        << std::endl;);
                        } else if (diffLen == (int) value.length()) {
                            STRACE("str",
                                   tout << __LINE__ << "\t " << mk_pp(we.second.get(), m) << " != \"" << value << "\""
                                        << std::endl;);
                            maxDiffStrs.push_back(value);
                        }
                    }
                }
            }
        }
        return maxDiffStrs;
    }

    expr* theory_str::create_conjuct_all_inequalities(expr* nn){
        ast_manager &m = get_manager();
        expr_ref_vector eqNodeSet(m);
        collect_eq_nodes(nn, eqNodeSet);
        expr_ref_vector ands(m);
        for (const auto& we : m_wi_expr_memo)
            if (eqNodeSet.contains(we.first.get()) || eqNodeSet.contains(we.second.get())){
                expr_ref tmp(mk_not(m, createEqualOperator(we.first.get(), we.second.get())), m);
                ands.push_back(tmp.get());
            }
        return createAndOperator(ands);
    }

    bool theory_str::is_trivial_inequality(expr* n, zstring s){
        if (s.length() == 0)
            return true;

        for (int i = 0; i < s.length(); ++i)
            if (sigmaDomain.find(s[i]) == sigmaDomain.end())
                return  true;

        rational lenVal, lowerBoundVal, upperBoundVal;
        if (get_len_value(n, lenVal) && lenVal != s.length())
            return true;

        if (lower_bound(n, lowerBoundVal) && lowerBoundVal > s.length())
            return true;

        if (upper_bound(n, upperBoundVal) && upperBoundVal < s.length())
            return true;
        return false;
    }

    bool theory_str::collect_not_contains(expr* nn){
        ast_manager &m = get_manager();
        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " " << mk_pp(nn, m) << std::endl;);
        std::vector<zstring> maxDiffStrs;
        for (const auto& we : m_wi_expr_memo){
            if (we.first.get() == nn){

                if (u.str.is_concat(we.second.get())){
                    expr* tmp = nullptr;
                    if (is_contain_equality(we.second.get(), tmp)){
                        zstring key;
                        if (u.str.is_string(tmp, key) && !is_trivial_contain(key)) {
                            STRACE("str",
                                   tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(tmp, m) << std::endl;);
                            return true;
                        }
                    }
                }
            }
            else if (we.second.get() == nn){

                if (u.str.is_concat(we.first.get())){
                    expr* tmp = nullptr;
                    if (is_contain_equality(we.first.get(), tmp)){
                        zstring key;
                        if (u.str.is_string(tmp, key) && !is_trivial_contain(key)) {
                            STRACE("str",
                                   tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(tmp, m) << std::endl;);
                            return true;
                        }
                    }
                }
            }
        }
        return false;
    }

    bool theory_str::collect_not_charAt(expr* nn, int &maxCharAt){
        ast_manager &m = get_manager();
        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " " << mk_pp(nn, m) << std::endl;);
        maxCharAt = 0;
        bool found = false;
        for (const auto& we : m_wi_expr_memo){
            if (u.str.is_at(we.first.get())) {
                expr* arg0 = to_app(we.first.get())->get_arg(0);
                if (arg0 == nn) {
                    expr *arg1 = to_app(we.first.get())->get_arg(1);
                    rational pos;
                    found = true;
                    if (get_arith_value(arg1, pos)) {
                        maxCharAt = std::max(maxCharAt, pos.get_int32());
                    }
                    else {
                        maxCharAt = -1;
                        return true;
                    }
                }
            }
            else if (u.str.is_at(we.second.get())) {
                expr* arg0 = to_app(we.second.get())->get_arg(0);
                if (arg0 == nn) {
                    expr *arg1 = to_app(we.second.get())->get_arg(1);
                    rational pos;
                    found = true;
                    if (get_arith_value(arg1, pos)) {
                        maxCharAt = std::max(maxCharAt, pos.get_int32());
                    }
                    else {
                        maxCharAt = -1;
                        return true;
                    }
                }
            }
        }
        maxCharAt += 1;
        return found;
    }

    bool theory_str::is_importantVar_recheck(
            expr* nn,
            int len,
            std::map<expr *, std::set<expr *>> combinations){
        ast_manager &m = get_manager();
        int diffLen = 0;
        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " " << mk_pp(nn, m) << " " << len << std::endl;);

        if (checkIfVarInUnionMembership(nn, len))
            return true;

        std::vector<zstring> maxDiffStrs = collect_all_inequalities(nn);
        if (maxDiffStrs.size() > 0)
            diffLen = maxDiffStrs[0].length();

        int maxCharAt = 0;
//        if (collect_not_charAt(nn, maxCharAt)) {
//            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": " << mk_pp(nn, m) << " == " << len << std::endl;);
//            if (maxCharAt == -1) {
//                return true;
//            }
//            else if (maxCharAt == len){
//                return true;
//            }
//            else
//                diffLen = maxCharAt;
//        }
        if (diffLen > 0) {
            context& ctx = get_context();
            std::vector<zstring> constParts;
            int constPartLen = 0;
            if (combinations.find(ctx.get_enode(nn)->get_root()->get_owner()) != combinations.end()) {
                for (const auto& concat : combinations[ctx.get_enode(nn)->get_root()->get_owner()]) {
                    ptr_vector<expr> nodeList;
                    get_nodes_in_concat(concat, nodeList);
                    zstring constPartTmp = "";
                    for (int j = 0; j < nodeList.size(); ++j) {
                        zstring valueStr;
                        bool has_eqc_value = false;
                        expr *constValue = get_eqc_value(nodeList[j], has_eqc_value);
                        if (has_eqc_value) {
                            u.str.is_string(constValue, valueStr);
                            constPartTmp = constPartTmp + valueStr;
                        }
                    }

                    if (constPartTmp.length() > constPartLen) {
                        constParts.clear();
                        constParts.push_back(constPartTmp);
                        constPartLen = (int)constPartTmp.length();
                        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " " << mk_pp(nn, m) << " " << constPartTmp << std::endl;);
                    }
                    else if (constPartTmp.length() == constPartLen) {
                        constParts.push_back(constPartTmp);
                    }
                }
            }

            if (constPartLen == diffLen) {
                for (const auto &s : maxDiffStrs) {
                    STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " diffstr: " << s << std::endl;);
                    for (const auto &ss : constParts) {
                        if (ss.operator==(s)) {
                            STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " " << ss << " == " << s << std::endl;);
                            if (u.str.is_concat(nn)) {
                                ptr_vector<expr> childrenVector;
                                get_nodes_in_concat(nn, childrenVector);
                                expr_ref_vector adds(m);
                                for (int i = 0; i < childrenVector.size(); ++i)
                                    adds.push_back(mk_strlen(childrenVector[i]));
                                expr_ref tmp(createGreaterEqOperator(createAddOperator(adds), mk_int(constPartLen + 1)), m);
                                expr* causes = create_conjuct_all_inequalities(nn);

//                                expr_ref tmpAssert(createEqualOperator(causes, tmp), m);
//                                assert_axiom(tmpAssert.get());
//                                uState.addAssertingConstraints(tmpAssert);
                            }
                            else {
                                expr_ref tmp(createGreaterEqOperator(mk_strlen(nn), mk_int(constPartLen + 1)), m);
                                expr* causes = create_conjuct_all_inequalities(nn);

//                                expr_ref tmpAssert(createEqualOperator(causes, tmp), m);
//                                assert_axiom(tmpAssert.get());
//                                uState.addAssertingConstraints(tmpAssert);
                            }
                        }
                    }
                }
                return false;
            }
        }
        else {
            if (len > 0)
                return false; // do not find inequalities
        } // difflen = 0

        return true;
    }



    void theory_str::print_all_assignments(){
        ast_manager &m = get_manager();
        context& ctx = get_context();
        (void) ctx;
        TRACE("str", tout << __FUNCTION__ << ": at level " << ctx.get_scope_level() << std::endl;);

        expr_ref_vector assignments(m);
        ctx.get_assignments(assignments);
        for (expr_ref_vector::iterator it = assignments.begin(); it != assignments.end(); ++it)
            STRACE("str", tout << "Assigned value " << mk_pp(*it, m) << std::endl;);
    }

    void theory_str::print_guessed_literals(){
        ast_manager &m = get_manager();
        context& ctx = get_context();
        (void) ctx;
        TRACE("str", tout << __FUNCTION__ << ": at level " << ctx.get_scope_level() << std::endl;);

        expr_ref_vector assignments(m);
        for (expr_ref_vector::iterator it = assignments.begin(); it != assignments.end(); ++it)
            STRACE("str", tout << "Assigned value " << mk_pp(*it, m) << std::endl;);
    }

    std::map<expr*, std::set<expr*>> theory_str::collect_inequalities_nonmembership(){
        ast_manager &m = get_manager();
        context& ctx = get_context();
        (void) ctx;

        sort* string_sort = u.str.mk_string_sort();
        std::map<expr*, std::set<expr*>> result;
        expr_ref_vector assignments(m);
        ctx.get_assignments(assignments);
        for (expr_ref_vector::iterator it = assignments.begin(); it != assignments.end(); ++it) {
            if (is_app(*it)){
                app *ap = to_app(*it);
                if (ap->get_num_args() == 1 && m.is_not(ap)){
                    // not something
                    if (is_app(ap->get_arg(0))){
                        app *app = to_app(ap->get_arg(0));
                        if (u.str.is_in_re(app)){
                            // a in b
                            expr* var = app->get_arg(0);
                            result[var].insert(ap->get_arg(0));
                        }
                        else if (m.is_eq(ap->get_arg(0))){

                            // a = b
                            expr* arg0 = app->get_arg(0);
                            expr* arg1 = app->get_arg(1);
                            if (m.get_sort(arg0) == string_sort) {
                                STRACE("str", tout << __FUNCTION__ << ": "<< mk_pp(*it, m) << std::endl;);
                                zstring strconst;
                                if (!u.str.is_string(arg0) && !u.str.is_string(arg1)) {
                                    result[arg0].insert(ap->get_arg(0));
                                    result[arg1].insert(ap->get_arg(0));
                                }
                                else if (u.str.is_string(arg0, strconst)){
                                    if (strconst.length() != 0 && is_var(arg1)){
                                        result[arg1].insert(ap->get_arg(0));
                                    }
                                }
                                else if (u.str.is_string(arg1, strconst)){
                                    if (strconst.length() != 0 && is_var(arg0)){
                                        result[arg0].insert(ap->get_arg(0));
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        STRACE("str", tout << __FUNCTION__ << ": DONE !" <<  std::endl;);
        for (const auto& it : result){
            STRACE("str", tout << __FUNCTION__ << ": not equal to " << mk_pp(it.first, m) << std::endl;);
            for (const auto& itor : it.second){
                STRACE("str", tout << __FUNCTION__ << ": " << mk_pp(itor, m) << std::endl;);
            }
        }
        return result;
    }

    std::map<expr*, std::set<expr*>> theory_str::normalize_eq(
            std::map<expr*, std::set<expr*>> &causes,
            std::set<expr*> &subNodes,
            std::set<std::pair<expr*, int>> &non_fresh_vars){
        clock_t t = clock();
        ast_manager &m = get_manager();
        context& ctx = get_context();
        (void) ctx;
        TRACE("str", tout << __FUNCTION__ << ": at level " << ctx.get_scope_level() << std::endl;);
        std::map<expr*, std::set<expr*>> combinations;
        std::set<expr*> eqc_roots;
        sort* string_sort = u.str.mk_string_sort();
        for (ptr_vector<enode>::const_iterator it = ctx.begin_enodes(); it != ctx.end_enodes(); ++it) {
            expr* owner = (*it)->get_root()->get_owner();
            if ((m.get_sort(owner)) == string_sort) {
                eqc_roots.insert(owner);
            }
        }

        for (const auto& node : eqc_roots){
            if (combinations.find(node) == combinations.end()){
                std::set<expr*> parents;
                extend_object(ctx.get_enode(node)->get_root()->get_owner(), combinations, causes, subNodes, parents, non_fresh_vars);
            }
        }
        STRACE("str", tout << __LINE__ <<  " time: " << __FUNCTION__ << ":  " << ((float)(clock() - t))/CLOCKS_PER_SEC << std::endl;);
        return refine_eq_combination(non_fresh_vars, combinations, subNodes);
    }

    std::map<expr*, std::set<expr*>> theory_str::refine_eq_combination(
            std::set<std::pair<expr*, int>> &non_fresh_vars,
            std::map<expr*, std::set<expr*>> combinations,
            std::set<expr*> subNodes
            ){
        TRACE("str", tout << __LINE__ << " " << __FUNCTION__ <<  std::endl;);
        std::map<expr*, std::set<expr*>> ret;
        expr* reg = nullptr;
        for (const auto& c : combinations){
            std::set<expr*> c_second = refine_eq_set(c.first, c.second, non_fresh_vars);
            bool important = is_important(c.first, non_fresh_vars);
            if (!important) {
                // the var is too complicated
                if (c_second.size() > 20) {
                    non_fresh_vars.insert(std::make_pair(c.first, -1));
                    ret[c.first] = c_second;
                }
                else if (subNodes.find(c.first) == subNodes.end() || u.str.is_string(c.first) || isInternalRegexVar(c.first, reg)) {
                    if (u.str.is_concat(c.first)) {
                        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << ": root concat node  " << mk_pp(c.first, get_manager()) << std::endl;);
                        // check if it is an important concat
                        bool importantConcat = false;
                        ptr_vector<expr> childrenVector;
                        get_all_nodes_in_concat(c.first, childrenVector);
                        for (const auto& v : non_fresh_vars)
                            if (childrenVector.contains(v.first)) {
                                importantConcat = true;
                                STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << ": important  " << mk_pp(v.first, get_manager()) << std::endl;);
                                break;
                            }

                        if (importantConcat)
                            ret[c.first] = c_second;
                        else {
                            STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << ": remove " << mk_pp(c.first, get_manager()) << " " << mk_pp(c.first, get_manager()) << std::endl;);
                            // remove c.first from the list
                            std::set<expr*> tmp;
                            for (const auto& cc : c_second)
                                if (cc != c.first){
                                    tmp.insert(cc);
                                }

                            if (tmp.size() >= 1)
                                ret[c.first] = tmp;
                        }
                    }
                    else {
                        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << ": root var node  " << mk_pp(c.first, get_manager()) << std::endl;);
                        ret[c.first] = c_second;
                    }

                }
                else
                    STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << ": remove " << mk_pp(c.first, get_manager()) << std::endl;);
            }
            else {
                STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << ": important node  " << mk_pp(c.first, get_manager()) << std::endl;);
                if (subNodes.find(c.first) == subNodes.end())
                    STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << ": root node  " << mk_pp(c.first, get_manager()) << std::endl;);
                ret[c.first] = c_second;
            }
        }
        return ret;
    }

    std::map<expr*, std::set<expr*>> theory_str::refine_eq_combination(
            std::set<std::pair<expr*, int>> &non_fresh_vars,
            std::map<expr*, std::set<expr*>> combinations,
            std::set<expr*> subNodes,
            std::set<expr*> notnon_fresh_vars
    ){
        TRACE("str", tout << __LINE__ << " " << __FUNCTION__ <<  std::endl;);
        ast_manager &m = get_manager();

        std::set<expr*> notnon_fresh_vars_filtered;
        for (const auto& n : notnon_fresh_vars) {
            STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << ": notnon_fresh_vars  " << mk_pp(n, m) << std::endl;);
            if (u.str.is_concat(n)){
                ptr_vector<expr> childrenVector;
                get_all_nodes_in_concat(n, childrenVector);

                bool shouldSkip = false;
                // if none of child nodes are not important
                for (const auto& nn : childrenVector)
                    if (is_important(nn, non_fresh_vars)){
                        shouldSkip = true;
                        break;
                    }
                if (!shouldSkip)
                    notnon_fresh_vars_filtered.insert(n);
            }
            else
                notnon_fresh_vars_filtered.insert(n);
        }

        std::set<expr*> toRemove;

        std::map<expr*, std::set<expr*>> ret;
        for (const auto& c : combinations){
            STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " handling " << mk_pp(c.first, get_manager()) << std::endl;);
            if (is_trivial_combination(c.first, c.second, non_fresh_vars))
                continue;
            STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " handling " << mk_pp(c.first, get_manager()) << std::endl;);
            std::set<expr*> tmpSet = refine_eq_set(c.first, c.second, non_fresh_vars, notnon_fresh_vars_filtered);
            // remove some imp vars
            if (c.second.size() > 20 && tmpSet.size() <= 20) {
                expr_ref_vector eqs(m);
                collect_eq_nodes(c.first, eqs);
                for (const auto& v : eqs)
                    toRemove.insert(v);
            }
            bool important = is_important(c.first, non_fresh_vars);
            if (!important) {

                STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " handling " << mk_pp(c.first, get_manager()) << std::endl;);
                if (tmpSet.size() > 20) {
                    non_fresh_vars.insert(std::make_pair(c.first, -1));
                    ret[c.first] = tmpSet;
                }
                else if (subNodes.find(c.first) == subNodes.end()) {
                    if (u.str.is_concat(c.first)) {
                        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << ": root node  " << mk_pp(c.first, get_manager()) << std::endl;);
                        // check if it is an important concat
                        ptr_vector<expr> childrenVector;
                        get_all_nodes_in_concat(c.first, childrenVector);
                        for (const auto& v : non_fresh_vars)
                            if (childrenVector.contains(v.first)) {
                                STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << ": important  " << mk_pp(v.first, get_manager()) << std::endl;);
                                break;
                            }

                        if (is_important_concat(c.first, non_fresh_vars))
                            ret[c.first] = tmpSet;
                        else {
                            STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << ": remove " << mk_pp(c.first, get_manager()) << " " << mk_pp(c.first, get_manager()) << std::endl;);
                            // remove c.first from the list
                            std::set<expr*> tmp;
                            for (const auto& cc : tmpSet)
                                if (cc != c.first){
                                    tmp.insert(cc);
                                }
                            ret[c.first] = tmp;
                        }
                    }
                    else
                        ret[c.first] = tmpSet;
                }
                else
                    STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << ": remove " << mk_pp(c.first, get_manager()) << std::endl;);
            }
            else {
                ret[c.first] = tmpSet;
            }
        }

        //update non_fresh_vars
        std::set<std::pair<expr*, int>> tmp;
        for (const auto& v : non_fresh_vars)
            if (toRemove.find(v.first) != toRemove.end() && v.second == -1) {

            }
            else
                tmp.insert(std::make_pair(v.first, v.second));

        non_fresh_vars.clear();
        non_fresh_vars = tmp;
        TRACE("str", tout << __FUNCTION__ << std::endl;);
        for (const auto& nn : non_fresh_vars)
            STRACE("str", tout << "\t "<< mk_pp(nn.first, m) << ": " << nn.second << std::endl;);
        return ret;
    }

    bool theory_str::is_important_concat(expr* e, std::set<std::pair<expr*, int>> non_fresh_vars){
        ptr_vector<expr> childrenVector;
        get_all_nodes_in_concat(e, childrenVector);
        for (const auto& v : non_fresh_vars)
            if (childrenVector.contains(v.first)) {
                STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << ": important  " << mk_pp(v.first, get_manager()) << std::endl;);
                return true;
            }
        return false;
    }

    /*
     * size = 0 or size = 1 && trivial equal
     */
    bool theory_str::is_trivial_combination(expr* v, std::set<expr*> eq, std::set<std::pair<expr*, int>> non_fresh_vars){
        if (eq.size() == 0)
            return true;

        if (is_important(v, non_fresh_vars)) {
            if (eq.size() == 1) {
                // if it is equal to itself only
                expr_ref_vector eqs(get_manager());
                collect_eq_nodes(v, eqs);
                if (eqs.size() == 1)
                    return true;
            }
            return false;
        }

        if (eq.size() == 1 && v == *(eq.begin()))
            return true;

        if (eq.size() == 1 && is_trivial_eq_concat(v, *(eq.begin()))) {
            ptr_vector<expr> v1;
            get_nodes_in_concat(v, v1);

            ptr_vector<expr> v2;
            get_nodes_in_concat(*(eq.begin()), v2);
            if (v1.size() == v2.size())
                return true;
        }

        return false;
    }

    std::set<expr*> theory_str::refine_eq_set(
            expr* var,
            std::set<expr*> s,
            std::set<std::pair<expr*, int>> non_fresh_vars,
            std::set<expr*> notnon_fresh_vars){
        TRACE("str", tout << __LINE__ << " " << __FUNCTION__ <<  std::endl;);
        ast_manager &m = get_manager();
        s = refine_all_duplications(s);
        std::set<expr*> ret;
        for (std::set<expr*>::iterator it = s.begin(); it != s.end(); ++it) {
            if (u.str.is_concat(*it)) {
                ptr_vector<expr> childrenVector;
                get_all_nodes_in_concat(*it, childrenVector);

                bool notAdd = false;

                if (are_equal_exprs(var, *it)) {
                    // do not have const or important var
                    bool found = false;
                    ptr_vector<expr> v;
                    get_nodes_in_concat(*it, v);
                    for (const auto& nn : v)
                        if (u.str.is_string(nn) || is_important(nn, non_fresh_vars)){
                            found = true;
                            break;
                        }
                    if (found)
                        notAdd = false;
                    else
                        notAdd = true;
                }
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ <<  std::endl;);
                // check if it contains a nonimportantVar
                if (!notAdd) {
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ <<  std::endl;);
//                    for (const auto &notimp : notnon_fresh_vars)
//                        if (childrenVector.contains(notimp)) {
//                            notAdd = true;
//                            if (!appear_in_eqs(ret, notimp)) {
//                                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": add " << mk_pp(*it, m)
//                                                   << " because of " << mk_pp(notimp, m) << std::endl;);
//                                notAdd = false;
//                                break;
//                            }
//                        }
                    for (const auto &notimp : notnon_fresh_vars)
                        if (childrenVector.contains(notimp)) {
                            notAdd = true;
                            if (!appear_in_eqs(ret, notimp)) {
                                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": add " << mk_pp(*it, m)
                                                   << " because of " << mk_pp(notimp, m) << std::endl;);
                                notAdd = false;
                                break;
                            }
                        }
                }

                if (!notAdd)
                    ret.insert(*it);
            }
            else if (is_important(*it, non_fresh_vars)  || u.str.is_string(*it))
                ret.insert(*it);
        }

        if (ret.size() == 1 && !is_important(var, non_fresh_vars)) {
            // check if none of variable is really important
            ptr_vector<expr> v;
            get_all_nodes_in_concat(*ret.begin(), v);
            bool shouldKeep = false;
            for (const auto& nn : v) {
                int tmp;
                if (is_important(nn, non_fresh_vars, tmp) && tmp == -1){
                    if (u.str.is_string(var)){
                        shouldKeep = true;
                        break;
                    }
                }
            }

            if (!shouldKeep)
                ret.clear();
        }
        return ret;
    }

    std::set<expr*> theory_str::refine_eq_set(
            expr* var,
            std::set<expr*> s,
            std::set<std::pair<expr*, int>> non_fresh_vars){
        TRACE("str", tout << __LINE__ << " " << __FUNCTION__ <<  std::endl;);
        s = refine_all_duplications(s);
        std::set<expr*> ret;
        for (std::set<expr*>::iterator it = s.begin(); it != s.end(); ++it) {
            if (u.str.is_concat(*it)) {
                ptr_vector<expr> childrenVector;
                get_all_nodes_in_concat(*it, childrenVector);

                bool notAdd = false;

                if (are_equal_exprs(var, *it)) {
                    // do not have const or important var
                    bool found = false;
                    ptr_vector<expr> v;
                    get_nodes_in_concat(*it, v);
                    for (const auto& nn : v)
                        if (u.str.is_string(nn) || is_important(nn, non_fresh_vars)){
                            found = true;
                            break;
                        }
                    if (found)
                        notAdd = false;
                    else
                        notAdd = true;
                }

                if (!notAdd)
                    ret.insert(*it);
            }
            else if (is_important(*it, non_fresh_vars)  || u.str.is_string(*it))
                ret.insert(*it);
        }

        if (ret.size() == 1 && !is_important(var, non_fresh_vars)) {
            // check if none of variable is really important
            ptr_vector<expr> v;
            get_all_nodes_in_concat(*ret.begin(), v);
            bool shouldKeep = false;
            for (const auto& nn : v) {
                int tmp;
                if (is_important(nn, non_fresh_vars, tmp) && tmp == -1){
                    if (u.str.is_string(var)){
                        shouldKeep = true;
                        break;
                    }
                }
            }

            if (!shouldKeep)
                ret.clear();
        }

        // check all pairs to see if they have the same role
//        std::vector<expr*> v = set2vector(ret);
//        ret.clear();
//        for (int i = 0; i < v.size(); ++i) {
//            if (u.str.is_concat(v[i])) {
//                ptr_vector<expr> nodes_i;
//                get_nodes_in_concat(v[i], nodes_i);
//                bool add = true;
//                for (int j = i + 1; j < v.size(); ++j) {
//                    ptr_vector<expr> nodes_j;
//                    get_nodes_in_concat(v[j], nodes_j);
//                    if (nodes_i.size() == nodes_j.size())
//                        if (same_role(nodes_i, nodes_j)){
//                            add = false;
//                            break;
//                        }
//                }
//
//                if (add)
//                    ret.insert(v[i]);
//            }
//            else
//                ret.insert(v[i]);
//        }
        return ret;
    }

    /*
     * 2 nodes have same role or not
     * if they are both concat funcs
     *      all elements have the same role
     * if they are both variables
     *      vars have the same bound, same eq, same diseq, same contains
     */
//    bool theory_str::same_role(expr* node_i, expr* node_j){
//        if (u.str.is_concat(node_i) && u.str.is_concat(node_j)){
//            ptr_vector<expr> nodes_i;
//            get_nodes_in_concat(node_i, nodes_i);
//            ptr_vector<expr> nodes_j;
//            get_nodes_in_concat(node_j, nodes_j);
//            if (nodes_i.size() == nodes_j.size()){
//                for (int k = 0; k < nodes_i.size(); ++k)
//                    if (!same_role(nodes_i[k], nodes_j[k]))
//                        return false;
//            }
//            else
//                return false;
//        }
//        else if (u.str.is_concat(node_i) || u.str.is_concat(node_j)){
//            return false;
//        }
//        else if (!isInternalVar(node_i) && !isInternalVar(node_j)){
//            //
//            rational lb_i, lb_j;
//            lower_bound(node_i, lb_i);
//            lower_bound(node_i, lb_i);
//
//        }
//    }

    std::set<expr*> theory_str::refine_all_duplications(std::set<expr*> s) {
        if (s.size() == 1)
            return s;
        std::vector<expr *> v;
        for (const auto &n : s) {
            v.push_back(n);
        }

        s.clear();
        for (int i = 0; i < v.size(); ++i) {
            bool eq = false;
            for (int j = i + 1; j < v.size(); ++j)
                if (are_equal_concat(v[i], v[j])) {
                    STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << ": remove " << mk_pp(v[i], get_manager()) << " " << mk_pp(v[j], get_manager()) << std::endl;);
                    eq = true;
                    break;
                }

            if (!eq)
                s.insert(v[i]);
            else {
                STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << ": remove " << mk_pp(v[i], get_manager()) << std::endl;);
            }
        }
        return s;
    }

    bool theory_str::are_equal_concat(expr* lhs, expr* rhs){
        ptr_vector<expr> vLhs;
        get_nodes_in_concat(lhs, vLhs);

        ptr_vector<expr> vRhs;
        get_nodes_in_concat(rhs, vRhs);

        if (vLhs.size() == vRhs.size()) {
            for (int i = 0; i < vLhs.size(); ++i)
                if (!are_equal_exprs(vLhs[i], vRhs[i]))
                    return false;
        }
        else
            return false;
        return true;
    }

    /*
     * true if var does appear in eqs
     */
    bool theory_str::appear_in_eqs(std::set<expr*> s, expr* var){
        for (const auto& eq : s)
            if (u.str.is_concat(eq)) {
                ptr_vector<expr> childrenVector;
                get_all_nodes_in_concat(eq, childrenVector);
                if (childrenVector.contains(var))
                    return true;
            }
        return false;
    }

    bool theory_str::appear_in_all_eqs(std::set<expr*> s, expr* var){
        for (const auto& eq : s)
            if (u.str.is_concat(eq)) {
                ptr_vector<expr> childrenVector;
                get_all_nodes_in_concat(eq, childrenVector);
                if (!childrenVector.contains(var))
                    return false;
            }
        return true;
    }

    /*
     * true if it has subvars
     */
    bool theory_str::has_sub_var(expr* var){
        ast_manager &m = get_manager();
        expr_ref_vector eqs(m);
        collect_eq_nodes(var, eqs);
        for (const auto& eq_imp : eqs){
            if (u.str.is_concat(eq_imp)) {
                return true;
            }
        }
        return false;
    }

    std::set<expr*> theory_str::refine_eq_set(
            std::set<expr*> s,
            std::set<std::pair<expr*, int>> non_fresh_vars){
        TRACE("str", tout << __LINE__ << " " << __FUNCTION__ <<  std::endl;);
        ast_manager &m = get_manager();
        std::set<expr*> ret;
        for (std::set<expr*>::iterator it = s.begin(); it != s.end(); ++it) {
            if (u.str.is_concat(*it)) {
                expr* arg0 = to_app(*it)->get_arg(0);
                expr_ref_vector eq0(m);
                collect_eq_nodes(arg0, eq0);
                bool imp0 = is_important(arg0, non_fresh_vars);

                expr* arg1 = to_app(*it)->get_arg(1);
                expr_ref_vector eq1(m);
                collect_eq_nodes(arg1, eq1);
                bool imp1 = is_important(arg1, non_fresh_vars);
                STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << ": checking " << mk_pp(arg0, m) << " " << mk_pp(arg1, m) << std::endl;);
                bool notAdd = false;
                if (!imp0 && !u.str.is_concat(arg0) && !u.str.is_string(arg0)) {
                    for (std::set<expr *>::iterator i = s.begin(); i != s.end(); ++i) {
                        if (u.str.is_concat(*i) && (*i) != (*it)) {
                            expr *arg00 = to_app(*i)->get_arg(0);
                            expr *arg01 = to_app(*i)->get_arg(1);
                            if (arg1 == arg01 && eq0.contains(arg00)) {
                                STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << ": eq with " << mk_pp(arg0, m) << " " << mk_pp(arg00, m) << std::endl;);
                                notAdd = true;
                                break;
                            }
                        }
                    }
                }

                if (!imp1 && !u.str.is_concat(arg1) && !u.str.is_string(arg1)){
                    for (std::set<expr *>::iterator i = s.begin(); i != s.end(); ++i) {
                        if (u.str.is_concat(*i) && (*i) != (*it)) {
                            expr *arg00 = to_app(*i)->get_arg(0);
                            expr *arg01 = to_app(*i)->get_arg(1);
                            if (arg0 == arg00 && eq1.contains(arg01)) {
                                STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << ": eq with " << mk_pp(arg1, m) << " " << mk_pp(arg01, m) << std::endl;);
                                notAdd = true;
                                break;
                            }
                        }
                    }
                }

                if (notAdd == false)
                    ret.insert(*it);
            }
        }
        return ret;
    }

    bool theory_str::is_important(expr *n, std::set<std::pair<expr*, int>> non_fresh_vars) {
        for (const auto& p : non_fresh_vars){
            if (p.first == n){
                return true;
            }
        }
        return false;
    }

    bool theory_str::is_important(expr *n, std::set<std::pair<expr*, int>> non_fresh_vars, int &l) {
        for (const auto& p : non_fresh_vars){
            if (p.first == n){
                l = p.second;
                return true;
            }
        }
        return false;
    }

    std::set<expr*> theory_str::extend_object(
            expr* object,
            std::map<expr*, std::set<expr*>> &combinations,
            std::map<expr*, std::set<expr*>> &causes,
            std::set<expr*> &subNodes,
            std::set<expr*> parents,
            std::set<std::pair<expr*, int>> non_fresh_vars){
        if (combinations[object].size() != 0)
            return combinations[object];

        ast_manager &m = get_manager();
        context& ctx = get_context();
        TRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": " << mk_pp(object, m) << std::endl;);
        if (parents.size() > 0) {
            for (const auto &p : parents)
                STRACE("str", tout << " --> " << mk_pp(p, m););
            STRACE("str", tout << std::endl;);
        }

        std::set<expr*> result;
        expr_ref_vector eqNodeSet(m);
        expr* constValue = collect_eq_nodes(object, eqNodeSet);
        object = ctx.get_enode(object)->get_root()->get_owner();


        if (constValue != nullptr) {
            result.insert(constValue);

            if (object != constValue) {
                expr_ref tmp(ctx.mk_eq_atom(object, constValue), m);
                ctx.internalize(tmp, false);
                causes[object].insert(tmp);
            }
        }

        std::set<expr *> eqConcat;
        // refine concat: a . b = c . d && a = c && b = d
        expr_ref_vector refined_eqNodeSet(m);
        for (expr_ref_vector::iterator it = eqNodeSet.begin(); it != eqNodeSet.end(); ++it) {
            if (u.str.is_concat(*it) && *it != object) {
                // get lhs
                expr_ref_vector eqLhsSet(m);
                collect_eq_nodes(to_app(*it)->get_arg(0), eqLhsSet);

                expr_ref_vector eqRhsSet(m);
                collect_eq_nodes(to_app(*it)->get_arg(1), eqRhsSet);

                bool found = false;
                for (expr_ref_vector::iterator itor = refined_eqNodeSet.begin();
                     itor != refined_eqNodeSet.end(); ++itor) {
                    expr* lhs = to_app(*itor)->get_arg(0);
                    expr* rhs = to_app(*itor)->get_arg(1);

                    if (eqLhsSet.contains(lhs) && eqRhsSet.contains(rhs)) {
                        found = true;
                        break;
                    }
                }

                if (!found)
                    refined_eqNodeSet.push_back(*it);
            }
            else if (u.str.is_concat(*it) && *it == object)
                refined_eqNodeSet.push_back(*it);
        }

        for (expr_ref_vector::iterator it = refined_eqNodeSet.begin(); it != refined_eqNodeSet.end(); ++it) {
            if (u.str.is_concat(*it)) {

                if (object != *it) {
                    expr_ref tmp(ctx.mk_eq_atom(object, *it), m);
                    ctx.internalize(tmp, false);
                    causes[object].insert(tmp);
                }
                // get lhs
                expr* arg0 = ctx.get_enode(to_app(*it)->get_arg(0))->get_root()->get_owner();
                expr* arg1 = ctx.get_enode(to_app(*it)->get_arg(1))->get_root()->get_owner();

                add_subnodes(arg0, arg1, subNodes);

                STRACE("str", tout << __LINE__ << " " << mk_pp(arg0, m) << " . " << mk_pp(arg1, m) << std::endl;);
                std::set<expr *> eqLhs;
                if (parents.find(arg0) == parents.end()) {
                    STRACE("str", tout << __LINE__ << " tracing lhs " << mk_pp(arg0, m) << std::endl;);
                    std::set<expr*> lhsParents;
                    lhsParents.insert(parents.begin(), parents.end());
                    lhsParents.insert(arg0);
                    eqLhs = extend_object(arg0, combinations, causes, subNodes, lhsParents, non_fresh_vars);
                }
                else {
                    eqLhs.insert(arg0);
                }

                // get rhs
                std::set<expr *> eqRhs;
                if (parents.find(arg1) == parents.end()) {
                    STRACE("str", tout << __LINE__ << " tracing rhs " << mk_pp(arg1, m) << std::endl;);
                    std::set<expr*> rhsParents;
                    rhsParents.insert(parents.begin(), parents.end());
                    rhsParents.insert(arg1);
                    eqRhs = extend_object(arg1, combinations, causes, subNodes, rhsParents, non_fresh_vars);
                }
                else {
                    eqRhs.insert(arg1);
                }

                if (is_important(arg1, non_fresh_vars) && !has_empty_vars(to_app(*it)->get_arg(1))) {
                    eqRhs = {to_app(*it)->get_arg(1)};
                }

                if (is_important(arg0, non_fresh_vars) && !has_empty_vars(to_app(*it)->get_arg(0))) {
                    eqLhs = {to_app(*it)->get_arg(0)};
                }

                causes[object].insert(createEqualOperator(arg0, to_app(*it)->get_arg(0)));
                causes[object].insert(createEqualOperator(arg1, to_app(*it)->get_arg(1)));
                // to prevent the exponential growth
                if (eqLhs.size() > 20){
                    eqLhs.clear();
                    eqLhs.insert(find_equivalent_variable(arg0));
                    STRACE("str", tout << __LINE__ << " too many eq combinations " << mk_pp(arg0, m) << std::endl;);
                }
                else {
                    if (causes.find(arg0) != causes.end())
                        causes[object].insert(causes[arg0].begin(), causes[arg0].end());
                }

                if (eqRhs.size() > 20){
                    eqRhs.clear();
                    eqRhs.insert(find_equivalent_variable(arg1));
                    STRACE("str", tout << __LINE__ << " too many eq combinations " << mk_pp(arg1, m) << std::endl;);
                }
                else {
                    if (causes.find(arg0) != causes.end())
                        causes[object].insert(causes[arg0].begin(), causes[arg0].end());
                }

                STRACE("str", tout << __LINE__ << " " << mk_pp(arg0, m) << " size = " << eqLhs.size()  << std::endl;);
                STRACE("str", tout << __LINE__ << " " << mk_pp(arg1, m) << " size = " << eqRhs.size()  << std::endl;);
                for (const auto &l : eqLhs)
                    for (const auto &r : eqRhs) {
                        zstring val_lhs, val_rhs;
                        bool hasLhSValue = false, hasRhSValue = false;
                        expr* valueLhs = get_eqc_value(l, hasLhSValue);
                        expr* valueRhs = get_eqc_value(r, hasRhSValue);

                        if (hasLhSValue) {
                            u.str.is_string(valueLhs, val_lhs);
                            STRACE("str", tout << __LINE__ << " " << mk_pp(l, m) << " " << val_lhs << std::endl;);
                        }
                        if (hasRhSValue) {
                            u.str.is_string(valueRhs, val_rhs);
                            STRACE("str", tout << __LINE__ << " " << mk_pp(r, m) << " " << val_rhs << std::endl;);
                        }
                        bool specialCase = false;
                        if (hasLhSValue)
                            if (val_lhs.length() == 0) {
                                STRACE("str", tout << __LINE__ << " " << mk_pp(l, m) << " " << val_lhs << "--> = " << mk_pp(r, m)<< std::endl;);
                                specialCase = true;
                                eqConcat.insert(r);
                            }

                        if (!specialCase && hasRhSValue)
                            if (val_rhs.length() == 0){
                                STRACE("str", tout << __LINE__ << " " << mk_pp(r, m) << " " << val_rhs << "--> = " << mk_pp(l, m) << std::endl;);
                                specialCase = true;
                                eqConcat.insert(l);
                            }

                        if (!specialCase) {
                            if (hasLhSValue && hasRhSValue){
                                expr *tmp = u.str.mk_string(val_lhs + val_rhs);
                                m_trail.push_back(tmp);
                                eqConcat.insert(tmp);
                            }
                            else if (hasLhSValue) {
                                expr *tmp = create_concat_with_str(val_lhs, r);
                                m_trail.push_back(tmp);
                                eqConcat.insert(tmp);
                            }
                            else if (hasRhSValue) {
                                expr *tmp = create_concat_with_str(l, val_rhs);
                                m_trail.push_back(tmp);
                                eqConcat.insert(tmp);
                            }
                            else {
                                expr *tmp = create_concat_with_concat(l, r);
                                m_trail.push_back(tmp);
                                eqConcat.insert(tmp);
                            }
                        }
                    }
            }
        }

        STRACE("str", tout << __LINE__ << " " << mk_pp(object, m) << " " << result.size() <<  " cases " << std::endl;);
        for (const auto& e: eqConcat)
            STRACE("str",
                   if (!u.str.is_concat(e))
                       tout << "\t\t" << mk_pp(e, m) << std::endl;
                   else {
                       ptr_vector<expr> childrenVector;
                       get_nodes_in_concat(e, childrenVector);
                       tout << "\t\t";
                       for (int i = 0; i < childrenVector.size(); ++i)
                           tout << mk_pp(childrenVector[i], m)  << " ";
                       tout << std::endl;
                   });

        // continuing refining
        for (const auto& nn : eqConcat)
            if (((!u.str.is_extract(nn)) &&
                 (!u.str.is_at(nn)) &&
                 (!u.str.is_replace(nn)) &&
                 (!u.str.is_itos(nn)) &&
                 (!u.str.is_nth(nn))) ||
                 u.str.is_concat(nn))
            {
                if (has_empty_vars(nn))
                    continue;
                STRACE("str", tout << __LINE__ << mk_pp(object, m) << " = " << mk_pp(nn, m) << std::endl;);
                expr_ref_vector tmp(m);
                get_const_regex_str_asts_in_node(nn, tmp);
                if (tmp.size() != 0)
                    result.insert(nn);
                else {
                    get_important_asts_in_node(nn, non_fresh_vars, tmp, true);
                    if (tmp.size() != 0)
                        result.insert(nn);
                }
            }
        STRACE("str", tout << __LINE__ << " " << mk_pp(object, m) << " " << result.size() <<  " cases " << std::endl;);
        if (result.size() == 0) {
            STRACE("str", tout << __LINE__ << " add itself " << mk_pp(object, m) << std::endl;);
            result.emplace(simplify_concat(object));
        }
        else {
            // important var, it = itself, size = 1, it is root --> add another option if it is possible
            if ( result.size() == 1 &&
                    is_important(object, non_fresh_vars) &&
                    object == *result.begin() &&
                    u.str.is_concat(object)
                ){
                for (const auto& nn : eqNodeSet)
                    if (!u.str.is_concat(nn) && to_app(nn)->get_num_args() < 2)
                        result.insert(nn);
            }
        }

        combinations[object] = result;
        for (const auto& e: result)
            STRACE("str",
                   if (!u.str.is_concat(e))
                       tout << "\t\t" << mk_pp(e, m) << std::endl;
                   else {
                       ptr_vector<expr> childrenVector;
                       get_nodes_in_concat(e, childrenVector);
                       tout << "\t\t";
                       for (int i = 0; i < childrenVector.size(); ++i)
                           tout << mk_pp(childrenVector[i], m)  << " ";
                       tout << std::endl;
                   });
        return result;
    }

    expr* theory_str::create_concat_with_concat(expr* n1, expr* n2){
        expr* arg0 = nullptr;
        expr* arg1 = nullptr;
        expr* arg2 = nullptr;
        expr* arg3 = nullptr;

        if (u.str.is_concat(n1, arg0, arg1) && u.str.is_concat(n2, arg2, arg3)){
            zstring v1, v2;
            if (u.str.is_string(arg1, v1) && u.str.is_string(arg2, v2)){
                return u.str.mk_concat(arg0, mk_concat(u.str.mk_string(v1 + v2), arg3));
            }
        }

        return u.str.mk_concat(n1, n2);
    }

    expr* theory_str::create_concat_with_str(expr* n, zstring str){
        expr* ends = ends_with_str(n);
        if (ends != nullptr){
            ptr_vector<expr> l;
            get_nodes_in_concat(n, l);
            zstring v;
            u.str.is_string(ends, v);
            v = v + str;
            ends = u.str.mk_string(v);
            for (int i = (int)l.size() - 2; i >= 0; --i){
                ends = u.str.mk_concat(l[i], ends);
            }
            return ends;
        }
        else
            return u.str.mk_concat(n, u.str.mk_string(str));
    }

    expr* theory_str::create_concat_with_str(zstring str, expr* n){
        expr* starts = starts_with_str(n);
        if (starts != nullptr){
            ptr_vector<expr> l;
            get_nodes_in_concat(n, l);
            zstring v;
            u.str.is_string(starts, v);
            v = str + v;
            starts = u.str.mk_string(v);

            expr* tmp = l[l.size() - 1];
            for (int i = (int)l.size() - 2; i >= 1; --i){
                tmp = u.str.mk_concat(l[i], tmp);
            }
            return u.str.mk_concat(starts, tmp);
        }
        else
            return u.str.mk_concat(u.str.mk_string(str), n);
    }

    expr* theory_str::ends_with_str(expr* n){
        if (u.str.is_concat(n)){
            ptr_vector<expr> l;
            get_nodes_in_concat(n, l);
            if (u.str.is_string(l[l.size() - 1]))
                return l[l.size() - 1];
        }
        return nullptr;
    }

    expr* theory_str::starts_with_str(expr* n){
        if (u.str.is_concat(n)){
            ptr_vector<expr> l;
            get_nodes_in_concat(n, l);
            if (u.str.is_string(l[0]))
                return l[0];
        }
        return nullptr;
    }

    void theory_str::add_subnodes(expr* concatL, expr* concatR, std::set<expr*> &subNodes){
        rational vLen;
        if (get_len_value(concatL, vLen)) {
            if (vLen.get_int64() == 0)
                return;
        }

        if (get_len_value(concatR, vLen)) {
            if (vLen.get_int64() == 0)
                return;
        }

        subNodes.insert(concatL);
        subNodes.insert(concatR);
    }

    bool theory_str::can_propagate() {
        return !m_basicstr_axiom_todo.empty() || !m_str_eq_todo.empty()
               || !m_concat_axiom_todo.empty() || !m_concat_eval_todo.empty()
               || !m_library_aware_axiom_todo.empty()
               || !m_delayed_axiom_setup_terms.empty()
               || !m_persisted_axiom_todo.empty()
               || (search_started && !m_delayed_assertions_todo.empty())
                ;
    }

    void theory_str::propagate() {
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " @lvl " << m_scope_level <<  std::endl;);

        assert_cached_eq_state();

        if (uState.reassertEQ)
            assert_cached_diseq_state();

        context & ctx = get_context();
        while (can_propagate()) {


            while(true) {
                // this can potentially recursively activate itself
                unsigned start_count = m_basicstr_axiom_todo.size();
                ptr_vector<enode> axioms_tmp(m_basicstr_axiom_todo);
                for (auto const& el : axioms_tmp) {
                    instantiate_basic_string_axioms(el);
                }
                unsigned end_count = m_basicstr_axiom_todo.size();
                if (end_count > start_count) {
                    STRACE("str", tout << "new basic string axiom terms added -- checking again" << std::endl;);
                    continue;
                } else {
                    break;
                }
            }
            m_basicstr_axiom_todo.reset();
            STRACE("str", tout << "reset m_basicstr_axiom_todo" << std::endl;);

//            for (auto const& pair : m_str_eq_todo) {
//                handle_equality(pair.first->get_owner(), pair.second->get_owner());
//            }
            m_str_eq_todo.reset();

            for (auto const& el : m_concat_axiom_todo) {
                instantiate_concat_axiom(el);
            }
            m_concat_axiom_todo.reset();

//            for (auto const& el : m_concat_eval_todo) {
//                try_eval_concat(el);
//            }
            m_concat_eval_todo.reset();

            while(true) {
                // Special handling: terms can recursively set up other terms
                // (e.g. indexof can instantiate other indexof terms).
                // - Copy the list so it can potentially be modified during setup.
                // - Don't clear this list if new ones are added in the process;
                //   instead, set up all the new terms before proceeding.
                // TODO see if any other propagate() worklists need this kind of handling
                // TODO we really only need to check the new ones on each pass
                unsigned start_count = m_library_aware_axiom_todo.size();
                STRACE("str", tout << __LINE__ << " m_library_aware_axiom_todo: size " << start_count << std::endl;);
                ptr_vector<enode> axioms_tmp(m_library_aware_axiom_todo);
                for (auto const& e : axioms_tmp) {
                    app * a = e->get_owner();
                    if (a == nullptr || a->get_num_args() == 0) {
                        STRACE("str", tout << __LINE__ << " instantiate_axiom null" << std::endl;);
                        continue;
                    }
                    if (u.str.is_stoi(a)) {
                        instantiate_axiom_str_to_int(e);
                    } else if (u.str.is_itos(a)) {
                        instantiate_axiom_int_to_str(e);
                    } else if (u.str.is_at(a)) {
                        instantiate_axiom_charAt(e);
                    } else if (u.str.is_prefix(a)) {
                        instantiate_axiom_prefixof(e);
                    } else if (u.str.is_suffix(a)) {
                        instantiate_axiom_suffixof(e);
                    } else if (u.str.is_contains(a)) {
                        instantiate_axiom_contains(e);
                    } else if (u.str.is_index(a)) {
                        instantiate_axiom_indexof(e);
                    } else if (u.str.is_extract(a)) {
                        instantiate_axiom_substr(e);
                    } else if (u.str.is_replace(a)) {
                        instantiate_axiom_replace(e);
                    } else if (u.str.is_in_re(a)) {
                        instantiate_axiom_regexIn(e);
                    } else {
                        STRACE("str", tout << "BUG: unhandled library-aware term " << mk_pp(e->get_owner(), get_manager()) << std::endl;);
                        NOT_IMPLEMENTED_YET();
                    }
                }
                unsigned end_count = m_library_aware_axiom_todo.size();
                if (end_count > start_count) {
                    STRACE("str", tout << "new library-aware terms added during axiom setup -- checking again" << std::endl;);
                    continue;
                } else {
                    break;
                }
            }
            m_library_aware_axiom_todo.reset();

            for (auto el : m_delayed_axiom_setup_terms) {
                // I think this is okay
                ctx.internalize(el, false);
                set_up_axioms(el);
            }
            m_delayed_axiom_setup_terms.reset();

            for (expr * a : m_persisted_axiom_todo) {
                assert_axiom(a);
            }
            m_persisted_axiom_todo.reset();

            if (search_started) {
                for (auto const& el : m_delayed_assertions_todo) {
                    assert_axiom(el);
                }
                m_delayed_assertions_todo.reset();
            }
        }
    }

    /*
     * Add axioms that are true for any string variable:
     * 1. Length(x) >= 0
     * 2. Length(x) == 0 <=> x == ""
     * If the term is a string constant, we can assert something stronger:
     *    Length(x) == strlen(x)
     */
    void theory_str::instantiate_basic_string_axioms(enode * str) {
        context & ctx = get_context();
        ast_manager & m = get_manager();

        {
            sort * a_sort = m.get_sort(str->get_owner());
            sort * str_sort = u.str.mk_string_sort();
            if (a_sort != str_sort) {
                STRACE("str", tout << "WARNING: not setting up string axioms on non-string term " << mk_pp(str->get_owner(), m) << std::endl;);
                return;
            }
        }

        // TESTING: attempt to avoid a crash here when a variable goes out of scope
        if (str->get_iscope_lvl() > ctx.get_scope_level()) {
            STRACE("str", tout << "WARNING: skipping axiom setup on out-of-scope string term" << std::endl;);
            return;
        }

        // generate a stronger axiom for constant strings
        app * a_str = str->get_owner();

        if (u.str.is_string(a_str)) {
            expr_ref len_str(m);
            len_str = mk_strlen(a_str);
            SASSERT(len_str);

            zstring strconst;
            u.str.is_string(str->get_owner(), strconst);
            unsigned int l = strconst.length();
            expr_ref len(m_autil.mk_numeral(rational(l), true), m);

            literal lit(mk_eq(len_str, len, false));
            ctx.mark_as_relevant(lit);
            ctx.mk_th_axiom(get_id(), 1, &lit);
        } else {
            // build axiom 1: Length(a_str) >= 0
            {
                // build LHS
                expr_ref len_str(m);
                len_str = mk_strlen(a_str);
                SASSERT(len_str);
                // build RHS
                expr_ref zero(m);
                zero = m_autil.mk_numeral(rational(0), true);
                SASSERT(zero);
                // build LHS >= RHS and assert
                app * lhs_ge_rhs = m_autil.mk_ge(len_str, zero);
                SASSERT(lhs_ge_rhs);
                assert_axiom(lhs_ge_rhs);
            }

            // build axiom 2: Length(a_str) == 0 <=> a_str == ""
            {
                // build LHS of iff
                expr_ref len_str(m);
                len_str = mk_strlen(a_str);
                SASSERT(len_str);
                expr_ref zero(m);
                zero = m_autil.mk_numeral(rational(0), true);
                SASSERT(zero);
                expr_ref lhs(m);
                lhs = ctx.mk_eq_atom(len_str, zero);
                SASSERT(lhs);
                // build RHS of iff
                expr_ref empty_str(m);
                empty_str = mk_string("");
                SASSERT(empty_str);
                expr_ref rhs(m);
                rhs = ctx.mk_eq_atom(a_str, empty_str);
                SASSERT(rhs);
                // build LHS <=> RHS and assert
                literal l(mk_eq(lhs, rhs, true));
                ctx.mark_as_relevant(l);
                ctx.mk_th_axiom(get_id(), 1, &l);
            }

        }
    }


    /*
     * Instantiate an axiom of the following form:
     * Length(Concat(x, y)) = Length(x) + Length(y)
     */
    void theory_str::instantiate_concat_axiom(enode * cat) {
        app * a_cat = cat->get_owner();
        SASSERT(u.str.is_concat(a_cat));

        ast_manager & m = get_manager();

        // build LHS
        expr_ref len_xy(m);
        len_xy = mk_strlen(a_cat);

        // build RHS: start by extracting x and y from Concat(x, y)
        SASSERT(a_cat->get_num_args() == 2);
        app * a_x = to_app(a_cat->get_arg(0));
        app * a_y = to_app(a_cat->get_arg(1));
        concat_astNode_map.insert(a_x, a_y, a_cat);
        expr_ref len_x(m);
        len_x = mk_strlen(a_x);

        expr_ref len_y(m);
        len_y = mk_strlen(a_y);

        // now build len_x + len_y
        expr_ref len_x_plus_len_y(m);
        len_x_plus_len_y = m_autil.mk_add(len_x, len_y);

        // finally assert equality between the two subexpressions
        app * eq = m.mk_eq(len_xy, len_x_plus_len_y);
        assert_axiom(eq);

        // len_x = 0 --> Concat(x, y) = y
//        assert_implication(m.mk_eq(len_x, mk_int(0)), createEqualOperator(a_cat, a_y));
//
//        // len_y = 0 --> Concat(x, y) = x
//        assert_implication(m.mk_eq(len_y, mk_int(0)), createEqualOperator(a_cat, a_x));
    }

    void theory_str::instantiate_axiom_prefixof(enode * e) {
        context & ctx = get_context();
        ast_manager & m = get_manager();

        app * expr = e->get_owner();
        if (axiomatized_terms.contains(expr)) {
            return;
        }
        axiomatized_terms.insert(expr);

        TRACE("str", tout << "instantiate prefixof axiom for " << mk_pp(expr, m) << std::endl;);

        expr_ref ts0(mk_str_var("pre_prefix"), m);
        expr_ref ts1(mk_str_var("post_prefix"), m);

        assert_axiom(ctx.mk_eq_atom(mk_strlen(ts0), mk_strlen(expr->get_arg(0))));

        expr_ref_vector innerItems(m);
        innerItems.push_back(ctx.mk_eq_atom(expr->get_arg(1), mk_concat(ts0, ts1)));
        innerItems.push_back(m.mk_ite(ctx.mk_eq_atom(ts0, expr->get_arg(0)), expr, mk_not(m, expr)));
        expr_ref then1(m.mk_and(innerItems.size(), innerItems.c_ptr()), m);
        SASSERT(then1);

        // the top-level condition is Length(arg0) >= Length(arg1)
        expr_ref topLevelCond(
                m_autil.mk_ge(
                        m_autil.mk_add(
                                mk_strlen(expr->get_arg(1)), m_autil.mk_mul(mk_int(-1), mk_strlen(expr->get_arg(0)))),
                        mk_int(0))
                , m);

        expr_ref finalAxiom(m.mk_ite(topLevelCond, then1, mk_not(m, expr)), m);
        assert_axiom(finalAxiom);
    }

    void theory_str::instantiate_axiom_suffixof(enode * e) {
        context & ctx = get_context();
        ast_manager & m = get_manager();

        app * expr = e->get_owner();
        if (axiomatized_terms.contains(expr)) {
            return;
        }
        axiomatized_terms.insert(expr);

        TRACE("str", tout << "instantiate suffixof axiom for " << mk_pp(expr, m) << std::endl;);

        expr_ref ts0(mk_str_var("pre_suffix"), m);
        expr_ref ts1(mk_str_var("post_suffix"), m);

        expr_ref_vector innerItems(m);
        innerItems.push_back(ctx.mk_eq_atom(expr->get_arg(1), mk_concat(ts0, ts1)));
        innerItems.push_back(ctx.mk_eq_atom(mk_strlen(ts1), mk_strlen(expr->get_arg(0))));
        innerItems.push_back(m.mk_ite(ctx.mk_eq_atom(ts1, expr->get_arg(0)), expr, mk_not(m, expr)));
        expr_ref then1(m.mk_and(innerItems.size(), innerItems.c_ptr()), m);

        // the top-level condition is Length(arg0) >= Length(arg1)
        expr_ref topLevelCond(
                m_autil.mk_ge(
                        m_autil.mk_add(
                                mk_strlen(expr->get_arg(1)), m_autil.mk_mul(mk_int(-1), mk_strlen(expr->get_arg(0)))),
                        mk_int(0))
                , m);

        expr_ref finalAxiom(m.mk_ite(topLevelCond, then1, mk_not(m, expr)), m);
        assert_axiom(finalAxiom);
    }

    /*
     * Quick paths:
     *      path 1: "abc" contains "a"
     *      path 2: (x . "abc" . y) contains "a"
     *
     *
     *      path 3: (str.contains (str.substr value1 number1 (+ number2 (str.indexof value1 "J" number1))) "J")
     *          --> (str.indexof value1 "J" number1) > -1 && (+ number2 (str.indexof value1 "J" number1)) > indexof
     * arg0 = pre_contains . arg1 . post_contains
     *
     */
    void theory_str::instantiate_axiom_contains(enode * e) {
        context & ctx = get_context();
        ast_manager & m = get_manager();

        app * ex = e->get_owner();
        if (axiomatized_terms.contains(ex)) {
            return;
        }
        axiomatized_terms.insert(ex);

        // quick path, because this is necessary due to rewriter behaviour
        // at minimum it should fix z3str/concat-006.smt2
        zstring haystackStr, needleStr;
        if (u.str.is_string(ex->get_arg(1), needleStr)) {
            if (u.str.is_string(ex->get_arg(0), haystackStr)) {
                if (haystackStr.contains(needleStr)) {
                    assert_axiom(ex);
                } else {
                    assert_axiom(mk_not(m, ex));
                }
                return;
            } else if (u.str.is_concat(ex->get_arg(0))) {
                // if it is a concat,
                // collect all consts in concat, and check
                ptr_vector<expr> childrenVector;
                get_nodes_in_concat(ex->get_arg(0), childrenVector);
                for (int i = 0; i < childrenVector.size(); ++i) {
                    zstring value;
                    if (u.str.is_string(childrenVector[i], value))
                        if (value.contains(needleStr)) {
                            assert_axiom(ex);
                            return;
                        }
                }
            }
            else if (u.str.is_extract(ex->get_arg(0))){
                // (str.contains (str.substr value1 0 (+ 1 (str.indexof value1 "J" 0))) "J")
                expr* substr = ex->get_arg(0);
                STRACE("str", tout << __LINE__ << " " << mk_pp(substr, m) << std::endl;);
                expr* arg0 = to_app(substr)->get_arg(0);
                expr* arg1 = to_app(substr)->get_arg(1);
                expr* arg2 = to_app(substr)->get_arg(2);

                // check the 2nd arg:
                if (u.str.is_index(arg1)){
                    app* indexOfApp = to_app(arg1);
                    expr* arg2_arg0 = indexOfApp->get_arg(0);
                    expr* arg2_arg1 = indexOfApp->get_arg(1);

                    // same var, same keyword
                    if (arg2_arg0 == arg0 && arg2_arg1 == ex->get_arg(1)){
                        // 3rd arg = 0 || contain = true
                        expr* e1 = createEqualOperator(arg2, mk_int(0));
                        if (needleStr.length() > 0)
                            assert_implication(e1, mk_not(m, ex));
                        else
                            assert_axiom(ex);

                        expr* e2 = createGreaterEqOperator(arg2, mk_int(1));
                        assert_implication(e2, ex);
                    }
                }

                // check the third arg: + , -
                if (m_autil.is_add(arg2) || m_autil.is_sub(arg2)) {
                    STRACE("str", tout << __LINE__ << " " << mk_pp(arg2, m) << std::endl;);
                    bool found_indexof = false;
                    bool completed = true;
                    app* indexOfApp = nullptr;
                    int sum = 0;
                    app* arg2app = to_app(arg2);
                    for (int i = 0; i < arg2app->get_num_args(); ++i) {

                        if (u.str.is_index(arg2app->get_arg(i))){
                            STRACE("str", tout << __LINE__ << " " << mk_pp(arg2app->get_arg(i), m) << std::endl;);
                            indexOfApp = to_app(arg2app->get_arg(i));
                            expr* arg2_arg0 = indexOfApp->get_arg(0);
                            expr* arg2_arg1 = indexOfApp->get_arg(1);
                            expr* arg2_arg2 = indexOfApp->get_arg(2);
                            if (arg2_arg0 == arg0){
                                zstring indexOfStr;
                                if (u.str.is_string(arg2_arg1, indexOfStr) && indexOfStr == needleStr) {
                                    if (arg2_arg2 == arg1){
                                        found_indexof = true;
                                    }
                                }
                            }
                        }
                        else {
                            rational val;
                            if (m_autil.is_numeral(arg2app->get_arg(i), val)) {
                                sum = sum + val.get_int64();
                            }
                            else if (m_autil.is_mul(arg2app->get_arg(i))) {
                                app* tmp = to_app(arg2app->get_arg(i));
                                int mul = 1;
                                for (int j = 0; j < tmp->get_num_parameters(); ++j)
                                    if (m_autil.is_numeral(tmp->get_arg(j), val))
                                        mul = mul * val.get_int64();
                                    else {
                                        completed = false;
                                        break;
                                    }

                                if (completed){
                                    sum += mul;
                                }
                                else
                                    break;
                            }
                            else {
                                completed = false;
                                break;
                            }
                        }
                    }

                    if (completed && found_indexof){
                        // index >= 0
                        expr* e1 = createGreaterEqOperator(indexOfApp, mk_int(0));
                        STRACE("str", tout << __LINE__ << " " << mk_pp(e1, m) << std::endl;);
                        // index + 1 >= arg2app
                        if (sum >= 1) {
                            // e1  --> contain = true
                            assert_implication(e1, ex);
                            return;
                        }
                        else {
                            // index <= arg2app
                            // e1 --> contain = false

                            assert_implication(e1, mk_not(m, ex));
                            return;
                        }
                    }
                }
            }
        }

        { // register Contains()
            expr * str = ex->get_arg(0);
            expr * substr = ex->get_arg(1);
            contains_map.push_back(ex);
            std::pair<expr*, expr*> key = std::pair<expr*, expr*>(str, substr);
            contain_pair_bool_map.insert(str, substr, ex);
            if (!contain_pair_idx_map.contains(str)) {
                contain_pair_idx_map.insert(str, std::set<std::pair<expr*, expr*>>());
            }
            if (!contain_pair_idx_map.contains(substr)) {
                contain_pair_idx_map.insert(substr, std::set<std::pair<expr*, expr*>>());
            }
            contain_pair_idx_map[str].insert(key);
            contain_pair_idx_map[substr].insert(key);
        }

        std::pair<app*, app*> value = std::make_pair<app*, app*>(mk_str_var("pre_contain"), mk_str_var("post_contain"));
        expr_ref haystack(ex->get_arg(0), m), needle(ex->get_arg(1), m);
        app* a = u.str.mk_contains(haystack, needle);
        enode* key = ensure_enode(a);
        if (contain_split_map.contains(key)) {
            std::pair<enode *, enode *> tmpvalue = contain_split_map[key];
            value = std::make_pair<app *, app *>(tmpvalue.first->get_owner(), tmpvalue.second->get_owner());
        }
        else {
            contain_split_map.insert(key, std::make_pair(ctx.get_enode(value.first), ctx.get_enode(value.second)));
        }
        expr_ref ts0(value.first, m);
        expr_ref ts1(value.second, m);

        if (u.str.is_extract(haystack.get())){
            app* substr = to_app(haystack.get());
            rational ra;
            if (m_autil.is_numeral(substr->get_arg(1), ra) && ra.get_int64() == 0){
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " found substr contain " << mk_pp(haystack.get(), m) << std::endl;);
                if (contain_pair_bool_map.contains(std::make_pair(substr->get_arg(0), needle.get()))) {
                    app *rootContain = mk_contains(substr->get_arg(0), needle);
                    enode* keynode = ensure_enode(rootContain);
                    SASSERT(contain_split_map.contains(keynode));
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " trying new assert " << mk_pp(haystack.get(), m) << std::endl;);
                    assert_axiom(createEqualOperator(value.first, contain_split_map[keynode].first->get_owner()));
                }
            }
        }

        for (const auto& p : contain_pair_bool_map){
            if (u.str.is_extract(p.get_key1()) && p.get_key2() == needle.get()){
                app* substr = to_app(p.get_key1());
                rational ra;
                if (substr->get_arg(0) == haystack.get() &&
                    m_autil.is_numeral(substr->get_arg(1), ra) && ra.get_int64() == 0){
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " found substr contain " << mk_pp(haystack.get(), m) << std::endl;);
                    app *rootContain = mk_contains(p.get_key1(), needle.get());
                    enode* keynode = ensure_enode(rootContain);
                    SASSERT(contain_split_map.contains(keynode));
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " trying new assert " << mk_pp(haystack.get(), m) << std::endl;);
                    assert_axiom(createEqualOperator(value.first, contain_split_map[keynode].first->get_owner()));
                }
            }
        }

        expr_ref breakdownAssert(ctx.mk_eq_atom(ex, ctx.mk_eq_atom(ex->get_arg(0), mk_concat(ts0, mk_concat(ex->get_arg(1), ts1)))), m);
        SASSERT(breakdownAssert);
        assert_axiom(mk_not(m, u.str.mk_contains(value.first, needle.get())));
        assert_axiom(breakdownAssert);
    }

    /*
     * arg1 >= 0 && arg1 < arg0.len,
     *  then    arg0 = charAt0 . charAt1 . charAt2
     *          charAt0.len = arg1
     *          charAt1.len = 1
     *  else return ""
     */
    void theory_str::instantiate_axiom_charAt(enode * e) {
        context &ctx = get_context();
        ast_manager &m = get_manager();
        expr *arg0, *arg1;
        app *expr = e->get_owner();
        if (axiomatized_terms.contains(expr)) {
            return;
        }
        axiomatized_terms.insert(expr);
        VERIFY(u.str.is_at(expr, arg0, arg1));

        TRACE("str", tout << __FUNCTION__ << ":" << mk_pp(expr, m) << std::endl;);

        expr_ref ts0(mk_str_var("charAt0"), m);
        expr_ref ts1(mk_str_var("charAt1"), m);
        expr_ref ts2(mk_str_var("charAt2"), m);

        expr_ref cond(m.mk_and(
                m_autil.mk_ge(arg1, mk_int(0)),
                m_autil.mk_lt(arg1, mk_strlen(arg0))), m);

        expr_ref_vector and_item(m);
        and_item.push_back(ctx.mk_eq_atom(arg0, mk_concat(ts0, mk_concat(ts1, ts2))));
        and_item.push_back(ctx.mk_eq_atom(arg1, mk_strlen(ts0)));
        and_item.push_back(ctx.mk_eq_atom(mk_strlen(ts1), mk_int(1)));

        expr_ref thenBranch(::mk_and(and_item));
        expr_ref elseBranch(ctx.mk_eq_atom(ts1, mk_string("")), m);
        expr_ref axiom(m.mk_ite(cond, thenBranch, elseBranch), m);
        expr_ref reductionVar(ctx.mk_eq_atom(expr, ts1), m);
        expr_ref finalAxiom(m.mk_and(axiom, reductionVar), m);
        get_context().get_rewriter()(finalAxiom);
        assert_axiom(finalAxiom);
    }

    /*
     * arg2 = 0,
     *      arg0 contains arg1
     *      then    arg0 = indexOf1 . arg1 . indexOf2
     *              indexOf1.len = indexAst
     *              charAt1.len = 1
     *              if needle.len = 1, then
     *                  indexOf1 does not contain arg1
     *              else
     *                  arg0 = x3 . x4
     *                  x3.len = indexAst + arg1.len - 1
     *                  x3 does not contain arg1
     *      else
     *              indexOf1 = -1
     *  return indexOf1
     */
    void theory_str::instantiate_axiom_indexof(enode * e) {
        context & ctx = get_context();
        ast_manager & m = get_manager();

        app * ex = e->get_owner();
        TRACE("str", tout << __FUNCTION__ << ":" << mk_pp(ex, m) << std::endl;);
        if (axiomatized_terms.contains(ex)) {
            return;
        }
        SASSERT(ex->get_num_args() == 3);
        // if the third argument is exactly the integer 0, we can use this "simple" indexof;
        // otherwise, we call the "extended" version
        expr * startingPosition = ex->get_arg(2);
        rational startingInteger;
        if (!m_autil.is_numeral(startingPosition, startingInteger) || !startingInteger.is_zero()) {
            // "extended" indexof term with prefix
            instantiate_axiom_indexof_extended(e);
            return;
        }
        axiomatized_terms.insert(ex);

        TRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ":" << mk_pp(ex, m) << std::endl;);
        std::pair<app*, app*> value;
        expr_ref haystack(ex->get_arg(0), m), needle(ex->get_arg(1), m);
        app* a = u.str.mk_contains(haystack, needle);
        enode* key = ensure_enode(a);

        if (contain_split_map.contains(key)) {
            std::pair<enode *, enode *> tmpvalue = contain_split_map[key];
            value = std::make_pair<app *, app *>(tmpvalue.first->get_owner(), tmpvalue.second->get_owner());
        }
        else {
            value = std::make_pair<app*, app*>(mk_str_var("indexOf1"), mk_str_var("indexOf2"));
            contain_split_map.insert(key, std::make_pair(ctx.get_enode(value.first), ctx.get_enode(value.second)));
        }

        if (u.str.is_extract(haystack.get())){
            app* substr = to_app(haystack.get());
            rational ra;
            if (m_autil.is_numeral(substr->get_arg(1), ra) && ra.get_int64() == 0){
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " found substr contain " << mk_pp(haystack.get(), m) << std::endl;);
                if (contain_pair_bool_map.contains(std::make_pair(substr->get_arg(0), needle.get()))) {
                    app *rootContain = mk_contains(substr->get_arg(0), needle);
                    enode* keynode = ensure_enode(rootContain);
                    SASSERT(contain_split_map.contains(keynode));
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " trying new assert " << mk_pp(haystack.get(), m) << std::endl;);
                    assert_axiom(createEqualOperator(value.first, contain_split_map[keynode].first->get_owner()));
                }
            }
        }

        for (const auto& p : contain_pair_bool_map){
            if (u.str.is_extract(p.get_key1()) && p.get_key2() == needle.get()){
                app* substr = to_app(p.get_key1());
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " found substr contain " << mk_pp(haystack.get(), m) << std::endl;);
                rational ra;
                if (substr->get_arg(0) == haystack.get() &&
                    m_autil.is_numeral(substr->get_arg(1), ra) && ra.get_int64() == 0){
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " found substr contain " << mk_pp(haystack.get(), m) << std::endl;);
                    app *rootContain = mk_contains(p.get_key1(), needle.get());
                    enode* keynode = ensure_enode(rootContain);
                    SASSERT(contain_split_map.contains(keynode));
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " trying new assert " << mk_pp(haystack.get(), m) << std::endl;);
                    assert_axiom(createEqualOperator(value.first, contain_split_map[keynode].first->get_owner()));
                }
            }
        }

        expr_ref x1(value.first, m);
        expr_ref x2(value.second, m);
        expr_ref indexAst(mk_int_var("index"), m);

        expr_ref condAst(mk_contains(ex->get_arg(0), ex->get_arg(1)), m);
        SASSERT(condAst);

        if (index_tail.contains(ex)) {
            STRACE("str",
                   tout << __LINE__ << " " << __FUNCTION__ << " update index tail vs substring " << mk_pp(index_tail[ex].first, m)
                        << std::endl;);
            assert_axiom(createEqualOperator(x2.get(), index_tail[ex].second));
            expr* x1_arg1 = mk_concat(x1.get(), ex->get_arg(1));
            assert_axiom(createEqualOperator(index_tail[ex].first, x1_arg1));
            length_relation.insert(std::make_pair(index_tail[ex].first, x1.get()));
            length_relation.insert(std::make_pair(index_tail[ex].first, ex->get_arg(1)));
        }
        else {
            index_tail.insert(ex, std::make_pair(mk_concat(x1.get(), ex->get_arg(1)), x2.get()));
        }

        if (index_head.contains(ex)) {
            STRACE("str",
                   tout << __LINE__ << " " << __FUNCTION__ << " update index head vs substring " << mk_pp(index_head[ex], m)
                        << std::endl;);
            assert_axiom(createEqualOperator(x1.get(), index_head[ex]));
        }
        else {
            index_head.insert(ex, x1.get());
        }

        // -----------------------
        // true branch
        expr_ref_vector thenItems(m);
        //  args[0] = x1 . args[1] . x2
        thenItems.push_back(ctx.mk_eq_atom(ex->get_arg(0), mk_concat(x1, mk_concat(ex->get_arg(1), x2))));
        //  indexAst = |x1|
        thenItems.push_back(ctx.mk_eq_atom(indexAst, mk_strlen(x1)));

        bool oneCharCase = false;
        zstring needleStr;
        if (u.str.is_string(ex->get_arg(1), needleStr)) {
            if (needleStr.length() == 1) {
                oneCharCase = true;
            }
        }

        if (oneCharCase){
            assert_axiom(mk_not(m, mk_contains(x1, ex->get_arg(1))));
        }
        else {
            //     args[0]  = x3 . x4
            //  /\ |x3| = |x1| + |args[1]| - 1
            //  /\ ! contains(x3, args[1])
            expr_ref x3(mk_str_var("x3"), m);
            expr_ref x4(mk_str_var("x4"), m);
            expr_ref tmpLen(m_autil.mk_add(indexAst, mk_strlen(ex->get_arg(1)), mk_int(-1)), m);
            SASSERT(tmpLen);
            thenItems.push_back(ctx.mk_eq_atom(ex->get_arg(0), mk_concat(x3, x4)));
            thenItems.push_back(ctx.mk_eq_atom(mk_strlen(x3), tmpLen));
            thenItems.push_back(mk_not(m, mk_contains(x3, ex->get_arg(1))));
        }
        expr_ref thenBranch(m.mk_and(thenItems.size(), thenItems.c_ptr()), m);
        SASSERT(thenBranch);

        // -----------------------
        // false branch
        expr_ref elseBranch(ctx.mk_eq_atom(indexAst, mk_int(-1)), m);
        SASSERT(elseBranch);

        expr_ref breakdownAssert(m.mk_ite(condAst, thenBranch, elseBranch), m);
        SASSERT(breakdownAssert);

        expr_ref reduceToIndex(ctx.mk_eq_atom(ex, indexAst), m);
        SASSERT(reduceToIndex);

        expr_ref finalAxiom(m.mk_and(breakdownAssert, reduceToIndex), m);
        SASSERT(finalAxiom);
        assert_axiom(finalAxiom);

        {
            // heuristic: integrate with str.contains information
            // (but don't introduce it if it isn't already in the instance)
            expr_ref haystack(ex->get_arg(0), m), needle(ex->get_arg(1), m), startIdx(ex->get_arg(2), m);
            expr_ref zeroAst(mk_int(0), m);
            // (H contains N) <==> (H indexof N, 0) >= 0
            expr_ref premise(u.str.mk_contains(haystack, needle), m);
            ctx.internalize(premise, false);
            expr_ref conclusion(m_autil.mk_ge(ex, zeroAst), m);
            expr_ref containsAxiom(ctx.mk_eq_atom(premise, conclusion), m);
            SASSERT(containsAxiom);

            // we can't assert this during init_search as it breaks an invariant if the instance becomes inconsistent
            m_delayed_axiom_setup_terms.push_back(containsAxiom);
        }
    }

    /*
     * arg2 != 0,
     *      arg0 = hd . tl
     *      then    arg0 = indexOf1 . arg1 . indexOf2
     *              indexOf1.len = indexAst
     *              charAt1.len = 1
     *              if needle.len = 1, then
     *                  indexOf1 does not contain arg1
     *              else
     *                  arg0 = x3 . x4
     *                  x3.len = indexAst + arg1.len - 1
     *                  x3 does not contain arg1
     *      else
     *              indexOf1 = -1
     *  return indexOf1
     */
    void theory_str::instantiate_axiom_indexof_extended(enode * _e) {
        context & ctx = get_context();
        ast_manager & m = get_manager();

        app * e = _e->get_owner();
        if (axiomatized_terms.contains(e)) {
            return;
        }
        SASSERT(e->get_num_args() == 3);
        axiomatized_terms.insert(e);

        TRACE("str", tout << __FUNCTION__ << ":" << mk_pp(e, m) << std::endl;);

        // str.indexof(H, N, i):
        // i < 0 --> -1
        // i == 0 --> str.indexof(H, N, 0)
        // i >= len(H) --> -1
        // 0 < i < len(H) -->
        //     H = hd ++ tl
        //     len(hd) = i
        //     str.indexof(tl, N, 0)

        expr * arg0 = nullptr; // "haystack"
        expr * arg1 = nullptr; // "needle"
        expr * startIndex = nullptr; // start index
        u.str.is_index(e, arg0, arg1, startIndex);

        expr_ref minus_one(m_autil.mk_numeral(rational::minus_one(), true), m);
        expr_ref zero(m_autil.mk_numeral(rational::zero(), true), m);

        // case split

        // case 1: startIndex < 0
        {
            expr_ref premise(m_autil.mk_le(startIndex, minus_one), m);
            if (premise != m.mk_false()) {
                expr_ref conclusion(ctx.mk_eq_atom(e, minus_one), m);
                assert_implication(premise, conclusion);
            }
        }

        expr_ref hd(mk_str_var("hd"), m);
        expr_ref tl(mk_str_var("tl"), m);


        // case 3: startIndex >= len(H), return -1
        {
            //th_rewriter rw(m);
            //rw(premise);
            expr_ref premise(m_autil.mk_ge(m_autil.mk_add(startIndex, m_autil.mk_mul(minus_one, mk_strlen(arg0))), zero), m);
            if (premise != m.mk_false()) {
                expr_ref conclusion(ctx.mk_eq_atom(e, minus_one), m);
                assert_implication(premise, conclusion);
            }
        }

        // case 4: 0 < i < len(H),
        //      arg0 = hd . tl
        //      hd.len = startIndex
        //      tlindex = indexOf(tl, arg1, 0)
        //      if tlindex >= 0, then
        //          indexOf = tlindex + |hd|,
        //      else indexOf = -1
        {
            expr_ref premise1(m_autil.mk_gt(startIndex, zero), m);
            expr_ref premise2(m.mk_not(m_autil.mk_ge(m_autil.mk_add(startIndex, m_autil.mk_mul(minus_one, mk_strlen(arg0))), zero)), m);
            expr_ref _premise(m.mk_and(premise1, premise2), m);
            expr_ref premise(_premise);
            th_rewriter rw(m);
            rw(premise);

            expr_ref_vector conclusion_terms(m);
            conclusion_terms.push_back(ctx.mk_eq_atom(arg0, mk_concat(hd, tl)));
            conclusion_terms.push_back(ctx.mk_eq_atom(mk_strlen(hd), startIndex));

            // if tlindex >= 0 --> indexOf = tlindex + hd.len, else indexOf = -1
            expr* tlIndexOf = mk_indexof(tl, arg1);
            conclusion_terms.push_back(createITEOperator(
                    createGreaterEqOperator(tlIndexOf, mk_int(0)),
                    ctx.mk_eq_atom(e, createAddOperator(tlIndexOf, mk_strlen(hd))),
                    ctx.mk_eq_atom(e, mk_int(-1))));

            expr_ref conclusion(mk_and(conclusion_terms), m);
            assert_implication(premise, conclusion);
        }

        {
            // heuristic: integrate with str.contains information
            // (but don't introduce it if it isn't already in the instance)
            // (0 <= startIndex < len(arg0)) ==> (arg0 contains arg1) <==> (arg0 indexof arg1, startIndex) >= startIndex
            expr_ref precondition1(m_autil.mk_gt(startIndex, minus_one), m);
            expr_ref precondition2(m.mk_not(m_autil.mk_ge(m_autil.mk_add(startIndex, m_autil.mk_mul(minus_one, mk_strlen(arg0))), zero)), m);
            expr_ref _precondition(m.mk_and(precondition1, precondition2), m);
            expr_ref precondition(_precondition);
            th_rewriter rw(m);
            rw(precondition);

            expr_ref premise(u.str.mk_contains(arg0, arg1), m);
            ctx.internalize(premise, false);
            expr_ref conclusion(m_autil.mk_ge(e, startIndex), m);
            expr_ref containsAxiom(ctx.mk_eq_atom(premise, conclusion), m);
            expr_ref finalAxiom(rewrite_implication(precondition, containsAxiom), m);
            // we can't assert this during init_search as it breaks an invariant if the instance becomes inconsistent
            m_delayed_assertions_todo.push_back(finalAxiom);
        }
    }

    /*
     * condition: pos >= 0 && pos < strlen(base) && len >= 0
     * if !condition
     *      return ""
     * if !condition && (pos+len) >= strlen(base)
     *      arg0 = substr0 . substr3 . substr 4
     *      substr0.len = pos
     *      substr4.len = 0
     *      return substr3
     * if !condition && (pos+len) < strlen(base)
     *      arg0 = substr0 . substr3 . substr 4
     *      substr0.len = pos
     *      substr3.len = len
     *      return substr3
     *
     *
     *
     */
    void theory_str::instantiate_axiom_substr(enode * e) {
        context & ctx = get_context();
        ast_manager & m = get_manager();
        expr* base = nullptr;
        expr* pos = nullptr;
        expr* len = nullptr;
        expr* arg0;
        expr* arg1;
        app * expr = e->get_owner();

        if (axiomatized_terms.contains(expr)) {
            return;
        }
        axiomatized_terms.insert(expr);

        TRACE("str", tout << __FUNCTION__ << ":" << mk_pp(expr, m) << std::endl;);

        VERIFY(u.str.is_extract(expr, base, pos, len));

        expr_ref zero(m_autil.mk_numeral(rational::zero(), true), m);
        expr_ref minusOne(m_autil.mk_numeral(rational::minus_one(), true), m);

        expr_ref_vector argumentsValid_terms(m);
        // pos >= 0
        argumentsValid_terms.push_back(m_autil.mk_ge(pos, zero));
        // pos < strlen(base)
        argumentsValid_terms.push_back(mk_not(m, m_autil.mk_ge(
                m_autil.mk_add(pos, m_autil.mk_mul(minusOne, mk_strlen(base))),
                zero)));

        // len >= 0
        argumentsValid_terms.push_back(m_autil.mk_ge(len, zero));


        // (pos+len) >= strlen(base)
        // --> pos + len + -1*strlen(base) >= 0
        expr_ref lenOutOfBounds(m_autil.mk_ge(
                m_autil.mk_add(pos, len, m_autil.mk_mul(minusOne, mk_strlen(base))),
                zero), m);
        expr_ref argumentsValid = mk_and(argumentsValid_terms);

        // Case 1: pos < 0 or pos >= strlen(base) or len < 0
        // ==> (Substr ...) = ""
        expr_ref case1_premise(m.mk_not(argumentsValid), m);
        expr_ref case1_conclusion(ctx.mk_eq_atom(expr, mk_string("")), m);
        expr_ref case1(m.mk_implies(case1_premise, case1_conclusion), m);

        bool startFromHead = false;
        rational startingInteger;
        if (m_autil.is_numeral(pos, startingInteger) && startingInteger.is_zero()) {
            startFromHead = true;
        }

        expr_ref_vector case2_conclusion_terms(m);
        expr_ref_vector case3_conclusion_terms(m);

        // Case 2: (pos >= 0 and pos < strlen(base) and len >= 0) and (pos+len) >= strlen(base)
        // ==> base = substr0 . substr3 . substr4 AND len(t0) = pos AND (Substr ...) = t1
        expr_ref t0(mk_str_var("substr0"), m);
        expr_ref t3(mk_str_var("substr3"), m);
        expr_ref t4(mk_str_var("substr4"), m);

        if (!startFromHead) {
            case2_conclusion_terms.push_back(ctx.mk_eq_atom(base, mk_concat(t0, mk_concat(t3, t4))));
            case2_conclusion_terms.push_back(ctx.mk_eq_atom(mk_strlen(t0), pos));

            case3_conclusion_terms.push_back(ctx.mk_eq_atom(base, mk_concat(t0, mk_concat(t3, t4))));
            case3_conclusion_terms.push_back(ctx.mk_eq_atom(mk_strlen(t0), pos));

            sync_index_head(pos, base, t0, mk_concat(t3, t4));
        }
        else {
            case2_conclusion_terms.push_back(ctx.mk_eq_atom(base, mk_concat(t3, t4)));
            case3_conclusion_terms.push_back(ctx.mk_eq_atom(base, mk_concat(t3, t4)));

            sync_index_head(len, base, t3, t4);
        }

        case2_conclusion_terms.push_back(ctx.mk_eq_atom(expr, t3));
        case2_conclusion_terms.push_back(ctx.mk_eq_atom(mk_strlen(t4), mk_int(0)));

        expr_ref case2_conclusion(mk_and(case2_conclusion_terms), m);
        expr_ref_vector premises(m);
        premises.push_back(argumentsValid);
        premises.push_back(lenOutOfBounds);
        expr_ref premise_expr(m);
        premise_expr = createAndOperator(premises);
        expr_ref case2(m.mk_implies(premise_expr, case2_conclusion), m);

        // Case 3: (pos >= 0 and pos < strlen(base) and len >= 0) and (pos+len) < strlen(base)
        // ==> base = t0.t3.t4 AND len(t0) = pos AND len(t3) = len AND (Substr ...) = t3

        case3_conclusion_terms.push_back(ctx.mk_eq_atom(mk_strlen(t3), len));
        case3_conclusion_terms.push_back(ctx.mk_eq_atom(expr, t3));

        expr_ref case3_conclusion(mk_and(case3_conclusion_terms), m);
        expr_ref case3(m.mk_implies(m.mk_and(argumentsValid, m.mk_not(lenOutOfBounds)), case3_conclusion), m);

        {
            th_rewriter rw(m);

            expr_ref case1_rw(case1, m);
            rw(case1_rw);
            assert_axiom(case1_rw);

            expr_ref case2_rw(case2, m);
            rw(case2_rw);
            assert_axiom(case2_rw);

            expr_ref case3_rw(case3, m);
            rw(case3_rw);
            assert_axiom(case3_rw);
        }
    }

    void theory_str::sync_index_head(expr* pos, expr* base, expr* first_part, expr* second_part){
        context & ctx = get_context();
        ast_manager & m = get_manager();
        STRACE("str",
               tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(pos, m) << " = " << mk_pp(first_part, m) << std::endl;);
        if (u.str.is_index(to_app(pos))){
            if (to_app(pos)->get_arg(0) == base){
                // index >= 0 --> substr0 == head of index
                if (index_head.contains(pos)) {
                    assert_axiom(ctx.mk_eq_atom(first_part, index_head[pos]));
                    STRACE("str",
                           tout << __LINE__ << " " << __FUNCTION__ << " update index head vs substring " << mk_pp(first_part, m) << " = " << mk_pp(index_head[pos], m)
                                << std::endl;);
                }
                else {
                    index_head.insert(pos, first_part);
                    STRACE("str",
                           tout << __LINE__ << " " << __FUNCTION__ << " update index head vs substring " << mk_pp(first_part, m) << " = " << mk_pp(index_head[pos], m)
                                << std::endl;);
                }
            }
        }
        else {
            expr* arg0 = nullptr;
            expr* arg1 = nullptr;
            if (m_autil.is_add(pos, arg0, arg1)){
                STRACE("str",
                       tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(pos, m) << " = " << mk_pp(first_part, m)
                            << std::endl;);
                if (u.str.is_index(to_app(arg0))){
                    zstring value;
                    if (u.str.is_string(to_app(arg0)->get_arg(1), value)){
                        if (arg1 == mk_int(value.length())){
                            if (index_tail.contains(arg0)) {
                                if (second_part != index_tail[arg0].second)
                                    assert_axiom(ctx.mk_eq_atom(second_part, index_tail[arg0].second));
                                if (first_part != index_tail[arg0].first)
                                    assert_axiom(ctx.mk_eq_atom(first_part, index_tail[arg0].first));

                                if (u.str.is_concat(index_tail[arg0].first)) {
                                    expr* concat_0 = to_app(index_tail[arg0].first)->get_arg(0);
                                    expr* concat_1 = to_app(index_tail[arg0].first)->get_arg(1);
                                    length_relation.insert(std::make_pair(first_part, concat_0));
                                    length_relation.insert(std::make_pair(first_part, concat_1));
                                }

                                STRACE("str",
                                       tout << __LINE__ << " " << __FUNCTION__ << " update index tail vs substring " << mk_pp(first_part, m) << " = " << mk_pp(index_tail[arg0].second, m)
                                            << std::endl;);
                            }
                            else {
                                index_tail.insert(arg0, std::make_pair(first_part, second_part));
                                STRACE("str",
                                       tout << __LINE__ << " " << __FUNCTION__ << " update index tail vs substring " << mk_pp(first_part, m) << " = " << mk_pp(index_tail[arg0].second, m)
                                            << std::endl;);
                            }
                        }
                    }
                }
                else if (u.str.is_index(to_app(arg1))) {
                    zstring value;
                    if (u.str.is_string(to_app(arg1)->get_arg(1), value)){
                        if (arg0 == mk_int(value.length())){
                            if (index_tail.contains(arg1)) {
                                if (second_part != index_tail[arg1].second)
                                    assert_axiom(ctx.mk_eq_atom(second_part, index_tail[arg1].second));
                                if (first_part != index_tail[arg1].first)
                                    assert_axiom(ctx.mk_eq_atom(first_part, index_tail[arg1].first));

                                if (u.str.is_concat(index_tail[arg1].first)) {
                                    expr* concat_0 = to_app(index_tail[arg1].first)->get_arg(0);
                                    expr* concat_1 = to_app(index_tail[arg1].first)->get_arg(1);
                                    length_relation.insert(std::make_pair(first_part, concat_0));
                                    length_relation.insert(std::make_pair(first_part, concat_1));
                                }

                                STRACE("str",
                                       tout << __LINE__ << " " << __FUNCTION__ << " update index tail vs substring " << mk_pp(first_part, m) << " = " << mk_pp(index_tail[arg1].first, m)
                                            << std::endl;);
                            }
                            else {
                                index_tail.insert(arg1, std::make_pair(first_part, second_part));
                                STRACE("str",
                                       tout << __LINE__ << " " << __FUNCTION__ << " update index tail vs substring " << mk_pp(first_part, m) << " = " << mk_pp(index_tail[arg1].first, m)
                                            << std::endl;);
                            }
                        }
                    }
                }
            }
        }
    }
    /*
     * Similar to IndexOf
     * If arg0 contains arg1
     * then    arg0 = replace1 . arg1 . replace2
     *         result = replace1 . arg2 . replace2
     *              if needle.len = 1, then
     *                  replace1 does not contain arg1
     *              else
     *                  arg0 = x3 . x4
     *                  x3.len = replace1.len + arg1.len - 1
     *                  x3 does not contain arg1
     * else
     *         result = arg0
     *
     */
    void theory_str::instantiate_axiom_replace(enode * e) {
        context & ctx = get_context();
        ast_manager & m = get_manager();

        app * expr = e->get_owner();

        if (axiomatized_terms.contains(expr)) {
            return;
        }
        axiomatized_terms.insert(expr);

        TRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ":" << mk_pp(expr, m) << std::endl;);
        std::pair<app*, app*> value;
        expr_ref haystack(expr->get_arg(0), m), needle(expr->get_arg(1), m);
        app* a = u.str.mk_contains(haystack, needle);
        enode* key = ensure_enode(a);
        if (contain_split_map.contains(key)) {
            std::pair<enode *, enode *> tmpvalue = contain_split_map[key];
            value = std::make_pair<app *, app *>(tmpvalue.first->get_owner(), tmpvalue.second->get_owner());
        }
        else {
            value = std::make_pair<app*, app*>(mk_str_var("replace1"), mk_str_var("replace2"));
            contain_split_map.insert(key, std::make_pair(ctx.get_enode(value.first), ctx.get_enode(value.second)));
        }

        if (u.str.is_extract(haystack.get())){
            app* substr = to_app(haystack.get());
            rational ra;
            if (m_autil.is_numeral(substr->get_arg(1), ra) && ra.get_int64() == 0){
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " found substr contain " << mk_pp(haystack.get(), m) << std::endl;);
                if (contain_pair_bool_map.contains(std::make_pair(substr->get_arg(0), needle.get()))) {
                    app *rootContain = mk_contains(substr->get_arg(0), needle);
                    enode* keynode = ensure_enode(rootContain);
                    SASSERT(contain_split_map.contains(keynode));
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " trying new assert " << mk_pp(haystack.get(), m) << std::endl;);
                    assert_axiom(createEqualOperator(value.first, contain_split_map[keynode].first->get_owner()));
                }
            }
        }

        for (const auto& p : contain_pair_bool_map){
            if (u.str.is_extract(p.get_key1()) && p.get_key2() == needle.get()){
                app* substr = to_app(p.get_key1());
                rational ra;
                if (substr->get_arg(0) == haystack.get() &&
                    m_autil.is_numeral(substr->get_arg(1), ra) && ra.get_int64() == 0){
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " found substr contain " << mk_pp(haystack.get(), m) << std::endl;);
                    app *rootContain = mk_contains(p.get_key1(), needle.get());
                    enode* keynode = ensure_enode(rootContain);
                    SASSERT(contain_split_map.contains(keynode));
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " trying new assert " << mk_pp(haystack.get(), m) << std::endl;);
                    assert_axiom(createEqualOperator(value.first, contain_split_map[keynode].first->get_owner()));
                }
            }
        }

        expr_ref x1(value.first, m);
        expr_ref x2(value.second, m);
        expr_ref result(mk_str_var("result"), m);

        // condAst = Contains(args[0], args[1])
        expr_ref condAst(mk_contains(expr->get_arg(0), expr->get_arg(1)), m);
        // -----------------------
        // true branch
        expr_ref_vector thenItems(m);
        //  args[0] = x1 . args[1] . x2
        thenItems.push_back(ctx.mk_eq_atom(expr->get_arg(0), mk_concat(x1, mk_concat(expr->get_arg(1), x2))));

        bool singleCharCase = false;
        zstring needleStr;
        if (u.str.is_string(expr->get_arg(1), needleStr)) {
            if (needleStr.length() == 1) {
                singleCharCase = true;
            }
        }

        if (singleCharCase) {
            assert_axiom(mk_not(m, mk_contains(x1, expr->get_arg(1))));
//            thenItems.push_back(mk_not(m, mk_contains(x1, expr->get_arg(1))));
        }
        else {
            //  args[0]  = x3 . x4 /\ |x3| = |x1| + |args[1]| - 1 /\ ! contains(x3, args[1])

            expr_ref x3(mk_str_var("replace3"), m);
            expr_ref x4(mk_str_var("replace4"), m);
            expr_ref tmpLen(m_autil.mk_add(mk_strlen(x1), mk_strlen(expr->get_arg(1)), mk_int(-1)), m);
            thenItems.push_back(ctx.mk_eq_atom(expr->get_arg(0), mk_concat(x3, x4)));
            thenItems.push_back(ctx.mk_eq_atom(mk_strlen(x3), tmpLen));
            thenItems.push_back(mk_not(m, mk_contains(x3, expr->get_arg(1))));
        }
        thenItems.push_back(ctx.mk_eq_atom(result, mk_concat(x1, mk_concat(expr->get_arg(2), x2))));

        // -----------------------
        // false branch
        expr_ref elseBranch(ctx.mk_eq_atom(result, expr->get_arg(0)), m);

        th_rewriter rw(m);

        expr_ref breakdownAssert(m.mk_ite(condAst, m.mk_and(thenItems.size(), thenItems.c_ptr()), elseBranch), m);
        expr_ref breakdownAssert_rw(breakdownAssert, m);
        rw(breakdownAssert_rw);
        assert_axiom(breakdownAssert_rw);

        expr_ref reduceToResult(ctx.mk_eq_atom(expr, result), m);
        expr_ref reduceToResult_rw(reduceToResult, m);
        rw(reduceToResult_rw);
        assert_axiom(reduceToResult_rw);
    }

    void theory_str::instantiate_axiom_regexIn(enode * e) {
        context &ctx = get_context();
        ast_manager &m = get_manager();

        app *ex = e->get_owner();
        if (axiomatized_terms.contains(ex)) {
            TRACE("str", tout << "already set up RegexIn axiom for " << mk_pp(ex, m) << std::endl;);
            return;
        }
        axiomatized_terms.insert(ex);

        TRACE("str", tout << __LINE__ << __FUNCTION__ << ":" << mk_pp(ex, m) << std::endl;);

        {
            zstring regexStr = get_std_regex_str(ex->get_arg(1));
            std::pair<expr *, zstring> key1(ex->get_arg(0), regexStr);
            // skip Z3str's map check, because we already check if we set up axioms on this term
            regex_in_bool_map[key1] = ex;
            if (!regex_in_var_reg_str_map.contains(ex->get_arg(0))) {
                regex_in_var_reg_str_map.insert(ex->get_arg(0), std::set<zstring>());
            }
            regex_in_var_reg_str_map[ex->get_arg(0)].insert(regexStr);
        }

        expr_ref str(ex->get_arg(0), m);
        app *regex = to_app(ex->get_arg(1));

        if (m_params.m_RegexAutomata) {
            regex_terms.insert(ex);
            if (!regex_terms_by_string.contains(str)) {
                regex_terms_by_string.insert(str, ptr_vector<expr>());
            }
            regex_terms_by_string[str].push_back(ex);

            expr* tmp = is_regex_plus_breakdown(regex);
            if (tmp != nullptr){
                regex = to_app(tmp);
                m_delayed_assertions_todo.push_back(rewrite_implication(ex, createGreaterEqOperator(mk_strlen(ex->get_arg(0)), mk_int(1))));
            }

            std::vector<expr*> regexElements = combine_const_str(parse_regex_components(remove_star_in_star(regex)));
            int boundLen = 100000;
            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ":" << regexElements.size() << std::endl;);
            expr_ref_vector ors(m);
            for (const auto& v : regexElements) {
                ensure_enode(v);
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ":" << mk_pp(v, m) << std::endl;);
                int tmpLen = 0;
                ptr_vector <expr> elements;
                get_nodes_in_reg_concat(v, elements);
                expr* concat = nullptr;
                for (int i  = 0; i < elements.size(); ++i) {
                    zstring tmpStr;
                    if (u.re.is_to_re(elements[i])) {
                        zstring value;
                        u.str.is_string(to_app(elements[i])->get_arg(0), value);
                        tmpLen += value.length();
                        concat = concat == nullptr ? to_app(elements[i])->get_arg(0) : u.str.mk_concat(concat, to_app(elements[i])->get_arg(0));
                    }
                    else if (u.re.is_plus(elements[i]) || u.re.is_union(elements[i])) {
                        std::vector<zstring> tmpVector;
                        collect_alternative_components(elements[i], tmpVector);
                        std::set<int> lenElements;
                        if (tmpVector.size() > 0) {
                            int minLen = tmpVector[0].length();
                            for (const auto &s : tmpVector) {
                                minLen = std::min(minLen, (int) s.length());
                                lenElements.insert(s.length());
                            }
                            tmpLen += minLen;
                        }

                        expr* tmp = mk_str_var(expr2str(elements[i]));
                        expr* tmp_in_re = u.re.mk_in_re(tmp, elements[i]);
                        m_delayed_assertions_todo.push_back(tmp_in_re);

                        if (u.re.is_union(elements[i])) {
                            int maxLen = 0;
                            expr_ref_vector orsTmp(m);
                            for (const auto& l : lenElements) {
                                maxLen = maxLen > l ? maxLen : l;
                                expr* tmpExpr = createEqualOperator(mk_strlen(tmp), mk_int(l));
                                orsTmp.push_back(tmpExpr);
                            }
                            if ((int)orsTmp.size() > 1) {
                                assert_axiom(createLessEqOperator(mk_strlen(tmp), mk_int(maxLen)));
                            }
                            else if (orsTmp.size() == 1){
                                assert_axiom(createOrOperator(orsTmp));
                            }
                        }
                        concat = concat == nullptr ? tmp : u.str.mk_concat(concat, tmp);
                    }
                    else if (u.re.is_star(elements[i])) {
                        expr* tmp = mk_str_var(expr2str(elements[i]));
                        expr* tmp_in_re = u.re.mk_in_re(tmp, elements[i]);
                        m_delayed_assertions_todo.push_back(tmp_in_re);
                        concat = concat == nullptr ? tmp : u.str.mk_concat(concat, tmp);
                    }
                    else if (u.re.is_full_char(elements[i])) {
                        expr* tmp = mk_str_var(expr2str(elements[i]));
                        assert_axiom(createEqualOperator(mk_strlen(tmp), mk_int(1)));
                        concat = concat == nullptr ? tmp : u.str.mk_concat(concat, tmp);
                    }
                    else if (u.re.is_full_seq(elements[i])){
                        expr* tmp = mk_str_var(expr2str(elements[i]));
                        concat = concat == nullptr ? tmp : u.str.mk_concat(concat, tmp);
                    }
                    ensure_enode(concat);
                    ensure_enode(mk_strlen(concat));
                }

                boundLen = boundLen < tmpLen ? boundLen : tmpLen;
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ":" << mk_pp(str, m) << " " << mk_pp(concat, m) << std::endl;);
                ors.push_back(createEqualOperator(str.get(), concat));
            }

            assert_implication(ex, createOrOperator(ors));
//            assert_implication(ex, createGreaterEqOperator(mk_strlen(str.get()), mk_int(boundLen)));
            return;
        }

        // quick reference for the following code:
        //  - ex: top-level regex membership term
        //  - str: string term appearing in ex
        //  - regex: regex term appearing in ex
        //  ex ::= (str.in.re str regex)
        STRACE("str", tout << __LINE__ << " "  << __FUNCTION__ << ":" << mk_pp(ex, m) << std::endl;);

        if (u.re.is_to_re(regex)) {
            STRACE("str", tout << __LINE__ << " "  << __FUNCTION__ << ":" << mk_pp(ex, m) << std::endl;);

            expr_ref rxStr(regex->get_arg(0), m);
            // want to assert 'expr IFF (str == rxStr)'
            expr_ref rhs(ctx.mk_eq_atom(str, rxStr), m);
            expr_ref finalAxiom(m.mk_iff(ex, rhs), m);
            SASSERT(finalAxiom);
            assert_axiom(finalAxiom);
            STRACE("str",
                  tout << __LINE__ << " "  << "set up Str2Reg: (RegexIn " << mk_pp(str, m) << " " << mk_pp(regex, m) << ")" << std::endl;);
        } else if (u.re.is_concat(regex)) {
            STRACE("str", tout << __LINE__ << " "  << __FUNCTION__ << ":" << mk_pp(ex, m) << std::endl;);

            expr_ref var1(mk_regex_rep_var(), m);
            expr_ref var2(mk_regex_rep_var(), m);
            expr_ref rhs(mk_concat(var1, var2), m);
            expr_ref rx1(regex->get_arg(0), m);
            expr_ref rx2(regex->get_arg(1), m);
            expr_ref var1InRegex1(mk_regexIn(var1, rx1), m);
            expr_ref var2InRegex2(mk_regexIn(var2, rx2), m);

            expr_ref_vector items(m);
            items.push_back(var1InRegex1);
            items.push_back(var2InRegex2);
            items.push_back(ctx.mk_eq_atom(ex, ctx.mk_eq_atom(str, rhs)));

            expr_ref finalAxiom(mk_and(items), m);
            SASSERT(finalAxiom);
            assert_axiom(finalAxiom);
        } else if (u.re.is_union(regex)) {
            STRACE("str", tout << __LINE__ << " "  << __FUNCTION__ << ":" << mk_pp(ex, m) << std::endl;);

            expr_ref var1(mk_regex_rep_var(), m);
            expr_ref var2(mk_regex_rep_var(), m);
            expr_ref orVar(m.mk_or(ctx.mk_eq_atom(str, var1), ctx.mk_eq_atom(str, var2)), m);
            expr_ref regex1(regex->get_arg(0), m);
            expr_ref regex2(regex->get_arg(1), m);
            expr_ref var1InRegex1(mk_regexIn(var1, regex1), m);
            expr_ref var2InRegex2(mk_regexIn(var2, regex2), m);
            expr_ref_vector items(m);
            items.push_back(var1InRegex1);
            items.push_back(var2InRegex2);
            items.push_back(ctx.mk_eq_atom(ex, orVar));
            assert_axiom(mk_and(items));

        } else if (u.re.is_star(regex)) {
            // slightly more complex due to the unrolling step.
            expr_ref regex1(regex->get_arg(0), m);
            expr_ref unrollCount(mk_unroll_bound_var(), m);
            expr_ref unrollFunc(mk_unroll(regex1, unrollCount), m);
            expr_ref_vector items(m);
            items.push_back(ctx.mk_eq_atom(ex, ctx.mk_eq_atom(str, unrollFunc)));
            items.push_back(
                    ctx.mk_eq_atom(ctx.mk_eq_atom(unrollCount, mk_int(0)), ctx.mk_eq_atom(unrollFunc, mk_string(""))));
            expr_ref finalAxiom(mk_and(items), m);
            SASSERT(finalAxiom);
            assert_axiom(finalAxiom);
        } else if (u.re.is_range(regex)) {
            // (re.range "A" "Z") unfolds to (re.union "A" "B" ... "Z");
            // we rewrite to expr IFF (str = "A" or str = "B" or ... or str = "Z")
            expr_ref lo(regex->get_arg(0), m);
            expr_ref hi(regex->get_arg(1), m);
            zstring str_lo, str_hi;
            SASSERT(u.str.is_string(lo));
            SASSERT(u.str.is_string(hi));
            u.str.is_string(lo, str_lo);
            u.str.is_string(hi, str_hi);
            SASSERT(str_lo.length() == 1);
            SASSERT(str_hi.length() == 1);
            unsigned int c1 = str_lo[0];
            unsigned int c2 = str_hi[0];
            if (c1 > c2) {
                // exchange
                unsigned int tmp = c1;
                c1 = c2;
                c2 = tmp;
            }
            expr_ref_vector range_cases(m);
            for (unsigned int ch = c1; ch <= c2; ++ch) {
                zstring s_ch(ch);
                expr_ref rhs(ctx.mk_eq_atom(str, u.str.mk_string(s_ch)), m);
                range_cases.push_back(rhs);
            }
            expr_ref rhs(mk_or(range_cases), m);
            expr_ref finalAxiom(m.mk_iff(ex, rhs), m);
            SASSERT(finalAxiom);
            assert_axiom(finalAxiom);
        } else if (u.re.is_full_seq(regex)) {
            // trivially true for any string!
            assert_axiom(ex);
        } else if (u.re.is_full_char(regex)) {
            // any char = any string of length 1
            expr_ref rhs(ctx.mk_eq_atom(mk_strlen(str), mk_int(1)), m);
            expr_ref finalAxiom(m.mk_iff(ex, rhs), m);
            SASSERT(finalAxiom);
            assert_axiom(finalAxiom);
        } else {
            STRACE("str", tout << __LINE__ << " "  << "ERROR: unknown regex expression " << mk_pp(regex, m) << "!" << std::endl;);
            NOT_IMPLEMENTED_YET();
        }
    }

    expr* theory_str::is_regex_plus_breakdown(expr* e){
        if (u.re.is_concat(e)){
            expr* arg0 = to_app(e)->get_arg(0);
            expr* arg1 = to_app(e)->get_arg(1);

            if (u.re.is_star(arg1)){
                expr* arg10 = to_app(arg1)->get_arg(0);
                if (arg10 == arg0)
                    return arg1;
            }

            if (u.re.is_star(arg0)){
                expr* arg00 = to_app(arg0)->get_arg(0);
                if (arg00 == arg1)
                    return arg0;
            }
        }
        return nullptr;
    }

    void theory_str::instantiate_axiom_str_to_int(enode * e) {
        context & ctx = get_context();
        ast_manager & m = get_manager();

        app * ex = e->get_owner();
        if (axiomatized_terms.contains(ex)) {
            TRACE("str", tout << "already set up str.to-int axiom for " << mk_pp(ex, m) << std::endl;);
            return;
        }
        axiomatized_terms.insert(ex);

        TRACE("str", tout << "instantiate str.to-int axiom for " << mk_pp(ex, m) << std::endl;);

        // let expr = (str.to-int S)
        // axiom 1: expr >= -1
        // axiom 2: expr = 0 <==> S = "0"

        expr * S = ex->get_arg(0);
        {
            expr_ref axiom1(m_autil.mk_ge(ex, m_autil.mk_numeral(rational::minus_one(), true)), m);
            SASSERT(axiom1);
            assert_axiom(axiom1);
        }

        expr_ref s2i(mk_int_var("s2i"), m);
        assert_axiom(ctx.mk_eq_atom(s2i, ex));
    }

    void theory_str::instantiate_axiom_int_to_str(enode * e) {
        context & ctx = get_context();
        ast_manager & m = get_manager();

        app * ex = e->get_owner();
        if (axiomatized_terms.contains(ex)) {
            TRACE("str", tout << "already set up str.from-int axiom for " << mk_pp(ex, m) << std::endl;);
            return;
        }
        axiomatized_terms.insert(ex);

        TRACE("str", tout << "instantiate str.from-int axiom for " << mk_pp(ex, m) << std::endl;);

        // axiom 1: N < 0 <==> (str.from-int N) = ""
        expr * N = ex->get_arg(0);
        {
            expr_ref axiom1_lhs(mk_not(m, m_autil.mk_ge(N, m_autil.mk_numeral(rational::zero(), true))), m);
            expr_ref axiom1_rhs(ctx.mk_eq_atom(ex, mk_string("")), m);
            expr_ref axiom1(ctx.mk_eq_atom(axiom1_lhs, axiom1_rhs), m);
            SASSERT(axiom1);
            assert_axiom(axiom1);
        }
        expr_ref i2s(mk_str_var("i2s"), m);
        assert_axiom(ctx.mk_eq_atom(i2s, ex));
    }

    app * theory_str::mk_strlen(expr * e) {
        app* tmp = u.str.mk_length(e);
        ensure_enode(tmp);
        return tmp;
    }

    expr * theory_str::mk_string(zstring const& str) {
        if (m_params.m_StringConstantCache) {
            ++totalCacheAccessCount;
            expr * val;
            if (stringConstantCache.find(str, val)) {
                return val;
            } else {
                val = u.str.mk_string(str);
                m_trail.push_back(val);
                stringConstantCache.insert(str, val);
                return val;
            }
        } else {
            return u.str.mk_string(str);
        }
    }

    expr * theory_str::mk_string(const char * str) {
        symbol sym(str);
        return u.str.mk_string(sym);
    }

    app * theory_str::mk_fresh_const(char const* name, sort* s) {
        string_buffer<64> buffer;
        buffer << name;
        buffer << "!tmp";
        buffer << m_fresh_id;
        m_fresh_id++;
        return u.mk_skolem(symbol(buffer.c_str()), 0, nullptr, s);
    }

    app * theory_str::mk_str_var(std::string name) {
        context & ctx = get_context();

        sort * string_sort = u.str.mk_string_sort();
        app * a = mk_fresh_const(name.c_str(), string_sort);
        m_trail.push_back(a);

        // I have a hunch that this may not get internalized for free...
        ctx.internalize(a, false);
        SASSERT(ctx.get_enode(a) != NULL);
        SASSERT(ctx.e_internalized(a));
        // this might help??
        mk_var(ctx.get_enode(a));
        m_basicstr_axiom_todo.push_back(ctx.get_enode(a));

        variable_set.insert(a);
        internal_variable_set.insert(a);
        track_variable_scope(a);

        return a;
    }

    expr * theory_str::mk_concat(expr * n1, expr * n2) {
        context &ctx = get_context();
        ast_manager &m = get_manager();
        ENSURE(n1 != nullptr);
        ENSURE(n2 != nullptr);
        bool n1HasEqcValue = false;
        bool n2HasEqcValue = false;
        n1 = get_eqc_value(n1, n1HasEqcValue);
        n2 = get_eqc_value(n2, n2HasEqcValue);
        if (n1HasEqcValue && n2HasEqcValue) {
            return mk_concat_const_str(n1, n2);
        } else if (n1HasEqcValue && !n2HasEqcValue) {
            bool n2_isConcatFunc = u.str.is_concat(to_app(n2));
            zstring n1_str;
            u.str.is_string(n1, n1_str);
            if (n1_str.empty()) {
                return n2;
            }
            if (n2_isConcatFunc) {
                expr *n2_arg0 = to_app(n2)->get_arg(0);
                expr *n2_arg1 = to_app(n2)->get_arg(1);
                if (u.str.is_string(n2_arg0)) {
                    n1 = mk_concat_const_str(n1, n2_arg0); // n1 will be a constant
                    n2 = n2_arg1;
                }
            }
        } else if (!n1HasEqcValue && n2HasEqcValue) {
            zstring n2_str;
            u.str.is_string(n2, n2_str);
            if (n2_str.empty()) {
                return n1;
            }

            if (u.str.is_concat(to_app(n1))) {
                expr *n1_arg0 = to_app(n1)->get_arg(0);
                expr *n1_arg1 = to_app(n1)->get_arg(1);
                if (u.str.is_string(n1_arg1)) {
                    n1 = n1_arg0;
                    n2 = mk_concat_const_str(n1_arg1, n2); // n2 will be a constant
                }
            }
        } else {
            if (u.str.is_concat(to_app(n1)) && u.str.is_concat(to_app(n2))) {
                expr *n1_arg0 = to_app(n1)->get_arg(0);
                expr *n1_arg1 = to_app(n1)->get_arg(1);
                expr *n2_arg0 = to_app(n2)->get_arg(0);
                expr *n2_arg1 = to_app(n2)->get_arg(1);
                if (u.str.is_string(n1_arg1) && u.str.is_string(n2_arg0)) {
                    expr *tmpN1 = n1_arg0;
                    expr *tmpN2 = mk_concat_const_str(n1_arg1, n2_arg0);
                    n1 = mk_concat(tmpN1, tmpN2);
                    n2 = n2_arg1;
                }
            }
        }

        //------------------------------------------------------
        // * expr * ast1 = mk_2_arg_app(ctx, td->Concat, n1, n2);
        // * expr * ast2 = mk_2_arg_app(ctx, td->Concat, n1, n2);
        // Z3 treats (ast1) and (ast2) as two different nodes.
        //-------------------------------------------------------
        expr *concatAst = nullptr;

        if (!concat_astNode_map.find(n1, n2, concatAst)) {
            concatAst = u.str.mk_concat(n1, n2);
            m_trail.push_back(concatAst);
            concat_astNode_map.insert(n1, n2, concatAst);

            expr_ref concat_length(mk_strlen(concatAst), m);

            ptr_vector<expr> childrenVector;
            get_nodes_in_concat(concatAst, childrenVector);
            expr_ref_vector items(m);
            for (auto el : childrenVector) {
                items.push_back(mk_strlen(el));
            }

            // len = sum len
            expr_ref lenAssert(ctx.mk_eq_atom(concat_length, m_autil.mk_add(items.size(), items.c_ptr())), m);
            assert_axiom(lenAssert);

//            if (!is_contain_equality(concatAst, tmp))
            {
                // | n1 | = 0 --> concat = n2
                expr_ref premise00(ctx.mk_eq_atom(mk_int(0), mk_strlen(n1)), m);
                expr_ref conclusion00(createEqualOperator(concatAst, n2), m);
                assert_implication(premise00, conclusion00);

                // | n2 | = 0 --> concat = n1
                expr_ref premise01(ctx.mk_eq_atom(mk_int(0), mk_strlen(n2)), m);
                expr_ref conclusion01(createEqualOperator(concatAst, n1), m);
                assert_implication(premise01, conclusion01);
            }
        }
        return concatAst;
    }

    app * theory_str::mk_int(int n) {
        return m_autil.mk_numeral(rational(n), true);
    }

    app * theory_str::mk_int(rational & q) {
        return m_autil.mk_numeral(q, true);
    }

    app * theory_str::mk_contains(expr * haystack, expr * needle) {
        app * contains = u.str.mk_contains(haystack, needle); // TODO double-check semantics/argument order
        m_trail.push_back(contains);
        // immediately force internalization so that axiom setup does not fail
        get_context().internalize(contains, false);
        set_up_axioms(contains);
        return contains;
    }

    // note, this invokes "special-case" handling for the start index being 0
    app * theory_str::mk_indexof(expr * haystack, expr * needle) {
        app * indexof = u.str.mk_index(haystack, needle, mk_int(0));
        m_trail.push_back(indexof);
        // immediately force internalization so that axiom setup does not fail
        get_context().internalize(indexof, false);
        set_up_axioms(indexof);
        return indexof;
    }

    app * theory_str::mk_int_var(std::string name) {
        context & ctx = get_context();
        ast_manager & m = get_manager();

        sort * int_sort = m.mk_sort(m_autil.get_family_id(), INT_SORT);
        app * a = mk_fresh_const(name.c_str(), int_sort);

        ctx.internalize(a, false);
        SASSERT(ctx.get_enode(a) != NULL);
        SASSERT(ctx.e_internalized(a));
        ctx.mark_as_relevant(a);
        // I'm assuming that this combination will do the correct thing in the integer theory.

        //mk_var(ctx.get_enode(a));
        m_trail.push_back(a);
        //variable_set.insert(a);
        //internal_variable_set.insert(a);
        //track_variable_scope(a);

        return a;
    }

    app * theory_str::mk_regex_rep_var() {
        context & ctx = get_context();

        sort * string_sort = u.str.mk_string_sort();
        app * a = mk_fresh_const("regex", string_sort);
        m_trail.push_back(a);

        ctx.internalize(a, false);
        SASSERT(ctx.get_enode(a) != NULL);
        SASSERT(ctx.e_internalized(a));
        mk_var(ctx.get_enode(a));
        m_basicstr_axiom_todo.push_back(ctx.get_enode(a));
        STRACE("str", tout << "add " << mk_pp(a, get_manager()) << " to m_basicstr_axiom_todo" << std::endl;);

        variable_set.insert(a);
        //internal_variable_set.insert(a);
        regex_variable_set.insert(a);
        track_variable_scope(a);

        return a;
    }

    expr * theory_str::mk_regexIn(expr * str, expr * regexp) {
        app * regexIn = u.re.mk_in_re(str, regexp);
        // immediately force internalization so that axiom setup does not fail
        get_context().internalize(regexIn, false);
        set_up_axioms(regexIn);
        return regexIn;
    }

    app * theory_str::mk_unroll(expr * n, expr * bound) {
        context & ctx = get_context();
        ast_manager & m = get_manager();

        expr * args[2] = {n, bound};
        app * unrollFunc = get_manager().mk_app(get_id(), _OP_RE_UNROLL, 0, nullptr, 2, args);
        m_trail.push_back(unrollFunc);

        expr_ref_vector items(m);
        items.push_back(ctx.mk_eq_atom(ctx.mk_eq_atom(bound, mk_int(0)), ctx.mk_eq_atom(unrollFunc, mk_string(""))));
        items.push_back(m_autil.mk_ge(bound, mk_int(0)));
        items.push_back(m_autil.mk_ge(mk_strlen(unrollFunc), mk_int(0)));

        expr_ref finalAxiom(mk_and(items), m);
        SASSERT(finalAxiom);
        assert_axiom(finalAxiom);
        return unrollFunc;
    }

    app * theory_str::mk_unroll_bound_var() {
        return mk_int_var("unroll");
    }

    app * theory_str::mk_str_to_re(expr * n){
        expr * args[1] = {n};
        app * a = get_manager().mk_app(get_id(), _OP_STRING_TO_REGEXP, 0, nullptr, 1, args);
        return a;
    }

    app * theory_str::mk_arr_var(std::string name) {
        context & ctx = get_context();
        ast_manager & m = get_manager();

        STRACE("str", tout << __FUNCTION__ << ":" << name << std::endl;);
        sort * int_sort = m.mk_sort(m_autil.get_family_id(), INT_SORT);
        sort * arr_sort = m_arrayUtil.mk_array_sort(int_sort, int_sort);
        app * a = mk_fresh_const(name.c_str(), arr_sort);
        ctx.internalize(a, false);
        ctx.mark_as_relevant(a);
        // I'm assuming that this combination will do the correct thing in the integer theory.

        m_trail.push_back(a);

        return a;
    }

    void theory_str::get_nodes_in_concat(expr * node, ptr_vector<expr> & nodeList) {
        app * a_node = to_app(node);
        if (!u.str.is_concat(a_node)) {
            nodeList.push_back(node);
            return;
        } else {
            SASSERT(a_node->get_num_args() == 2);
            expr * leftArg = a_node->get_arg(0);
            expr * rightArg = a_node->get_arg(1);
            get_nodes_in_concat(leftArg, nodeList);
            get_nodes_in_concat(rightArg, nodeList);
        }
    }

    void theory_str::get_nodes_in_reg_concat(expr * node, ptr_vector<expr> & nodeList) {
        app * a_node = to_app(node);
        if (!u.re.is_concat(a_node)) {
            nodeList.push_back(node);
            return;
        } else {
            SASSERT(a_node->get_num_args() == 2);
            expr * leftArg = a_node->get_arg(0);
            expr * rightArg = a_node->get_arg(1);
            get_nodes_in_reg_concat(leftArg, nodeList);
            get_nodes_in_reg_concat(rightArg, nodeList);
        }
    }

    void theory_str::get_all_nodes_in_concat(expr * node, ptr_vector<expr> & nodeList) {
        app * a_node = to_app(node);
        if (!u.str.is_concat(a_node)) {
            nodeList.push_back(node);
            return;
        } else {
            SASSERT(a_node->get_num_args() == 2);
            nodeList.push_back(node);
            expr * leftArg = a_node->get_arg(0);
            expr * rightArg = a_node->get_arg(1);
            get_all_nodes_in_concat(leftArg, nodeList);
            get_all_nodes_in_concat(rightArg, nodeList);
        }
    }

    /*
     * Returns the simplified concatenation of two expressions,
     * where either both expressions are constant strings
     * or one expression is the empty string.
     * If this precondition does not hold, the function returns NULL.
     * (note: this function was strTheory::Concat())
     */
    expr * theory_str::mk_concat_const_str(expr * n1, expr * n2) {
        bool n1HasEqcValue = false;
        bool n2HasEqcValue = false;
        expr * v1 = get_eqc_value(n1, n1HasEqcValue);
        expr * v2 = get_eqc_value(n2, n2HasEqcValue);
        if (u.str.is_string(v1)) {
            n1HasEqcValue = true;
        }
        if (u.str.is_string(v2)) {
            n2HasEqcValue = true;
        }
        if (n1HasEqcValue && n2HasEqcValue) {
            zstring n1_str;
            u.str.is_string(v1, n1_str);
            zstring n2_str;
            u.str.is_string(v2, n2_str);
            zstring result = n1_str + n2_str;
            return mk_string(result);
        } else if (n1HasEqcValue && !n2HasEqcValue) {
            zstring n1_str;
            u.str.is_string(v1, n1_str);
            if (n1_str.empty()) {
                return n2;
            }
        } else if (!n1HasEqcValue && n2HasEqcValue) {
            zstring n2_str;
            u.str.is_string(v2, n2_str);
            if (n2_str.empty()) {
                return n1;
            }
        }
        return nullptr;
    }

    /*
     * Look through the equivalence class of n to find a string constant.
     * Return that constant if it is found, and set hasEqcValue to true.
     * Otherwise, return n, and set hasEqcValue to false.
     */

    expr * theory_str::get_eqc_value(expr * n, bool & hasEqcValue) {
        return z3str2_get_eqc_value(n, hasEqcValue);
    }


    // Simulate the behaviour of get_eqc_value() from Z3str2.
    // We only check m_find for a string constant.

    expr * theory_str::z3str2_get_eqc_value(expr * n , bool & hasEqcValue) {
        theory_var curr = get_var(n);
        if (curr != null_theory_var) {
            curr = m_find.find(curr);
            theory_var first = curr;

            do {
                expr* a = get_ast(curr);
                if (u.str.is_string(a)) {
                    hasEqcValue = true;
                    return a;
                }
                curr = m_find.next(curr);
            }
            while (curr != first && curr != null_theory_var);
        }
        hasEqcValue = false;
        return n;
    }

    expr * theory_str::get_eqc_next(expr * n) {
        theory_var v = get_var(n);
        if (v != null_theory_var) {
            theory_var r = m_find.next(v);
            return get_ast(r);
        }
        return n;
    }

    theory_var theory_str::get_var(expr * n) const {
        if (!is_app(n)) {
            return null_theory_var;
        }
        context & ctx = get_context();
        if (ctx.e_internalized(to_app(n))) {
            enode * e = ctx.get_enode(to_app(n));

            return e->get_th_var(get_id());
        }
        return null_theory_var;
    }

    app * theory_str::get_ast(theory_var v) {
        return get_enode(v)->get_owner();
    }

    static zstring str2RegexStr(zstring str) {
        zstring res("");
        int len = str.length();
        for (int i = 0; i < len; i++) {
            char nc = str[i];
            // 12 special chars
            if (nc == '\\' || nc == '^' || nc == '$' || nc == '.' || nc == '|' || nc == '?'
                || nc == '*' || nc == '+' || nc == '(' || nc == ')' || nc == '[' || nc == '{') {
                res = res + zstring("\\");
            }
            char tmp[2] = {(char)str[i], '\0'};
            res = res + zstring(tmp);
        }
        return res;
    }

    zstring theory_str::get_std_regex_str(expr * regex) {
        app *a_regex = to_app(regex);
        if (u.re.is_to_re(a_regex)) {
            expr *regAst = a_regex->get_arg(0);
            zstring regAstVal;
            u.str.is_string(regAst, regAstVal);
            zstring regStr = str2RegexStr(regAstVal);
            return regStr;
        } else if (u.re.is_concat(a_regex)) {
            expr *reg1Ast = a_regex->get_arg(0);
            expr *reg2Ast = a_regex->get_arg(1);
            zstring reg1Str = get_std_regex_str(reg1Ast);
            zstring reg2Str = get_std_regex_str(reg2Ast);
            return zstring("(") + reg1Str + zstring(")(") + reg2Str + zstring(")");
        } else if (u.re.is_union(a_regex)) {
            expr *reg1Ast = a_regex->get_arg(0);
            expr *reg2Ast = a_regex->get_arg(1);
            zstring reg1Str = get_std_regex_str(reg1Ast);
            zstring reg2Str = get_std_regex_str(reg2Ast);
            return zstring("(") + reg1Str + zstring(")|(") + reg2Str + zstring(")");
        } else if (u.re.is_star(a_regex)) {
            expr *reg1Ast = a_regex->get_arg(0);
            zstring reg1Str = get_std_regex_str(reg1Ast);
            return zstring("(") + reg1Str + zstring(")*");
        } else if (u.re.is_range(a_regex)) {
            expr *range1 = a_regex->get_arg(0);
            expr *range2 = a_regex->get_arg(1);
            zstring range1val, range2val;
            u.str.is_string(range1, range1val);
            u.str.is_string(range2, range2val);
            return zstring("[") + range1val + zstring("-") + range2val + zstring("]");
        } else if (u.re.is_loop(a_regex)) {
            expr *body;
            unsigned lo, hi;
            u.re.is_loop(a_regex, body, lo, hi);
            rational rLo(lo);
            rational rHi(hi);
            zstring bodyStr = get_std_regex_str(body);
            return zstring("(") + bodyStr + zstring("{") + zstring(rLo.to_string().c_str()) + zstring(",") +
                   zstring(rHi.to_string().c_str()) + zstring("})");
        } else if (u.re.is_full_seq(a_regex)) {
            return zstring("(.*)");
        } else if (u.re.is_full_char(a_regex)) {
            return zstring("str.allchar");
        } else {
            TRACE("str", tout << "BUG: unrecognized regex term " << mk_pp(regex, get_manager()) << std::endl;);
            UNREACHABLE();
            return zstring("");
        }
    }

    bool theory_str::get_len_value(expr* e, rational& val) {
        if (opt_DisableIntegerTheoryIntegration) {
            TRACE("str", tout << "WARNING: integer theory integration disabled" << std::endl;);
            return false;
        }

        context& ctx = get_context();
        ast_manager & m = get_manager();

        rational val1;
        expr_ref len(m), len_val(m);
        expr* e1, *e2;
        ptr_vector<expr> todo;
        todo.push_back(e);
        val.reset();
        while (!todo.empty()) {
            expr* c = todo.back();
            todo.pop_back();
            if (u.str.is_concat(to_app(c))) {
                e1 = to_app(c)->get_arg(0);
                e2 = to_app(c)->get_arg(1);
                todo.push_back(e1);
                todo.push_back(e2);
            }
            else if (u.str.is_string(to_app(c))) {
                zstring tmp;
                u.str.is_string(to_app(c), tmp);
                unsigned int sl = tmp.length();
                val += rational(sl);
            }
            else {
                len = mk_strlen(c);
                // debugging
//                STRACE("str", {
//                    tout << mk_pp(len, m) << ":" << std::endl
//                         << (ctx.is_relevant(len.get()) ? "relevant" : "not relevant") << std::endl
//                         << (ctx.e_internalized(len) ? "internalized" : "not internalized") << std::endl
//                            ;
//                    if (ctx.e_internalized(len)) {
//                        enode * e_len = ctx.get_enode(len);
//                        tout << "has " << e_len->get_num_th_vars() << " theory vars" << std::endl;
//
//                        // eqc if (ctx.e_internalized(len)) {
//                        enode * e_len = ctx.get_enode(len);
//                        tout << "has " << e_len->get_num_th_vars() << " theory vars" << std::endl;
//
//                        // eqc debugging
//                        {
//                            tout << "dump equivalence class of " << mk_pp(len, get_manager()) << std::endl;
//                            enode * nNode = ctx.get_enode(len);
//                            enode * eqcNode = nNode;
//                            do {
//                                app * ast = eqcNode->get_owner();
//                                tout << mk_pp(ast, get_manager()) << std::endl;
//                                eqcNode = eqcNode->get_next();
//                            } while (eqcNode != nNode);
//                        }
//                    }debugging
//                        {
//                            tout << "dump equivalence class of " << mk_pp(len, get_manager()) << std::endl;
//                            enode * nNode = ctx.get_enode(len);
//                            enode * eqcNode = nNode;
//                            do {
//                                app * ast = eqcNode->get_owner();
//                                tout << mk_pp(ast, get_manager()) << std::endl;
//                                eqcNode = eqcNode->get_next();
//                            } while (eqcNode != nNode);
//                        }
//                    }
//                });

                if (ctx.e_internalized(len) && get_arith_value(len, val1)) {
                    val += val1;
                }
                else {
                    return false;
                }
            }
        }

        return val.is_int();
    }

    bool theory_str::get_arith_value(expr* e, rational& val) const {
        context& ctx = get_context();
        if (!ctx.e_internalized(e)) {
            return false;
        }
        // check root of the eqc for an integer constant
        // if an integer constant exists in the eqc, it should be the root
        enode * en_e = ctx.get_enode(e);
        enode * root_e = en_e->get_root();
        if (m_autil.is_numeral(root_e->get_owner(), val) && val.is_int()) {
            return true;
        } else {
            return false;
        }

    }

    bool theory_str::upper_bound(expr* _e, rational& hi) const {
        context& ctx = get_context();
        ast_manager & m = get_manager();
        expr_ref e(u.str.mk_length(_e), m);
        family_id afid = m_autil.get_family_id();
        expr_ref _hi(m);
        do {
            theory_mi_arith* tha = get_th_arith<theory_mi_arith>(ctx, afid, e);
            if (tha && tha->get_upper(ctx.get_enode(e), _hi)) break;
            theory_i_arith* thi = get_th_arith<theory_i_arith>(ctx, afid, e);
            if (thi && thi->get_upper(ctx.get_enode(e), _hi)) break;
            theory_lra* thr = get_th_arith<theory_lra>(ctx, afid, e);
            if (thr && thr->get_upper(ctx.get_enode(e), _hi)) break;
            return false;
        }
        while (false);
        return m_autil.is_numeral(_hi, hi) && hi.is_int();
    }

    bool theory_str::lower_bound(expr* _e, rational& lo) const {
        context& ctx = get_context();
        ast_manager & m = get_manager();
        expr_ref e(u.str.mk_length(_e), m);
        expr_ref _lo(m);
        family_id afid = m_autil.get_family_id();
        do {
            theory_mi_arith* tha = get_th_arith<theory_mi_arith>(ctx, afid, e);
            if (tha && tha->get_lower(ctx.get_enode(e), _lo)) break;
            theory_i_arith* thi = get_th_arith<theory_i_arith>(ctx, afid, e);
            if (thi && thi->get_lower(ctx.get_enode(e), _lo)) break;
            theory_lra* thr = get_th_arith<theory_lra>(ctx, afid, e);
            if (thr && thr->get_lower(ctx.get_enode(e), _lo)) break;
            return false;
        }
        while (false);
        return m_autil.is_numeral(_lo, lo) && lo.is_int();
    }

    bool theory_str::upper_num_bound(expr* e, rational& hi) const {
        context& ctx = get_context();
        ast_manager & m = get_manager();
        family_id afid = m_autil.get_family_id();
        expr_ref _hi(m);
        do {
            theory_mi_arith* tha = get_th_arith<theory_mi_arith>(ctx, afid, e);
            if (tha && tha->get_upper(ctx.get_enode(e), _hi)) break;
            theory_i_arith* thi = get_th_arith<theory_i_arith>(ctx, afid, e);
            if (thi && thi->get_upper(ctx.get_enode(e), _hi)) break;
            theory_lra* thr = get_th_arith<theory_lra>(ctx, afid, e);
            if (thr && thr->get_upper(ctx.get_enode(e), _hi)) break;
            return false;
        }
        while (false);
        return m_autil.is_numeral(_hi, hi) && hi.is_int();
    }

    bool theory_str::lower_num_bound(expr* e, rational& lo) const {
        context& ctx = get_context();
        ast_manager & m = get_manager();
        expr_ref _lo(m);
        family_id afid = m_autil.get_family_id();
        do {
            theory_mi_arith* tha = get_th_arith<theory_mi_arith>(ctx, afid, e);
            if (tha && tha->get_lower(ctx.get_enode(e), _lo)) break;
            theory_i_arith* thi = get_th_arith<theory_i_arith>(ctx, afid, e);
            if (thi && thi->get_lower(ctx.get_enode(e), _lo)) break;
            theory_lra* thr = get_th_arith<theory_lra>(ctx, afid, e);
            if (thr && thr->get_lower(ctx.get_enode(e), _lo)) break;
            return false;
        }
        while (false);
        return m_autil.is_numeral(_lo, lo) && lo.is_int();
    }

    void theory_str::get_concats_in_eqc(expr * n, std::set<expr*> & concats) {

        expr * eqcNode = n;
        do {
            if (u.str.is_concat(to_app(eqcNode))) {
                concats.insert(eqcNode);
            }
            eqcNode = get_eqc_next(eqcNode);
        } while (eqcNode != n);
    }

    /*
     * Collect constant strings (from left to right) in an AST node.
     */
    void theory_str::get_const_str_asts_in_node(expr * node, expr_ref_vector & astList) {
        if (u.str.is_string(node)) {
            astList.push_back(node);
            //} else if (getNodeType(t, node) == my_Z3_Func) {
        } else if (is_app(node)) {
            app * func_app = to_app(node);
            unsigned int argCount = func_app->get_num_args();
            for (unsigned int i = 0; i < argCount; i++) {
                expr * argAst = func_app->get_arg(i);
                get_const_str_asts_in_node(argAst, astList);
            }
        }
    }

    eautomaton* theory_str::get_automaton(expr* re) {
        eautomaton* result = nullptr;
        ast_manager & m = get_manager();
        if (m_re2aut.find(re, result)) {
            return result;
        }
        if (!m_mk_aut.has_solver()) {
            m_mk_aut.set_solver(alloc(seq_expr_solver, m, get_context().get_fparams()));
        }
        result = m_mk_aut(re);
        m_automata.push_back(result);
        m_re2aut.insert(re, result);
        m_res.push_back(re);
        return result;
    }

    /*
     * Collect constant strings (from left to right) in an AST node.
     */
    void theory_str::get_const_regex_str_asts_in_node(expr * node, expr_ref_vector & astList) {
        zstring value;
        if (u.str.is_string(node, value) && value.length() > 0) {
            astList.push_back(node);
        } else if (is_app(node)) {
            app * func_app = to_app(node);
            unsigned int argCount = func_app->get_num_args();
            for (unsigned int i = 0; i < argCount; i++) {
                expr * argAst = func_app->get_arg(i);
                get_const_regex_str_asts_in_node(argAst, astList);
            }
        }
        else {
            for (const auto& we: membership_memo) {
                if (node == we.first.get()) {
                    astList.push_back(node);
                    break;
                }
            }
        }
    }

    /*
     * Check if there are empty vars in an AST node.
     */
    bool theory_str::has_empty_vars(expr * node) {
        ptr_vector<expr> vars;
        get_nodes_in_concat(node, vars);
        rational vLen;
        for (int i = 0; i < vars.size(); ++i){
            if (get_len_value(vars[i], vLen))
                if (vLen.get_int64() == 0)
                    return true;
        }
        return false;
    }

    /*
     * Collect important vars in AST node
     */
    void theory_str::get_important_asts_in_node(expr * node, std::set<std::pair<expr*, int>> non_fresh_vars, expr_ref_vector & astList, bool consider_itself) {
        if (consider_itself)
            for (const auto& p : non_fresh_vars)
                if (p.first == node) {
                    STRACE("str", tout << __LINE__ <<  " \t found in the important list " << mk_ismt2_pp(node, get_manager()) << std::endl;);
                    astList.push_back(node);
                    break;
                }

        if (is_app(node)) {
            app * func_app = to_app(node);
            unsigned int argCount = func_app->get_num_args();
            for (unsigned int i = 0; i < argCount; i++) {
                expr * argAst = func_app->get_arg(i);
                get_important_asts_in_node(argAst, non_fresh_vars, astList, true);
            }
        }
    }

    void theory_str::track_variable_scope(expr * var) {
        if (internal_variable_scope_levels.find(m_scope_level) == internal_variable_scope_levels.end()) {
            internal_variable_scope_levels[m_scope_level] = obj_hashtable<expr>();
        }
        internal_variable_scope_levels[m_scope_level].insert(var);
    }

    expr * theory_str::rewrite_implication(expr * premise, expr * conclusion) {
        ast_manager & m = get_manager();
        return m.mk_or(mk_not(m, premise), conclusion);
    }

    void theory_str::assert_implication(expr * premise, expr * conclusion) {
        ast_manager & m = get_manager();
        expr_ref axiom(m.mk_or(mk_not(m, premise), conclusion), m);
        assert_axiom(axiom);
    }

    expr* theory_str::query_theory_arith_core(expr* n, model_generator& mg){
        context& ctx = get_context();
        family_id afid = m_autil.get_family_id();
        ptr_vector<expr> values;
        app* value = nullptr;
        do {
            theory_mi_arith* tha = get_th_arith<theory_mi_arith>(ctx, afid, n);
            if (tha) {
                model_value_proc* tmp = tha->mk_value(ctx.get_enode(n), mg);
                value = tmp->mk_value(mg, values);
                break;
            }
            theory_i_arith* thi = get_th_arith<theory_i_arith>(ctx, afid, n);
            if (thi) {
                model_value_proc* tmp = tha->mk_value(ctx.get_enode(n), mg);
                value = tmp->mk_value(mg, values);
                break;
            }
            theory_lra* thr = get_th_arith<theory_lra>(ctx, afid, n);
            if (thr) {
                model_value_proc* tmp = tha->mk_value(ctx.get_enode(n), mg);
                value = tmp->mk_value(mg, values);
                break;
            }
            break;
        }
        while (false);

        return value;
    }

    expr* theory_str::query_theory_array(expr* n, model_generator& mg){
        ast_manager& m = get_manager();
        context& ctx = get_context();
        family_id afid = m_arrayUtil.get_family_id();
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " family_id: " << afid  << " node: " << mk_pp(n, get_manager()) << std::endl;);
        ptr_vector<expr> dependency_values;
        app* value = nullptr;
        do {
            theory_array_base* arrBase = get_th_array<theory_array_base>(ctx, afid, n);
            if (arrBase) {
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << std::endl;);
                model_value_proc* tmp = arrBase->mk_value(ctx.get_enode(n), mg);
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << std::endl;);
                buffer<model_value_dependency> dependencies;
                tmp->get_dependencies(dependencies);
                for (model_value_dependency const& d : dependencies) {
                    if (d.is_fresh_value()) {
                        SASSERT(d.get_value()->get_value());
                        dependency_values.push_back(d.get_value()->get_value());
                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": " << mk_pp(d.get_value()->get_value(), m) << std::endl;);
                    }
                    else {
                        enode * child = d.get_enode();
                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": " << mk_pp(child->get_owner(), m) << std::endl;);
                        child = child->get_root();
                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": " << mk_pp(child->get_owner(), m) << std::endl;);
                        app * val = nullptr;
                        if (mg.get_root2value().find(child, val))
                            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": " << mk_pp(val, m) << std::endl;);
                        dependency_values.push_back(val);
                    }
                }
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << std::endl;);
                value = tmp->mk_value(mg, dependency_values);
                break;
            }

            theory_array* arrtheory = get_th_array<theory_array>(ctx, afid, n);
            if (arrtheory) {
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << std::endl;);
                model_value_proc* tmp = arrtheory->mk_value(ctx.get_enode(n), mg);

                buffer<model_value_dependency> dependencies;
                tmp->get_dependencies(dependencies);
                for (model_value_dependency const& d : dependencies) {
                    if (d.is_fresh_value()) {
                        SASSERT(d.get_value()->get_value());
                        dependency_values.push_back(d.get_value()->get_value());
                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": " << mk_pp(d.get_value()->get_value(), m) << std::endl;);
                    }
                    else {
                        enode * child = d.get_enode();
                        child = child->get_root();
                        app * val = nullptr;
                        mg.get_root2value().find(child, val);
                        dependency_values.push_back(val);
                    }
                }

                value = tmp->mk_value(mg, dependency_values);
                break;
            }

            theory_array_full* arrfull = get_th_array<theory_array_full>(ctx, afid, n);
            if (arrfull) {
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << std::endl;);
                model_value_proc* tmp = arrfull->mk_value(ctx.get_enode(n), mg);

                buffer<model_value_dependency> dependencies;
                tmp->get_dependencies(dependencies);
                for (model_value_dependency const& d : dependencies) {
                    if (d.is_fresh_value()) {
                        SASSERT(d.get_value()->get_value());
                        dependency_values.push_back(d.get_value()->get_value());
                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": " << mk_pp(d.get_value()->get_value(), m) << std::endl;);
                    }
                    else {
                        enode * child = d.get_enode();
                        child = child->get_root();
                        app * val = nullptr;
                        mg.get_root2value().find(child, val);
                        dependency_values.push_back(val);
                    }
                }

                value = tmp->mk_value(mg, dependency_values);
                break;
            }
            break;
        }
        while (false);
        return value;
    }


    void theory_str::init_model(model_generator& mg) {
        ast_manager& m = get_manager();
        context& ctx = get_context();
        STRACE("str", tout << "initializing model..." << std::endl;);
        std::map<expr*, rational> varLen;
        std::set<expr*> included_nodes;

        // prepare backwardDep
        for (const auto& n : uState.eq_combination) {
            if (!ctx.is_relevant(n.first))
                continue;

            std::set<expr*> dep = getDependency(n.first);
            expr_ref_vector tmp(m);
            collect_eq_nodes(n.first, tmp);
            expr* reg = nullptr;
            for (const auto& nn : dep) {
                if (!ctx.is_relevant(nn))
                    continue;
                if (u.str.is_string(nn) || is_important(nn) || isInternalRegexVar(nn, reg) || is_regex_concat(nn)) {
                    if (!are_equal_exprs(n.first, nn))
                        backwardDep[ctx.get_enode(n.first)->get_root()->get_owner()].insert(
                                ctx.get_enode(nn)->get_root()->get_owner());
                    included_nodes.insert(ctx.get_enode(nn)->get_root()->get_owner());
                }
            }
        }


        for (const auto& c : concat_astNode_map) {
            if (!ctx.is_relevant(c.get_value()) || !ctx.is_relevant(c.get_key1()) || !ctx.is_relevant(c.get_key2()))
                continue;
            rational len;
            if ((get_len_value(c.get_key2(), len) && len.get_int64() == 0) ||
                (get_len_value(c.get_key1(), len) && len.get_int64() == 0))
                continue;

            expr* key1_root = ctx.get_enode(c.get_key1())->get_root()->get_owner();
            expr* key2_root = ctx.get_enode(c.get_key2())->get_root()->get_owner();
            expr* c_root = ctx.get_enode(c.get_value())->get_root()->get_owner();
            expr* reg = nullptr;

            // arg1
            if (u.str.is_string(key2_root) || is_important(key2_root) || isInternalRegexVar(key2_root, reg) || is_regex_concat(key2_root)) {
                if (!are_equal_exprs(c_root, key2_root)) {
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(c.get_key2(), m) << " VS " << mk_pp(c.get_value(), m) << std::endl;);
                    backwardDep[c_root].insert(c.get_key2());
                    if (key2_root != c.get_value())
                        backwardDep[c_root].insert(key2_root);
                }
            }
            else if (included_nodes.find(key2_root) == included_nodes.end()) {
                if ((get_len_value(c.get_key1(), len) && len.get_int64() == 0) || are_equal_exprs(c.get_key2(), c.get_value()))
                    continue;
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(c.get_key2(), m) << " VS " << mk_pp(c.get_value(), m) << std::endl;);
                if (key2_root != c.get_value())
                    backwardDep[key2_root].insert(c.get_value());

                backwardDep[c.get_key2()].insert(c.get_value());
                if (c.get_key2() != key2_root)
                    linkers[key2_root] = c.get_key2();
            }

            // arg0
            if (u.str.is_string(key1_root) || is_important(key1_root) || isInternalRegexVar(key1_root, reg) || is_regex_concat(key1_root)) {
                if (!are_equal_exprs(c_root, key1_root)) {
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(c.get_key1(), m) << " VS " << mk_pp(c.get_value(), m) << std::endl;);
                    backwardDep[c_root].insert(c.get_key1());
                    if (key1_root != c.get_value())
                        backwardDep[c_root].insert(key1_root);
                }
            }
            else if (included_nodes.find(key1_root) == included_nodes.end()) {
                if ((get_len_value(c.get_key2(), len) && len.get_int64() == 0) || are_equal_exprs(c.get_key1(), c.get_value()))
                    continue;
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(c.get_key1(), m) << " VS " << mk_pp(c.get_value(), m) << std::endl;);
                backwardDep[key1_root].insert(c.get_value());
                backwardDep[c.get_key1()].insert(c.get_value());

                if (c.get_key1() != key1_root)
                    linkers[key1_root] = c.get_key1();
            }
        }

        for (const auto& e: backwardDep) {
            STRACE("str", tout << __LINE__ << " " << mk_pp(e.first, m) << std::endl;);
            for (const auto& ee : e.second)
                STRACE("str", tout << __LINE__ << " \t" << mk_pp(ee, m) << std::endl;);
        }

        defaultChar = setupDefaultChar(initIncludeCharSet(), initExcludeCharSet());
    }

    void theory_str::finalize_model(model_generator& mg) {
        STRACE("str", tout << "finalizing model..." << std::endl;);
        ast_manager& m = get_manager();
        std::map<expr*, rational> varLen;

        for (const auto& n : variable_set){
            rational vLen;
            if (get_len_value(n, vLen)) {
                STRACE("str", tout << __LINE__ << " " << mk_pp(n, m) << " len = " << vLen << std::endl;);
                varLen[n] = vLen;
            }
            else {
                expr_ref len(m);
                len = mk_strlen(n);
                expr* value = query_theory_arith_core(len, mg);
                if (value != nullptr) {
                    STRACE("str", tout << __LINE__ << " len value :  " << mk_pp(n, m) << ": " << mk_pp(value, m) << std::endl;);
                    if (get_arith_value(value, vLen))
                        varLen[n] = vLen;
                }
            }
            STRACE("str", tout << std::endl;);
        }

//        std::vector<std::pair<expr*, rational>> freeValueVars;
//        if (!fixedValue(freeValueVars, varLen)) {
//            assignValues(mg, freeValueVars, varLen, uState.non_fresh_vars);
//        }
    }

    void theory_str::assert_axiom(expr *const e) {
        if (e == nullptr || get_manager().is_true(e)) return;

        ast_manager& m = get_manager();
        context& ctx = get_context();
        expr_ref ex{e, m};

        if (!ctx.b_internalized(ex)) {
            ctx.internalize(ex, false);
        }
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << mk_pp(e, m) << std::endl;);
        literal lit(ctx.get_literal(ex));
        ctx.mark_as_relevant(lit);
        ctx.mk_th_axiom(get_id(), 1, &lit);
    }

    void theory_str::assert_axiom(expr *const e1, expr *const e2) {
        assert_implication(e2, e1);
        return;
        ast_manager& m = get_manager();
        context& ctx = get_context();
        expr_ref ex1{e1, m};
        expr_ref ex2{e2, m};

        if (!ctx.b_internalized(ex1)) {
            ctx.internalize(ex1, false);
        }

        if (!ctx.b_internalized(ex2)) {
            ctx.internalize(ex2, false);
        }

        literal lit1(ctx.get_literal(ex1));
        literal lit2(ctx.get_literal(ex2));
        ctx.mark_as_relevant(lit1);
        ctx.mark_as_relevant(lit2);
        ctx.mk_th_axiom(get_id(), lit1, lit2);
    }

    void theory_str::dump_assignments() {
        STRACE("str", \
                ast_manager& m = get_manager();
                context& ctx = get_context();

                for (int i = 0; i < mful_scope_levels.size(); ++i)
                    {

                        literal tmp = ctx.get_literal(mful_scope_levels[i].get());
                        int assignLvl = ctx.get_assign_level(tmp);

                        STRACE("str", tout << __LINE__ << " assigned expr " << mk_pp(mful_scope_levels[i].get(), m)
                                           << ", assignLevel = " << assignLvl << std::endl;);
                    }

                for (const auto& n : variable_set){

                    rational vLen;
                    expr_ref value(m);
                    if (ctx.get_value(ctx.get_enode(n), value)){
                        STRACE("str", tout << __LINE__ << " var " << mk_pp(n, m) << " value = " << mk_pp(value.get(), m) << std::endl;);
                    }
                    else if (get_len_value(n, vLen)) {
                        STRACE("str", tout << __LINE__ << " var " << mk_pp(n, m) << " len = " << vLen << std::endl;);
                    }
                    else {
                        if (lower_bound(n, vLen)){
                            STRACE("str", tout << __LINE__ << " var " << mk_pp(n, m) << " lower_bound = " << vLen << std::endl;);
                        }
                        if (upper_bound(n, vLen)){
                            STRACE("str", tout << __LINE__ << " var " << mk_pp(n, m) << " upper_bound = " << vLen << std::endl;);
                        }
                    }
                }

                for (const auto& we: non_membership_memo) {
                    STRACE("str", tout << "Non membership: " << we.first << " = " << we.second << std::endl;);
                }

                for (const auto& we: membership_memo) {
                    STRACE("str", tout << "Membership: " << we.first << " = " << we.second << std::endl;);
                }

                if (string_int_conversion_terms.size() > 0) {
                    rational bound;
                    if (lower_num_bound(get_bound_str_int_control_var(), bound)){
                        STRACE("str", tout << __LINE__ << " var " << mk_pp(get_bound_str_int_control_var(), m) << " lower_bound = " << bound << std::endl;);
                    }
                }
        );
    }

    void theory_str::dump_literals() {
        STRACE("str", \
                ast_manager& m = get_manager();
                context& ctx = get_context();

                expr_ref_vector tmpExprs(m);
                ctx.get_relevant_literals(tmpExprs);
                for (int i = 0; i < tmpExprs.size(); ++i) {
                    literal tmp = ctx.get_literal(tmpExprs[i].get());
                    int assignLvl = ctx.get_assign_level(tmp);
                    if (ctx.get_assignment(tmpExprs[i].get()) == l_true && !m.is_or(tmpExprs[i].get()) && !m.is_and(tmpExprs[i].get()) && !m.is_ite(tmpExprs[i].get())){
                        STRACE("str", tout << __LINE__ << " guessed literal " << mk_pp(tmpExprs[i].get(), m)
                                           << ", assignLevel = " << assignLvl << std::endl;);
                    }
                }
        );
    }

    void theory_str::fetch_guessed_core_exprs(
            std::map<expr*, std::set<expr*>> eq_combination,
            expr_ref_vector &guessedExprs,
            expr_ref_vector diseqExprs,
            rational bound){
        ast_manager& m = get_manager();
        // collect vars
        std::set<expr*> allvars = collect_all_vars_in_eq_combination(eq_combination);
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << allvars.size() << std::endl;);
        expr_ref_vector orgExprs(m);
        orgExprs.append(guessedExprs);

        expr_ref_vector ret(m);
        expr_ref_vector tmpGuessedExprs(m);
        while (true) {
            // collect all eq
            for (const auto &e : guessedExprs) {
                if (to_app(e)->get_num_args() != 2) {
                    continue;
                }

                bool adding = false;
                expr *lhs = to_app(e)->get_arg(0);
                expr *rhs = to_app(e)->get_arg(1);

                // check rhs
                if (!adding && u.str.is_concat(rhs)) {
                    ptr_vector<expr> argVec;
                    get_nodes_in_concat(rhs, argVec);
                    if (check_intersection_not_empty(argVec, allvars)) {
                        // add lhs
                        ret.push_back(e);
                        adding = true;
                        update_all_vars(allvars, lhs);
                        update_all_vars(allvars, rhs);
                    }
                }

                // check lhs
                if (!adding && u.str.is_concat(lhs)) {
                    ptr_vector<expr> argVec;
                    get_nodes_in_concat(lhs, argVec);
                    if (check_intersection_not_empty(argVec, allvars)) {
                        // add rhs
                        ret.push_back(e);
                        adding = true;
                        update_all_vars(allvars, rhs);
                        update_all_vars(allvars, lhs);
                    }
                }

                if (!adding){
                    if (!u.str.is_concat(lhs) && !u.str.is_concat(rhs)) {
                        if (!u.str.is_string(lhs) && allvars.find(lhs) != allvars.end()){
                            ret.push_back(e);
                            adding = true;
                            allvars.insert(rhs);
                        }
                        else if (!u.str.is_string(rhs) && allvars.find(rhs) != allvars.end()){
                            ret.push_back(e);
                            adding = true;
                            allvars.insert(lhs);
                        }
                    }
                }


                if (adding == false)
                    tmpGuessedExprs.push_back(e);
            }

            // check if no improvement
            if (tmpGuessedExprs.size() == guessedExprs.size())
                break;

            guessedExprs.reset();
            guessedExprs.append(tmpGuessedExprs);
            tmpGuessedExprs.reset();
            tmpGuessedExprs.append(tmpGuessedExprs);
        }

        rational len;
        for (const auto& v : allvars) {
            if (get_len_value(v, len) && len.get_int64() == 0) {
                ret.push_back(createEqualOperator(v, mk_string("")));
            }
            else if (u.str.is_string(v)) {
                // const = concat
                expr_ref_vector eqs(m);
                collect_eq_nodes(v, eqs);
                for (const auto& eq : eqs)
                    if (u.str.is_concat(eq)) {
                        ret.push_back(createEqualOperator(v, eq));
                    }
            }
        }

        for (const auto& e : diseqExprs){
            if (to_app(e)->get_num_args() == 1) {
                expr *eq = to_app(e)->get_arg(0);
                if (to_app(eq)->get_num_args() == 2) {
                    expr *lhs = to_app(eq)->get_arg(0);
                    expr *rhs = to_app(eq)->get_arg(1);
                    expr* key;
                    if (is_contain_equality(lhs, key)) {
                        zstring keyStr;
                        if (u.str.is_string(key, keyStr)){
                            if (!is_trivial_contain(keyStr))
                                ret.push_back(e);
                        }
                    }
                    else if (is_contain_equality(rhs, key)){
                        zstring keyStr;
                        if (u.str.is_string(key, keyStr)){
                            if (!is_trivial_contain(keyStr))
                                ret.push_back(e);
                        }
                    }
                }
            }
        }

        if (get_bound_str_int_control_var() != nullptr) {
            if (bound == rational(0))
                ret.push_back(createEqualOperator(get_bound_str_int_control_var(), mk_int(str_int_bound)));
            else
                ret.push_back(createEqualOperator(get_bound_str_int_control_var(), mk_int(bound)));
        }

        guessedExprs.reset();
        guessedExprs.append(ret);
//        for (int i = 0; i < guessedExprs.size(); ++i)
//            STRACE("str", tout << __LINE__ << " core guessed exprs " << mk_pp(guessedExprs[i].get(), m) << std::endl;);
    }

    void theory_str::fetch_related_exprs(
            expr_ref_vector allvars,
            expr_ref_vector &guessedExprs){
        ast_manager& m = get_manager();

        expr_ref_vector ret(m);
        rational lenValue;
        for (const auto &e : guessedExprs) {
            expr *lhs = to_app(e)->get_arg(0);
            expr *rhs = to_app(e)->get_arg(1);

            // skip empty values
            if (get_len_value(lhs, lenValue) && lenValue.get_int64() == 0)
                continue;

            if (get_len_value(rhs, lenValue) && lenValue.get_int64() == 0)
                continue;

            // check rhs
            ptr_vector<expr> argVec;
            get_nodes_in_concat(rhs, argVec);
            if (check_intersection_not_empty(argVec, allvars)) {
                argVec.reset();
                get_nodes_in_concat(lhs, argVec);
                if (check_intersection_not_empty(argVec, allvars)) {
                    // add rhs
                    ret.push_back(e);
                }
            }
        }

        // capture empty values
        for (const auto& v : allvars)
            if (get_len_value(v, lenValue) && lenValue.get_int64() == 0)
                ret.push_back(createEqualOperator(v, mk_string("")));

        guessedExprs.reset();
        guessedExprs.append(ret);
        for (int i = 0; i < guessedExprs.size(); ++i)
            STRACE("str", tout << __LINE__ << " core guessed exprs " << mk_pp(guessedExprs[i].get(), m) << std::endl;);
    }

    /*
     * v does not contain replacekey
     */
    expr_ref_vector theory_str::check_contain_related_vars(
            expr* v,
            zstring containKey){
        ast_manager& m = get_manager();
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << std::endl;);

        expr_ref_vector ret(m);
        zstring value;
        rational lenValue;
        ptr_vector<expr> childrenVector;
        get_all_nodes_in_concat(v, childrenVector);

        for (int i = 0; i < childrenVector.size(); ++i) {
            ret.push_back(childrenVector[i]);
            if (u.str.is_string(childrenVector[i], value))
                if (value.contains(containKey))
                    return ret;
        }

        int pos = 0;
        while (pos < ret.size()){
            expr* tmp = ret[pos].get();
            pos++;

            if (get_len_value(tmp, lenValue) && lenValue.get_int64() == 0)
                continue;

            if (u.str.is_replace(tmp)){
                expr* arg0 = to_app(tmp)->get_arg(0);
                expr* arg1 = to_app(tmp)->get_arg(1);
                zstring val;
                if (u.str.is_string(arg1, val)) {
                    if (!val.contains(containKey)) {  // x = replace y val ? && val does not contain key --> y does not contain key
                        ptr_vector<expr> childrenVector;
                        get_all_nodes_in_concat(arg0, childrenVector);
                        for (int j = 0; j < childrenVector.size(); ++j)
                            if (!ret.contains(childrenVector[j])) {
                                ret.push_back(childrenVector[j]);
                                if (u.str.is_string(childrenVector[j], value))
                                    if (value.contains(containKey))
                                        return ret;
                            }
                    }
                }
            }

            expr_ref_vector tmpVector(m);
            collect_eq_nodes(tmp, tmpVector); // var in class of tmp also does not contain containkey
            for (int i = 0; i  < tmpVector.size(); ++i)
                if (!ret.contains(tmpVector[i].get())){
                    STRACE("str", tout << __LINE__ << " " << mk_pp(tmp, m) << " == " << mk_pp(tmpVector[i].get(), m) << std::endl;);
                    ptr_vector<expr> childrenVector;
                    get_all_nodes_in_concat(tmpVector[i].get(), childrenVector);
                    for (int j = 0; j < childrenVector.size(); ++j)
                        if (!ret.contains(childrenVector[j])) {
                            ret.push_back(childrenVector[j]);
                            if (u.str.is_string(childrenVector[j], value))
                                if (value.contains(containKey))
                                    return ret;
                        }
                }
        }

        ret.reset();
        return ret;
    }

    std::set<expr*> theory_str::collect_all_vars_in_eq_combination(std::map<expr*, std::set<expr*>> eq_combination){
        std::set<expr*> allvars;
        for (const auto& eq : eq_combination){
            // collect vars or not
            // not collect if it is not important, and none of variable is really important

            for (const auto& e : eq.second) {
                ptr_vector<expr> argVec;
                get_nodes_in_concat(e, argVec);
                for (int i = 0; i < argVec.size(); ++i) {
                    zstring value;
                    if (u.str.is_string(argVec[i], value) && value.length() == 0)
                        continue;
                    allvars.insert(argVec[i]);
                }
            }
        }
        return allvars;
    }

    void theory_str::update_all_vars(std::set<expr*> &allvars, expr* e){
        if (u.str.is_concat(e)) {
            ptr_vector<expr> argVec;
            get_nodes_in_concat(e, argVec);
            for (int j = 0; j < argVec.size(); ++j)
                allvars.insert(argVec[j]);
        }
        else {
            allvars.insert(e);
        }
    }

    bool theory_str::check_intersection_not_empty(ptr_vector<expr> v, std::set<expr*> allvars){
        for (int i = 0; i < v.size(); ++i)
            if (!u.str.is_string(v[i]))
                if (allvars.find(v[i]) != allvars.end())
                    return true;
        return false;
    }

    bool theory_str::check_intersection_not_empty(ptr_vector<expr> v, expr_ref_vector allvars){
        for (int i = 0; i < v.size(); ++i)
            if (allvars.contains(v[i]))
                return true;
        return false;
    }

    void theory_str::fetch_guessed_exprs_from_cache(UnderApproxState state, expr_ref_vector &guessedExprs) {
        guessedExprs.append(state.equalities);
        fetch_guessed_core_exprs(state.eq_combination, guessedExprs, state.disequalities, state.str_int_bound);
    }

    void theory_str::fetch_guessed_exprs_with_scopes(expr_ref_vector &guessedEqs) {
        ast_manager& m = get_manager();
        context& ctx = get_context();
        for (int i = 0; i < mful_scope_levels.size(); ++i) {
            literal tmp = ctx.get_literal(mful_scope_levels[i].get());
            int assignLvl = ctx.get_assign_level(tmp);
            if (assignLvl >= 0)
                if (!m.is_not(mful_scope_levels[i].get()))
                    guessedEqs.push_back(mful_scope_levels[i].get());
        }
    }

    void theory_str::fetch_guessed_exprs_with_scopes(expr_ref_vector &guessedEqs, expr_ref_vector &guessedDisEqs) {
        ast_manager& m = get_manager();
        context& ctx = get_context();
        for (int i = 0; i < mful_scope_levels.size(); ++i) {
            literal tmp = ctx.get_literal(mful_scope_levels[i].get());
            int assignLvl = ctx.get_assign_level(tmp);
            if (assignLvl >= 0) {
                if (!m.is_not(mful_scope_levels[i].get()))
                    guessedEqs.push_back(mful_scope_levels[i].get());
                else
                    guessedDisEqs.push_back(mful_scope_levels[i].get());
            }
        }
    }

    void theory_str::fetch_guessed_literals_with_scopes(literal_vector &guessedLiterals) {
        ast_manager& m = get_manager();
        context& ctx = get_context();

        for (int i = 0; i < mful_scope_levels.size(); ++i)
            if (!m.is_not(mful_scope_levels[i].get()))
            {
                literal tmp = ctx.get_literal(mful_scope_levels[i].get());

                STRACE("str", tout << __LINE__ << " guessedLiterals " << mk_pp(mful_scope_levels[i].get(), m) << std::endl;);

                guessedLiterals.push_back(tmp);
            }
    }

    void theory_str::fetch_guessed_str_int_with_scopes(expr_ref_vector &guessedEqs, expr_ref_vector &guessedDisEqs) {
        ast_manager& m = get_manager();
        context& ctx = get_context();

        expr_ref_vector assignments(m);
        ctx.get_assignments(assignments);
        expr_ref_vector stored_eq(m);
        expr_ref_vector stored_diseq(m);
        for (const auto& s : assignments) {
            if (ctx.is_relevant(s)) {
                if (!m.is_not(s)) {
                    app* a = to_app(s);
                    if (a->get_num_args() == 2 && m.is_eq(a) &&
                            ((u.str.is_stoi(a->get_arg(0)) || u.str.is_stoi(a->get_arg(1))) ||
                                    (u.str.is_itos(a->get_arg(0)) || u.str.is_itos(a->get_arg(1))))) {
                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(s, m) << std::endl;);
                        if ((u.str.is_stoi(a->get_arg(0)) || u.str.is_itos(a->get_arg(0))) &&
                                !stored_eq.contains(a->get_arg(0))) {
                            guessedEqs.push_back(s);
                            stored_eq.push_back(a->get_arg(0));
                        }
                        else if ((u.str.is_stoi(a->get_arg(1)) || u.str.is_itos(a->get_arg(1))) &&
                                 !stored_eq.contains(a->get_arg(1))) {
                            guessedEqs.push_back(s);
                            stored_eq.push_back(a->get_arg(1));
                        }
                    }
                }
                else if (to_app(s)->get_num_args() == 1){
                    app* a = to_app(to_app(s)->get_arg(0));
                    if (a->get_num_args() == 2 && m.is_eq(a) &&
                        ((u.str.is_stoi(a->get_arg(0)) || u.str.is_stoi(a->get_arg(1))) ||
                                (u.str.is_itos(a->get_arg(0)) || u.str.is_itos(a->get_arg(1))))) {
                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(s, m) << std::endl;);
                        if ((u.str.is_stoi(a->get_arg(0)) || u.str.is_itos(a->get_arg(0))) &&
                            !stored_diseq.contains(a->get_arg(0))) {
                            guessedDisEqs.push_back(s);
                            stored_diseq.push_back(a->get_arg(0));
                        }
                        else if ((u.str.is_stoi(a->get_arg(1)) || u.str.is_itos(a->get_arg(1))) &&
                                 !stored_diseq.contains(a->get_arg(1))) {
                            guessedDisEqs.push_back(s);
                            stored_diseq.push_back(a->get_arg(1));
                        }
                    }
                }
            }
        }
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " leave " << std::endl;);
    }


    void theory_str::dump_bool_vars() {
        STRACE("str", \
                ast_manager& m = get_manager();
                context& ctx = get_context();
                int numBV = ctx.get_num_bool_vars();
                for (bool_var v = 0; v < numBV; v++)
                    if (ctx.has_enode(v) && ctx.get_assign_level(v) > 0){
                        lbool value = ctx.get_assignment(v);
                        expr* node = ctx.bool_var2expr(v);
                        switch (value) {
                            case l_undef:
                                STRACE("str", tout << __LINE__ << " var " << mk_pp(node, m) << " bvalue = l_undef, assignLevel = " << ctx.get_assign_level(v) << " marked: " << ctx.is_marked(v) << "assumption:"  << ctx.is_assumption(v) << std::endl;);
                                break;
                            case l_true:
                                STRACE("str", tout << __LINE__ << " var " << mk_pp(node, m) << " bvalue = true, assignLevel = " << ctx.get_assign_level(v) << " marked: " << ctx.is_marked(v) << "assumption:"  << ctx.is_assumption(v) << std::endl;);
                                break;
                            case l_false:
                                STRACE("str", tout << __LINE__ << " var " << mk_pp(node, m) << " bvalue = false, assignLevel = " << ctx.get_assign_level(v) << " marked: " << ctx.is_marked(v) << "assumption:"  << ctx.is_assumption(v) << std::endl;);
                                break;
                            default:
                                break;
                        }
                    }
        );
    }

    const bool theory_str::is_theory_str_term(expr *const e) const {
        ast_manager& m = get_manager();
        return (m.get_sort(e) == m.mk_sort(m.mk_family_id("seq"), _STRING_SORT, 0, nullptr));
    }

    decl_kind theory_str::get_decl_kind(expr *const e) const {
        return to_app(e)->get_decl_kind();
    }

    str::word_term theory_str::get_word_term(expr *const e) const {
        if (get_decl_kind(e) == OP_STRING_CONST) {
            std::stringstream ss;
            ss << mk_ismt2_pp(e, get_manager());
            return str::word_term::of_string(ss.str());
        }
        if (get_decl_kind(e) == OP_SEQ_CONCAT) {
            str::word_term result;
            const unsigned num_args = to_app(e)->get_num_args();
            for (unsigned i = 0; i < num_args; i++) {
                const str::word_term& sub_term = get_word_term(to_app(e)->get_arg(i));
                result.concat(sub_term);
            }
            return result;
        }
        std::stringstream ss;
        ss << mk_ismt2_pp(e, get_manager());
        return str::word_term::of_variable(ss.str());
    }

    str::state theory_str::build_state_from_memo() const {
        str::state result;
        STRACE("str", tout << "[Build State]\nword equation memo:\n";);
        STRACE("str", if (m_we_expr_memo.empty()) tout << "--\n";);
        for (const auto& we : m_we_expr_memo) {
            STRACE("str", tout << we.first << " = " << we.second << std::endl;);
            const str::word_term& lhs = get_word_term(we.first);
            const str::word_term& rhs = get_word_term(we.second);
            result.satisfy_constraint(str::word_equation{rhs, lhs});
        }
        STRACE("str", tout << "word disequality memo:\n";);
        STRACE("str", if (m_wi_expr_memo.empty()) tout << "--\n";);
        for (const auto &wi : m_wi_expr_memo) {
            if (!u.str.is_empty(wi.second.get()) && !u.str.is_empty(wi.first.get())) {
                STRACE("str", tout << "not (" << wi.first << " = " << wi.second << ")\n";);
                const str::word_term &lhs = get_word_term(wi.first);
                const str::word_term &rhs = get_word_term(wi.second);
                result.fail_constraint(str::word_equation{rhs, lhs});
            }
        }
        STRACE("str", tout << std::endl;);
        return result;
    }

    const bool theory_str::block_dpllt_assignment_from_memo() {
        ast_manager& m = get_manager();
        expr *refinement_expr = nullptr;
        STRACE("str", tout << "[Assert Blocking]\nformulas:\n";);
        for (const auto& we : m_we_expr_memo) {
            expr *const e = m.mk_not(mk_eq_atom(we.first, we.second));
            refinement_expr = refinement_expr == nullptr ? e : m.mk_or(refinement_expr, e);
            STRACE("str", tout << we.first << " = " << we.second << '\n';);
        }
        for (const auto& wi : m_wi_expr_memo) {
            expr *const e = mk_eq_atom(wi.first, wi.second);
            refinement_expr = refinement_expr == nullptr ? e : m.mk_or(refinement_expr, e);
            STRACE("str", tout << "not (" << wi.first << " = " << wi.second << ")\n";);
        }
        if (refinement_expr != nullptr) {
            assert_axiom(refinement_expr);
            STRACE("str", tout << "assertion:\n" << mk_pp(refinement_expr, m) << "\n\n"
                               << std::flush;);
            return true;
        }
        return false;
    }

}
