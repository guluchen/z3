#include <algorithm>
#include <functional>
#include "ast/ast_pp.h"
#include "smt/theory_str.h"
#include "smt/smt_context.h"
#include "smt/smt_model_generator.h"

/* TODO:
 *  1. better algorithm for checking solved form
 *  2. on-the-fly over-approximation
 *  3. better algorithm for computing state transform
 */

namespace smt {

    namespace str {

        using namespace std::placeholders;

        const element& element::null() {
            static const element e{element::t::NONE, ""};
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

        word_term word_term::from_string(const zstring& str) {
            word_term result;
            for (std::size_t i = 0; i < str.length(); i++) {
                result.m_elements.push_back({element::t::CONST, {str[i]}});
            }
            return result;
        }

        word_term word_term::from_variable(const zstring& name) {
            return {{element::t::VAR, name}};
        }

        const bool
        word_term::prefix_const_mismatched(const word_term& w1, const word_term& w2) {
            if (w1.empty() || w2.empty()) return false;

            auto it1 = w1.m_elements.begin();
            auto it2 = w2.m_elements.begin();
            while (*it1 == *it2) {
                if (++it1 == w1.m_elements.end() || ++it2 == w2.m_elements.end()) return false;
            }
            return it1->typed(element::t::CONST) && it2->typed(element::t::CONST) &&
                   it1->value() != it2->value();
        }

        const bool
        word_term::suffix_const_mismatched(const word_term& w1, const word_term& w2) {
            if (w1.empty() || w2.empty()) return false;

            auto it1 = w1.m_elements.end();
            auto it2 = w2.m_elements.end();
            while (*it1 == *it2) {
                if (--it1 == w1.m_elements.begin() || --it2 == w2.m_elements.begin()) return false;
            }
            return it1->typed(element::t::CONST) && it2->typed(element::t::CONST) &&
                   it1->value() != it2->value();
        }

        const bool word_term::unequalable_no_empty_var(const word_term& w1, const word_term& w2) {
            return (!w1.has_variable() && w1.length() < w2.length()) ||
                   (!w2.has_variable() && w2.length() < w1.length()) ||
                   prefix_const_mismatched(w1, w2) || suffix_const_mismatched(w1, w2);
        }

        const bool word_term::unequalable(const word_term& w1, const word_term& w2) {
            return (!w1.has_variable() && w1.constant_count() < w2.constant_count()) ||
                   (!w2.has_variable() && w2.constant_count() < w1.constant_count()) ||
                   prefix_const_mismatched(w1, w2) || suffix_const_mismatched(w1, w2);
        }

        word_term::word_term(std::initializer_list<element> list) {
            m_elements.insert(m_elements.begin(), list.begin(), list.end());
        }

        const std::size_t word_term::constant_count() const {
            static const auto& is_const = std::bind(&element::typed, _1, element::t::CONST);
            return (std::size_t) std::count_if(m_elements.begin(), m_elements.end(), is_const);
        }

        const std::set<element> word_term::variables() const {
            std::set<element> result;
            for (const auto& e : m_elements) {
                if (e.typed(element::t::VAR)) {
                    result.insert(e);
                }
            }
            return result;
        }

        const bool word_term::has_constant() const {
            static const auto& is_const = std::bind(&element::typed, _1, element::t::CONST);
            return std::any_of(m_elements.begin(), m_elements.end(), is_const);
        }

        const bool word_term::has_variable() const {
            static const auto& is_var = std::bind(&element::typed, _1, element::t::VAR);
            return std::any_of(m_elements.begin(), m_elements.end(), is_var);
        }

        const bool word_term::check_head(const element::t& t) const {
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
            if (head.typed(element::t::CONST)) {
                in_consts = true;
                os << '"' << head;
            } else os << head;
            for (auto it = ++(w.m_elements.begin()); it != w.m_elements.end(); it++) {
                if (it->typed(element::t::CONST)) {
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
            if (m_lhs.length() == 1 && m_lhs.check_head(element::t::VAR)) {
                return m_lhs.head();
            }
            if (m_rhs.length() == 1 && m_rhs.check_head(element::t::VAR)) {
                return m_rhs.head();
            }
            return element::null();
        }

        const word_term& word_equation::definition_body() const {
            if (m_lhs.length() == 1 && m_lhs.check_head(element::t::VAR)) {
                return m_rhs;
            }
            if (m_rhs.length() == 1 && m_rhs.check_head(element::t::VAR)) {
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

        const bool word_equation::check_heads(const element::t& lht, const element::t& rht) const {
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

            const bool var_const_headed = hh.first.typed(element::t::VAR);
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
            if (m_src.check_heads(element::t::VAR, element::t::VAR)) {
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

        const word_equation& state::only_one_eq_left() const {
            return m_wes_to_satisfy.size() == 1 ? *m_wes_to_satisfy.begin()
                                                : word_equation::null();
        }

        const std::vector<std::vector<word_term>> state::eq_classes() const {
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

        const bool state::eq_classes_inconsistent() const {
            const auto& unequalable = m_allow_empty_var ? word_term::unequalable
                                                        : word_term::unequalable_no_empty_var;
            for (const auto& cls : eq_classes()) {
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

        const bool state::diseq_inconsistent() const {
            return !m_wes_to_fail.empty() && m_wes_to_fail.begin()->empty();
        }

        const bool state::unsolvable_by_check() const {
            const auto& unsolvable = std::bind(&word_equation::unsolvable, _1, m_allow_empty_var);
            return std::any_of(m_wes_to_satisfy.begin(), m_wes_to_satisfy.end(), unsolvable) ||
                   diseq_inconsistent();
        }

        const bool state::unsolvable_by_inference() const {
            return diseq_inconsistent() || eq_classes_inconsistent();
        }

        const bool state::in_definition_form() const {
            static const auto& in_def_form = std::mem_fn(&word_equation::in_definition_form);
            return std::all_of(m_wes_to_satisfy.begin(), m_wes_to_satisfy.end(), in_def_form);
        }

        const bool state::in_solved_form() const {
            return (in_definition_form() && definition_acyclic()) || m_wes_to_satisfy.empty();
        }

        void state::should_satisfy(const word_equation& we) {
            SASSERT(we);

            if (we.empty()) return;
            const word_equation& trimmed = we.trim_prefix();
            if (trimmed.empty()) return;
            m_wes_to_satisfy.insert(trimmed);
        }

        void state::should_fail(const word_equation& we) {
            SASSERT(we);

            const word_equation& trimmed = we.trim_prefix();
            if (trimmed.unsolvable(m_allow_empty_var)) return;
            m_wes_to_fail.insert(trimmed);
        }

        state state::replace(const element& tgt, const word_term& subst) const {
            state result{m_allow_empty_var};
            for (const auto& we : m_wes_to_satisfy) {
                result.should_satisfy(we.replace(tgt, subst));
            }
            for (const auto& we : m_wes_to_fail) {
                result.should_fail(we.replace(tgt, subst));
            }
            return result;
        }

        state state::remove(const element& tgt) const {
            return replace(tgt, {});
        }

        state state::remove_all(const std::set<element>& tgt) const {
            state result{m_allow_empty_var};
            for (const auto& we : m_wes_to_satisfy) {
                result.should_satisfy(we.remove_all(tgt));
            }
            for (const auto& we : m_wes_to_fail) {
                result.should_fail(we.remove_all(tgt));
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

            if (curr_we.check_heads(element::t::VAR, element::t::VAR)) {
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
            if (m_wes_to_fail.empty()) {
                return {*m_wes_to_satisfy.begin(), null};
            }
            SASSERT(!m_wes_to_fail.begin()->empty());
            const word_equation& we = *m_wes_to_satisfy.begin();
            const word_equation& wi = *m_wes_to_fail.begin();
            return we < wi ? trans_source{we, null} : trans_source{null, wi};
        }

        void state::transform_one_var(const head_pair& hh, std::list<state>& result) const {
            SASSERT(hh.first);
            SASSERT(hh.second);

            const bool var_const_headed = hh.first.typed(element::t::VAR);
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
                c.allow_empty_var(false);
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
                STRACE("str", tout << "from:\n" << curr_s << std::endl;);
                for (const auto& next_s : curr_s.transform()) {
                    if (m_processed.find(next_s) != m_processed.end()) {
                        STRACE("str", tout << "already visited:\n" << next_s << std::endl;);
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
                    const word_equation& last_we = next_s.only_one_eq_left();
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
            : theory{m.mk_family_id("seq")}, m_params{params}, m_util_a{m}, m_util_s{m} {
    }

    void theory_str::display(std::ostream& os) const {
        os << "theory_str display" << std::endl;
    }

    void theory_str::init(context *ctx) {
        theory::init(ctx);
    }

    void theory_str::add_theory_assumptions(expr_ref_vector& assumptions) {
        STRACE("str", tout << "add theory assumption for theory_str" << std::endl;);
    }

    theory_var theory_str::mk_var(enode *const n) {
        STRACE("str", tout << "mk_var for " << mk_pp(n->get_owner(), get_manager()) << std::endl;);
        if (!is_theory_str_term(n->get_owner())) {
            return null_theory_var;
        }
        if (is_attached_to_var(n)) {
            const theory_var& v = n->get_th_var(get_id());
            STRACE("str", tout << "already attached to theory var #" << v << std::endl;);
            return v;
        } else {
            context& ctx = get_context();
            const theory_var& v = theory::mk_var(n);
            ctx.attach_th_var(n, this, v);
            ctx.mark_as_relevant(n);
            STRACE("str", tout << "new theory var #" << v << ": " << get_enode(v) << std::endl;);
            return v;
        }
    }

    bool theory_str::internalize_atom(app *const atom, const bool gate_ctx) {
        (void) gate_ctx;
        return internalize_term(atom);
    }

    bool theory_str::internalize_term(app *const term) {
        ast_manager& m = get_manager();
        context& ctx = get_context();
        SASSERT(term->get_family_id() == get_family_id());
        STRACE("str", tout << "internalize term: " << mk_pp(term, m) << std::endl;);

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
            STRACE("str", tout << "arg has theory var #" << v_arg << std::endl;);
        }

        const theory_var& v = mk_var(e);
        (void) v;
        STRACE("str", tout << "term has theory var #" << v << std::endl;);
        return true;
    }

    void theory_str::init_search_eh() {
        STRACE("str", tout << "init search" << std::endl;);
    }

    void theory_str::relevant_eh(app *const n) {
        (void) n;
        STRACE("str", tout << "relevant: " << mk_pp(n, get_manager()) << std::endl;);
    }

    void theory_str::assign_eh(bool_var v, const bool is_true) {
        // YFC: membership constraint goes here
        (void) v;
        (void) is_true;
        STRACE("str", tout << "assign: v" << v << " #" << get_context().bool_var2expr(v)->get_id()
                           << " is_true: " << is_true << std::endl;);
    }

    void theory_str::new_eq_eh(theory_var x, theory_var y) {
        ast_manager& m = get_manager();
        const expr_ref l{get_enode(x)->get_owner(), m};
        const expr_ref r{get_enode(y)->get_owner(), m};
        m_word_eq_todo.push_back({l, r});
        STRACE("str", tout << "new eq: " << mk_pp(l, m) << " = " << mk_pp(r, m) << std::endl;);
    }

    void theory_str::new_diseq_eh(theory_var x, theory_var y) {
        ast_manager& m = get_manager();
        const expr_ref l{get_enode(x)->get_owner(), m};
        const expr_ref r{get_enode(y)->get_owner(), m};
        m_word_diseq_todo.push_back({l, r});
        STRACE("str", tout << "new diseq: " << mk_pp(l, m) << " != " << mk_pp(r, m) << std::endl;);
    }

    bool theory_str::can_propagate() {
        return false;
    }

    void theory_str::propagate() {
        STRACE("str", tout << "propagate" << std::endl;);
    }

    void theory_str::push_scope_eh() {
        m_scope_level += 1;
        m_word_eq_todo.push_scope();
        m_word_diseq_todo.push_scope();
        STRACE("str", tout << "push to " << m_scope_level << std::endl;);
    }

    void theory_str::pop_scope_eh(const unsigned num_scopes) {
        m_scope_level -= num_scopes;
        m_word_eq_todo.pop_scope(num_scopes);
        m_word_diseq_todo.pop_scope(num_scopes);
        STRACE("str", tout << "pop " << num_scopes << " to " << m_scope_level << std::endl;);
    }

    void theory_str::reset_eh() {
        STRACE("str", tout << "reset" << std::endl;);
    }

    final_check_status theory_str::final_check_eh() {
        if (m_word_eq_todo.empty()) return FC_DONE;
        TRACE("str", tout << "final_check level " << get_context().get_scope_level() << std::endl;);

        const str::state& root = mk_state_from_todo();
        STRACE("str", tout << "root built:\n" << root << std::endl;);
        str::neilson_based_solver solver{root};
        if (root.unsolvable_by_inference() && block_curr_assignment()) {
            return FC_CONTINUE;
        }
        solver.check_sat();
        if (solver.solution_found()) {
            STRACE("str", tout << "[Solved]\n";);
            return FC_DONE;
        } else if (block_curr_assignment()) {
            return FC_CONTINUE;
        } else {
            STRACE("str", dump_assignments(););
            return FC_DONE;
        }
    }

    model_value_proc *theory_str::mk_value(enode *const n, model_generator& mg) {
        ast_manager& m = get_manager();
        app *const tgt = n->get_owner();
        (void) m;
        // if the owner is not internalized, it doesn't have an e-node associated.
        SASSERT(get_context().e_internalized(tgt));
        STRACE("str", tout << "mk_value for: " << mk_pp(tgt, m) << " (sort "
                           << mk_pp(m.get_sort(tgt), m) << ")" << std::endl;);
        return alloc(expr_wrapper_proc, tgt);
    }

    void theory_str::init_model(model_generator& mg) {
        STRACE("str", tout << "init model" << std::endl;);
    }

    void theory_str::finalize_model(model_generator& mg) {
        STRACE("str", tout << "finalize model" << std::endl;);
    }

    lbool theory_str::validate_unsat_core(expr_ref_vector& unsat_core) {
        return l_undef;
    }

    void theory_str::assert_axiom(expr *const e) {
        if (e == nullptr || get_manager().is_true(e)) return;

        context& ctx = get_context();
        if (!ctx.b_internalized(e)) {
            ctx.internalize(e, false);
        }
        literal lit{ctx.get_literal(e)};
        ctx.mark_as_relevant(lit);
        ctx.mk_th_axiom(get_id(), 1, &lit);
    }

    void theory_str::dump_assignments() {
        STRACE("str", \
                ast_manager& m = get_manager();
                context& ctx = get_context();
                tout << "dump all assignments:\n";
                expr_ref_vector assignments{m};
                ctx.get_assignments(assignments);
                for (expr *const e : assignments) {
                    tout << mk_pp(e, m) << (ctx.is_relevant(e) ? "\n" : " (NOT REL)\n");
                }
                tout << std::flush;
        );
    }

    const bool theory_str::is_theory_str_term(expr *const e) const {
        return m_util_s.str.is_string_term(e);
    }

    str::word_term theory_str::mk_word_term(expr *const e) const {
        zstring s;
        if (m_util_s.str.is_string(e, s)) {
            return str::word_term::from_string(s);
        }
        if (m_util_s.str.is_concat(e)) {
            str::word_term result;
            for (unsigned i = 0; i < to_app(e)->get_num_args(); i++) {
                result.concat(mk_word_term(to_app(e)->get_arg(i)));
            }
            return result;
        }
        func_decl *const fun = to_app(e)->get_decl();
        SASSERT(fun->get_arity() == 0 && fun->get_range()->get_family_id() == get_family_id());
        return str::word_term::from_variable({fun->get_name().bare_str()});
    }

    str::state theory_str::mk_state_from_todo() const {
        str::state result;
        STRACE("str", tout << "[Build State]\nword equation todo:\n";);
        STRACE("str", if (m_word_eq_todo.empty()) tout << "--\n";);
        for (const auto& eq : m_word_eq_todo) {
            STRACE("str", tout << eq.first << " = " << eq.second << std::endl;);
            result.should_satisfy({mk_word_term(eq.first), mk_word_term(eq.second)});
        }
        STRACE("str", tout << "word disequality todo:\n";);
        STRACE("str", if (m_word_diseq_todo.empty()) tout << "--\n";);
        for (const auto& diseq : m_word_diseq_todo) {
            STRACE("str", tout << diseq.first << " != " << diseq.second << '\n';);
            result.should_fail({mk_word_term(diseq.first), mk_word_term(diseq.second)});
        }
        STRACE("str", tout << std::endl;);
        return result;
    }

    const bool theory_str::block_curr_assignment() {
        ast_manager& m = get_manager();
        expr *refinement = nullptr;
        STRACE("str", tout << "[Assert Axioms]\nformulas:\n";);
        for (const auto& we : m_word_eq_todo) {
            expr *const e = m.mk_not(mk_eq_atom(we.first, we.second));
            refinement = refinement == nullptr ? e : m.mk_or(refinement, e);
            STRACE("str", tout << we.first << " = " << we.second << '\n';);
        }
        for (const auto& wi : m_word_diseq_todo) {
            expr *const e = mk_eq_atom(wi.first, wi.second);
            refinement = refinement == nullptr ? e : m.mk_or(refinement, e);
            STRACE("str", tout << wi.first << " != " << wi.second << '\n';);
        }
        if (refinement != nullptr) {
            assert_axiom(refinement);
            STRACE("str", tout << "assertion:\n" << mk_pp(refinement, m) << "\n\n" << std::flush;);
            return true;
        }
        return false;
    }

}
