#include <algorithm>
#include <functional>
#include "ast/ast_ll_pp.h"
#include "ast/ast_pp.h"
#include "ast/ast_smt2_pp.h"
#include "ast/ast_util.h"
#include "ast/rewriter/seq_rewriter.h"
#include "smt_kernel.h"
#include "smt/smt_context.h"
#include "smt/smt_model_generator.h"
#include "smt/theory_arith.h"
#include "smt/theory_seq_empty.h"
#include "smt/theory_str.h"

/* TODO:
 *  1. better algorithm for checking solved form
 *  2. on-the-fly over-approximation
 *  3. better algorithm for computing state transform
 */

namespace smt {

    namespace str {

        using namespace std::placeholders;

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

        const element_set word_term::variables() const {
            element_set result;
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

        const element_set word_equation::variables() const {
            element_set result;
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

        word_equation word_equation::remove_all(const element_set& tgt) const {
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

        const element_set state::variables() const {
            element_set result;
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

        const bool state::unsolvable() const {
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
            return m_wes_to_fail.empty() &&
                   ((in_definition_form() && definition_acyclic()) || m_wes_to_satisfy.empty());
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

            if (we.unsolvable(m_allow_empty_var)) return;
            m_wes_to_fail.insert(we.trim_prefix());
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

        state state::remove_all(const element_set& tgt) const {
            state result{m_allow_empty_var};
            for (const auto& we : m_wes_to_satisfy) {
                result.satisfy_constraint(we.remove_all(tgt));
            }
            for (const auto& we : m_wes_to_fail) {
                result.fail_constraint(we.remove_all(tgt));
            }
            return result;
        }

        const state_list state::transform() const {
            const word_equation& curr_we = transformation_source();
            SASSERT(!unsolvable() && curr_we);

            const head_pair& hh = curr_we.heads();
            state_list result;
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

        const word_equation& state::transformation_source() const {
            if (m_wes_to_satisfy.empty()) {
                if (m_wes_to_fail.empty()) return word_equation::null();
                SASSERT(!m_wes_to_fail.begin()->empty());
                return *m_wes_to_fail.begin();
            }
            if (m_wes_to_fail.empty()) return *m_wes_to_satisfy.begin();
            SASSERT(!m_wes_to_fail.begin()->empty());
            return std::min(*m_wes_to_satisfy.begin(), *m_wes_to_fail.begin());
        }

        void state::transform_one_var(const head_pair& hh, state_list& result) const {
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

        void state::transform_two_var(const head_pair& hh, state_list& result) const {
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
                if (curr_case.unsolvable()) {
                    STRACE("str", tout << "failed:\n" << curr_case << std::endl;);
                    continue;
                }
                m_processed.insert(curr_case);
                STRACE("str", tout << "add:\n" << curr_case << std::endl;);
                for (const auto& var : curr_case.variables()) {
                    m_pending.push(curr_case.remove(var));
                }
            }
            state_set processed;
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

    theory_str::theory_str(ast_manager& m, const theory_str_params& params) :
            theory{m.mk_family_id("seq")}, m_scope_level{0}, m_params{params} {
    }

    void theory_str::display(std::ostream& os) const {
        os << "theory_str display" << std::endl;
    }

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
        STRACE("str", tout << "internalizing term: " << mk_ismt2_pp(term, m) << std::endl;);

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

    theory_var theory_str::mk_var(enode *const n) {
        STRACE("str", tout << "mk_var for " << mk_pp(n->get_owner(), get_manager()) << std::endl;);
        if (!(is_theory_str_term(n->get_owner()))) {
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

    model_value_proc *theory_str::mk_value(enode *const n, model_generator& mg) {
        ast_manager& m = get_manager();
        app_ref owner{m};
        owner = n->get_owner();
        // if the owner is not internalized, it doesn't have an e-node associated.
        SASSERT(get_context().e_internalized(owner));
        STRACE("str", tout << "mk_value for: " << mk_ismt2_pp(owner, m) << " (sort "
                           << mk_ismt2_pp(m.get_sort(owner), m) << ")" << std::endl;);
        return alloc(expr_wrapper_proc, owner);
    }

    void theory_str::add_theory_assumptions(expr_ref_vector& assumptions) {
        STRACE("str", tout << "add theory assumption for theory_str" << std::endl;);
    }

    lbool theory_str::validate_unsat_core(expr_ref_vector& unsat_core) {
        return l_undef;
    }

    void theory_str::new_eq_eh(theory_var x, theory_var y) {
        ast_manager& m = get_manager();
        enode *const n1 = get_enode(x);
        enode *const n2 = get_enode(y);
        const str::expr_pair we{expr_ref{n1->get_owner(), m}, expr_ref{n2->get_owner(), m}};
        m_we_expr_memo.push_back(we);
        STRACE("str", tout << "new eq: " << mk_ismt2_pp(n1->get_owner(), m) << " = "
                           << mk_ismt2_pp(n2->get_owner(), m) << std::endl;);
    }

    void theory_str::new_diseq_eh(theory_var x, theory_var y) {
        ast_manager& m = get_manager();
        enode *const n1 = get_enode(x);
        enode *const n2 = get_enode(y);
        const str::expr_pair wi{expr_ref{n1->get_owner(), m}, expr_ref{n2->get_owner(), m}};
        m_wi_expr_memo.push_back(wi);
        STRACE("str", tout << "new diseq: not (" << mk_ismt2_pp(n1->get_owner(), m) << " = "
                           << mk_ismt2_pp(n2->get_owner(), m) << ')' << std::endl;);
    }

    void theory_str::init_search_eh() {
        STRACE("str", tout << "init search" << std::endl;);
    }

    void theory_str::relevant_eh(app *const n) {
        (void) n;
        STRACE("str", tout << "relevant: " << mk_ismt2_pp(n, get_manager()) << std::endl;);
    }

    void theory_str::assign_eh(bool_var v, const bool is_true) {
        // YFC: membership constraint goes here
        (void) v;
        (void) is_true;
        STRACE("str", tout << "assign: v" << v << " #" << get_context().bool_var2expr(v)->get_id()
                           << " is_true: " << is_true << std::endl;);
    }

    void theory_str::push_scope_eh() {
        m_scope_level += 1;
        m_we_expr_memo.push_scope();
        m_wi_expr_memo.push_scope();
        STRACE("str", tout << "push to " << m_scope_level << std::endl;);
    }

    void theory_str::pop_scope_eh(const unsigned num_scopes) {
        m_scope_level -= num_scopes;
        m_we_expr_memo.pop_scope(num_scopes);
        m_wi_expr_memo.pop_scope(num_scopes);
        STRACE("str", tout << "pop " << num_scopes << " to " << m_scope_level << std::endl;);
    }

    void theory_str::reset_eh() {
        STRACE("str", tout << "resetting" << std::endl;);
    }

    final_check_status theory_str::final_check_eh() {
        context& ctx = get_context();
        (void) ctx;
        TRACE("str", tout << "final_check at level " << ctx.get_scope_level() << std::endl;);

        const str::state& root = build_state_from_memo();
        STRACE("str", tout << "root built:\n" << root << std::endl;);
        str::neilson_based_solver solver{root};
        if (root.unsolvable_by_inference() && block_dpllt_assignment_from_memo()) {
            return FC_CONTINUE;
        }
        solver.check_sat();
        if (solver.solution_found()) {
            STRACE("str", tout << "[Solved]\n";);
            return FC_DONE;
        }

        if (block_dpllt_assignment_from_memo()) {
            return FC_CONTINUE;
        } else {
            STRACE("str", dump_assignments(););
            return FC_DONE;
        }
    }

    bool theory_str::can_propagate() {
        return false;
    }

    void theory_str::propagate() {
        STRACE("str", tout << "propagating..." << std::endl;);
    }

    void theory_str::init_model(model_generator& mg) {
        STRACE("str", tout << "initializing model..." << std::endl;);
    }

    void theory_str::finalize_model(model_generator& mg) {
        STRACE("str", tout << "finalizing model..." << std::endl;);
    }

    void theory_str::assert_axiom(expr *const e) {
        if (e == nullptr || get_manager().is_true(e)) return;

        ast_manager& m = get_manager();
        context& ctx = get_context();
        expr_ref ex{e, m};
        if (!ctx.b_internalized(ex)) {
            ctx.internalize(ex, false);
        }
        literal lit(ctx.get_literal(ex));
        ctx.mark_as_relevant(lit);
        ctx.mk_th_axiom(get_id(), 1, &lit);
    }

    void theory_str::dump_assignments() {
        STRACE("str", \
                ast_manager& m = get_manager();
                context& ctx = get_context();
                tout << "dumping all assignments:\n";
                expr_ref_vector assignments{m};
                ctx.get_assignments(assignments);
                for (expr *const e : assignments) {
                    tout << mk_ismt2_pp(e, m) << (ctx.is_relevant(e) ? "\n" : " (NOT REL)\n")
                         << std::flush;
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
        for (const auto& wi : m_wi_expr_memo) {
            STRACE("str", tout << "not  (" << wi.first << " = " << wi.second << ")\n";);
            const str::word_term& lhs = get_word_term(wi.first);
            const str::word_term& rhs = get_word_term(wi.second);
            result.fail_constraint(str::word_equation{rhs, lhs});
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
