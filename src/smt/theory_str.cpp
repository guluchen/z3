#include <algorithm>
#include "ast/ast_pp.h"
#include "smt/theory_str.h"
#include "smt/smt_context.h"
#include "smt/smt_model_generator.h"

namespace smt {

    namespace str {

        using namespace std::placeholders;

        std::size_t element::hash::operator()(const element& e) const {
            using enum_t = std::underlying_type<t>::type;
            static const auto string_hash{std::hash<std::string>{}};
            static const auto enum_t_hash{std::hash<enum_t>{}};
            const auto n = static_cast<enum_t>(e.type());
            return string_hash(e.value().encode()) ^ enum_t_hash(n);
        }

        const element& element::null() {
            static const element e{element::t::NONE, ""};
            return e;
        }

        bool element::operator==(const element& other) const {
            return other.m_type == m_type && other.m_value == m_value;
        }

        bool element::operator<(const element& other) const {
            if (m_type < other.m_type) return true;
            if (m_type > other.m_type) return false;
            return m_value < other.m_value;
        }

        std::ostream& operator<<(std::ostream& os, const element& s) {
            os << s.value();
            return os;
        }

        std::size_t word_term::hash::operator()(const word_term& w) const {
            static const auto element_hash{element::hash{}};
            std::size_t result{37633};
            for (const auto& e : w.m_elements) {
                result += element_hash(e);
            }
            return result;
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

        bool word_term::prefix_const_mismatched(const word_term& w1, const word_term& w2) {
            if (w1.empty() || w2.empty()) return false;

            auto it1 = w1.m_elements.begin();
            auto it2 = w2.m_elements.begin();
            while (*it1 == *it2) {
                if (++it1 == w1.m_elements.end() || ++it2 == w2.m_elements.end()) return false;
            }
            return it1->typed(element::t::CONST) && it2->typed(element::t::CONST) &&
                   it1->value() != it2->value();
        }

        bool word_term::suffix_const_mismatched(const word_term& w1, const word_term& w2) {
            if (w1.empty() || w2.empty()) return false;

            auto it1 = w1.m_elements.end();
            auto it2 = w2.m_elements.end();
            while (*it1 == *it2) {
                if (--it1 == w1.m_elements.begin() || --it2 == w2.m_elements.begin()) return false;
            }
            return it1->typed(element::t::CONST) && it2->typed(element::t::CONST) &&
                   it1->value() != it2->value();
        }

        bool word_term::unequalable_no_empty_var(const word_term& w1, const word_term& w2) {
            return (!w1.has_variable() && w1.length() < w2.length()) ||
                   (!w2.has_variable() && w2.length() < w1.length()) ||
                   prefix_const_mismatched(w1, w2) || suffix_const_mismatched(w1, w2);
        }

        bool word_term::unequalable(const word_term& w1, const word_term& w2) {
            return (!w1.has_variable() && w1.constant_num() < w2.constant_num()) ||
                   (!w2.has_variable() && w2.constant_num() < w1.constant_num()) ||
                   prefix_const_mismatched(w1, w2) || suffix_const_mismatched(w1, w2);
        }

        word_term::word_term(std::initializer_list<element> list) {
            m_elements.insert(m_elements.begin(), list.begin(), list.end());
        }

        std::size_t word_term::constant_num() const {
            static const auto& is_const = std::bind(&element::typed, _1, element::t::CONST);
            return (std::size_t) std::count_if(m_elements.begin(), m_elements.end(), is_const);
        }

        std::set<element> word_term::variables() const {
            std::set<element> result;
            for (const auto& e : m_elements) {
                if (e.typed(element::t::VAR)) {
                    result.insert(e);
                }
            }
            return result;
        }

        const element& word_term::head() const {
            return m_elements.empty() ? element::null() : m_elements.front();
        }

        bool word_term::has_constant() const {
            static const auto& is_const = std::bind(&element::typed, _1, element::t::CONST);
            return std::any_of(m_elements.begin(), m_elements.end(), is_const);
        }

        bool word_term::has_variable() const {
            static const auto& is_var = std::bind(&element::typed, _1, element::t::VAR);
            return std::any_of(m_elements.begin(), m_elements.end(), is_var);
        }

        bool word_term::check_head(const element::t& t) const {
            const element& h = head();
            return h && h.typed(t);
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

        bool word_term::operator==(const word_term& other) const {
            const auto begin = m_elements.begin();
            const auto end = m_elements.end();
            const auto other_begin = other.m_elements.begin();
            return m_elements.size() == other.m_elements.size() &&
                   std::mismatch(begin, end, other_begin).first == end; // no mismatch
        }

        bool word_term::operator<(const word_term& other) const {
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

        std::size_t word_equation::hash::operator()(const word_equation& we) const {
            static const auto word_term_hash{word_term::hash{}};
            return word_term_hash(we.m_lhs) + word_term_hash(we.m_rhs);
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

        std::set<element> word_equation::variables() const {
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
                SASSERT(m_lhs.length() <= 1);
                return m_lhs;
            }
            return word_term::null();
        }

        bool word_equation::unsolvable(const bool allow_empty_var) const {
            return allow_empty_var ? word_term::unequalable(m_lhs, m_rhs)
                                   : word_term::unequalable_no_empty_var(m_lhs, m_rhs);
        }

        bool word_equation::in_definition_form() const {
            return (bool) definition_var();
        }

        bool word_equation::check_heads(const element::t& lht, const element::t& rht) const {
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

        bool word_equation::operator==(const word_equation& other) const {
            return m_lhs == other.m_lhs && m_rhs == other.m_rhs;
        }

        bool word_equation::operator<(const word_equation& other) const {
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

        std::size_t state::hash::operator()(const state& s) const {
            static const auto element_hash{element::hash{}};
            static const auto word_equation_hash{word_equation::hash{}};
            static const auto language_hash{language::hash{}};
            std::size_t result{22447};
            result += s.m_allow_empty_var ? 10093 : 0;
            for (const auto& we : s.m_wes_to_satisfy) {
                result += word_equation_hash(we);
            }
            for (const auto& we : s.m_wes_to_fail) {
                result += word_equation_hash(we);
            }
            for (const auto& kv : s.m_lang_to_satisfy) {
                result += element_hash(kv.first) + language_hash(kv.second);
            }
            return result;
        }

        std::set<element> state::variables() const {
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

        std::vector<std::vector<word_term>> state::eq_classes() const {
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

        const word_equation& state::smallest_eq() const {
            return m_wes_to_satisfy.empty() ? word_equation::null()
                                            : *m_wes_to_satisfy.begin();
        }

        const word_equation& state::only_one_eq_left() const {
            return m_wes_to_satisfy.size() == 1 ? *m_wes_to_satisfy.begin()
                                                : word_equation::null();
        }

        bool state::in_definition_form() const {
            static const auto& in_def_form = std::mem_fn(&word_equation::in_definition_form);
            return std::all_of(m_wes_to_satisfy.begin(), m_wes_to_satisfy.end(), in_def_form);
        }

        bool state::in_solved_form() const {
            return (in_definition_form() && definition_acyclic()) || m_wes_to_satisfy.empty();
        }

        bool state::eq_classes_inconsistent() const {
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

        bool state::diseq_inconsistent() const {
            return !m_wes_to_fail.empty() && m_wes_to_fail.begin()->empty();
        }

        bool state::unsolvable_by_check() const {
            const auto& unsolvable = std::bind(&word_equation::unsolvable, _1, m_allow_empty_var);
            return std::any_of(m_wes_to_satisfy.begin(), m_wes_to_satisfy.end(), unsolvable) ||
                   diseq_inconsistent();
        }

        bool state::unsolvable_by_inference() const {
            return diseq_inconsistent() || eq_classes_inconsistent();
        }

        void state::add_word_eq(const word_equation& we) {
            SASSERT(we);

            if (we.empty()) return;
            word_equation&& trimmed = we.trim_prefix();
            if (trimmed.empty()) return;
            m_wes_to_satisfy.insert(std::move(trimmed));
        }

        void state::add_word_diseq(const word_equation& we) {
            SASSERT(we);

            word_equation&& trimmed = we.trim_prefix();
            if (trimmed.unsolvable(m_allow_empty_var)) return;
            m_wes_to_fail.insert(std::move(trimmed));
        }

        state state::replace(const element& tgt, const word_term& subst) const {
            state result{m_allow_empty_var};
            for (const auto& we : m_wes_to_satisfy) {
                result.add_word_eq(we.replace(tgt, subst));
            }
            for (const auto& we : m_wes_to_fail) {
                result.add_word_diseq(we.replace(tgt, subst));
            }
            return result;
        }

        state state::remove(const element& tgt) const {
            return replace(tgt, {});
        }

        state state::remove_all(const std::set<element>& tgt) const {
            state result{m_allow_empty_var};
            for (const auto& we : m_wes_to_satisfy) {
                result.add_word_eq(we.remove_all(tgt));
            }
            for (const auto& we : m_wes_to_fail) {
                result.add_word_diseq(we.remove_all(tgt));
            }
            return result;
        }

        bool state::operator==(const state& other) const {
            return m_allow_empty_var == other.m_allow_empty_var &&
                   m_wes_to_satisfy == other.m_wes_to_satisfy &&
                   m_wes_to_fail == other.m_wes_to_fail &&
                   m_lang_to_satisfy == other.m_lang_to_satisfy;
        }

        bool state::operator<(const state& other) const {
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

        bool state::dag_def_check_node(const def_graph& graph, const def_node& node,
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

        bool state::definition_acyclic() const {
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

        neilsen_transforms::move neilsen_transforms::move::add_record(const element& e) const {
            std::vector<element> r{m_record};
            r.push_back(e);
            return {m_from, m_type, std::move(r)};
        };

        neilsen_transforms::mk_move::mk_move(const state& s, const word_equation& src)
                : m_state{s}, m_src{src} {}

        std::list<neilsen_transforms::action> neilsen_transforms::mk_move::operator()() {
            if (src_vars_empty()) {
                SASSERT(!m_src.rhs().has_constant());
                return {prop_empty()};
            }
            if (src_var_is_const()) {
                return {prop_const()};
            }
            if (m_src.check_heads(element::t::VAR, element::t::VAR)) {
                return handle_two_var();
            }
            return handle_one_var();
        }

        bool neilsen_transforms::mk_move::src_vars_empty() {
            return m_state.allows_empty_var() && m_src.lhs().empty();
        }

        bool neilsen_transforms::mk_move::src_var_is_const() {
            const word_term& def_body = m_src.definition_body();
            return def_body && (def_body.length() == 1 || !def_body.has_variable());
        }

        neilsen_transforms::action neilsen_transforms::mk_move::prop_empty() {
            const std::set<element> empty_vars{m_src.rhs().variables()};
            const std::vector<element> record{empty_vars.begin(), empty_vars.end()};
            return {{m_state, move::t::TO_EMPTY, record}, m_state.remove_all(empty_vars)};
        }

        neilsen_transforms::action neilsen_transforms::mk_move::prop_const() {
            const element& var = m_src.definition_var();
            const word_term& def = m_src.definition_body();
            std::vector<element> record{var};
            record.insert(record.end(), def.content().begin(), def.content().end());
            return {{m_state, move::t::TO_CONST, record}, m_state.replace(var, def)};
        }

        std::list<neilsen_transforms::action> neilsen_transforms::mk_move::handle_two_var() {
            const head_pair& hh = m_src.heads();
            const element& x = hh.first;
            const element& y = hh.second;
            std::list<action> result;
            result.push_back({{m_state, move::t::TO_VAR_VAR, {x, y}}, m_state.replace(x, {y, x})});
            result.push_back({{m_state, move::t::TO_VAR_VAR, {y, x}}, m_state.replace(y, {x, y})});
            if (m_state.allows_empty_var()) {
                result.push_back({{m_state, move::t::TO_EMPTY, {x}}, m_state.remove(x)});
                result.push_back({{m_state, move::t::TO_EMPTY, {y}}, m_state.remove(y)});
            } else {
                result.push_back({{m_state, move::t::TO_VAR, {x, y}}, m_state.replace(x, {y})});
            }
            return result;
        }

        std::list<neilsen_transforms::action> neilsen_transforms::mk_move::handle_one_var() {
            const head_pair& hh = m_src.heads();
            const bool var_const_headed = hh.first.typed(element::t::VAR);
            const element& v = var_const_headed ? hh.first : hh.second;
            const element& c = var_const_headed ? hh.second : hh.first;
            std::list<action> result;
            result.push_back({{m_state, move::t::TO_CHAR_VAR, {v, c}}, m_state.replace(v, {c, v})});
            if (m_state.allows_empty_var()) {
                result.push_back({{m_state, move::t::TO_EMPTY, {v}}, m_state.remove(v)});
            } else {
                result.push_back({{m_state, move::t::TO_CONST, {c}}, m_state.replace(v, {c})});
            }
            return result;
        }

        bool neilsen_transforms::record_graph::contains(const state& s) const {
            return m_backward_def.find(s) != m_backward_def.end();
        }

        const std::list<neilsen_transforms::move>&
        neilsen_transforms::record_graph::incoming_moves(const state& s) const {
            SASSERT(contains(s));
            return m_backward_def.find(s)->second;
        }

        void neilsen_transforms::record_graph::add_move(move&& m, const state& s) {
            SASSERT(contains(m.m_from) && contains(s));
            m_backward_def[s].emplace_back(std::move(m));
        }

        const state& neilsen_transforms::record_graph::add_state(state&& s) {
            SASSERT(!contains(s));
            auto&& pair = std::make_pair(std::move(s), std::list<move>{});
            return m_backward_def.emplace(std::move(pair)).first->first;
        }

        neilsen_transforms::neilsen_transforms(state&& root) {
            const state& s = m_records.add_state(std::move(root));
            m_pending.emplace(s);
        }

        bool neilsen_transforms::should_explore_all() const {
            return false;
        }

        result neilsen_transforms::check(const bool split_var_empty_ahead) {
            if (in_status(result::SAT)) return m_status;
            if (split_var_empty_ahead && split_var_empty_cases() == result::SAT) {
                return m_status = result::SAT;
            }
            STRACE("str", tout << "[Check SAT]\n";);
            while (!m_pending.empty()) {
                const state& curr_s = m_pending.top();
                m_pending.pop();
                STRACE("str", tout << "from:\n" << curr_s << std::endl;);
                for (auto& action : transform(curr_s)) {
                    if (m_records.contains(action.second)) {
                        m_records.add_move(std::move(action.first), action.second);
                        STRACE("str", tout << "already visited:\n" << action.second << std::endl;);
                        continue;
                    }
                    const state& s = m_records.add_state(std::move(action.second));
                    m_records.add_move(std::move(action.first), s);
                    if (s.unsolvable_by_inference()) {
                        STRACE("str", tout << "failed:\n" << s << std::endl;);
                        continue;
                    }
                    if (s.in_solved_form()) {
                        STRACE("str", tout << "[Solved]\n" << s << std::endl;);
                        return m_status = result::SAT;
                    }
                    const word_equation& only_one_left = s.only_one_eq_left();
                    if (only_one_left && only_one_left.in_definition_form()) {
                        // solved form check failed, the we in definition form must be recursive
                        const word_equation& last_we_recursive_def = only_one_left;
                        if (!last_we_recursive_def.definition_body().has_constant()) {
                            STRACE("str", tout << "[Solved]\n" << s << std::endl;);
                            return m_status = result::SAT;
                        }
                        STRACE("str", tout << "failed:\n" << s << std::endl;);
                        continue;
                    }
                    STRACE("str", tout << "to:\n" << s << std::endl;);
                    m_pending.emplace(s);
                }
            }
            return result::UNSAT;
        }

        result neilsen_transforms::split_var_empty_cases() {
            STRACE("str", tout << "[Split Empty Variable Cases]\n";);
            std::queue<state_cref> pending{split_first_level_var_empty()};
            SASSERT(m_pending.empty());
            if (in_status(result::SAT)) return m_status;
            while (!pending.empty()) {
                const state& curr_s = pending.front();
                pending.pop();
                m_pending.emplace(curr_s);
                for (const auto& var : curr_s.variables()) {
                    state&& next_s = curr_s.remove(var);
                    next_s.allow_empty_var(false);
                    if (m_records.contains(next_s)) {
                        for (const auto& m : m_records.incoming_moves(curr_s)) {
                            m_records.add_move(m.add_record(var), next_s);
                        }
                        continue;
                    }
                    next_s.allow_empty_var(true);
                    if (!should_explore_all() && next_s.in_solved_form()) {
                        const state& s = m_records.add_state(std::move(next_s));
                        for (const auto& m : m_records.incoming_moves(curr_s)) {
                            m_records.add_move(m.add_record(var), s);
                        }
                        STRACE("str", tout << "[Solved]\n" << s << std::endl;);
                        return m_status = result::SAT;
                    }
                    if (next_s.unsolvable_by_check()) {
                        next_s.allow_empty_var(false);
                        const state& s = m_records.add_state(std::move(next_s));
                        for (const auto& m : m_records.incoming_moves(curr_s)) {
                            m_records.add_move(m.add_record(var), s);
                        }
                        STRACE("str", tout << "failed:\n" << curr_s << std::endl;);
                        continue;
                    }
                    next_s.allow_empty_var(false);
                    const state& s = m_records.add_state(std::move(next_s));
                    for (const auto& m : m_records.incoming_moves(curr_s)) {
                        m_records.add_move(m.add_record(var), s);
                    }
                    pending.emplace(s);
                    STRACE("str", tout << "add:\n" << s << std::endl;);
                }
            }
            SASSERT(in_status(result::UNKNOWN));
            return m_status;
        }

        std::queue<state_cref> neilsen_transforms::split_first_level_var_empty() {
            std::queue<state_cref> result;
            while (!m_pending.empty()) {
                const state& curr_s = m_pending.top();
                m_pending.pop();
                for (const auto& var : curr_s.variables()) {
                    state&& next_s = curr_s.remove(var);
                    next_s.allow_empty_var(false);
                    if (m_records.contains(next_s)) {
                        m_records.add_move({curr_s, move::t::TO_EMPTY, {var}}, next_s);
                        continue;
                    }
                    next_s.allow_empty_var(true);
                    if (!should_explore_all() && next_s.in_solved_form()) {
                        const state& s = m_records.add_state(std::move(next_s));
                        m_records.add_move({curr_s, move::t::TO_EMPTY, {var}}, s);
                        m_status = result::SAT;
                        STRACE("str", tout << "[Solved]\n" << s << std::endl;);
                        return {};
                    }
                    if (next_s.unsolvable_by_check()) {
                        next_s.allow_empty_var(false);
                        const state& s = m_records.add_state(std::move(next_s));
                        m_records.add_move({curr_s, move::t::TO_EMPTY, {var}}, s);
                        STRACE("str", tout << "failed:\n" << curr_s << std::endl;);
                        continue;
                    }
                    next_s.allow_empty_var(false);
                    const state& s = m_records.add_state(std::move(next_s));
                    m_records.add_move({curr_s, move::t::TO_EMPTY, {var}}, s);
                    result.emplace(s);
                    STRACE("str", tout << "add:\n" << s << std::endl;);
                }
            }
            return result;
        }

        std::list<neilsen_transforms::action> neilsen_transforms::transform(const state& s) const {
            SASSERT(!s.unsolvable_by_check() && s.word_eq_num() != 0);
            // no diseq-only handling for now
            return mk_move{s, s.smallest_eq()}();
        }

    }

    theory_str::theory_str(ast_manager& m, const theory_str_params& params)
            : theory{m.mk_family_id("seq")}, m_params{params}, m_util_a{m}, m_util_s{m},
              m_fresh_id{0}, m_rewrite{m} {}

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
        STRACE("str",
               tout << "mk_var for " << mk_pp(n->get_owner(), get_manager()) << std::endl;);
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
        context& ctx = get_context();
        unsigned nFormulas = ctx.get_num_asserted_formulas();
        for (unsigned i = 0; i < nFormulas; ++i) {
            //expr * ex = ctx.get_asserted_formula(i);
            //set_up_axioms(ex);
        }
        STRACE("str", tout << "init search" << std::endl;);
    }

    void theory_str::relevant_eh(app *const n) {
        if (m_util_s.str.is_extract(n)) {
            add_extract_axiom(n);
        }
        if (m_util_s.str.is_index(n) ||
            m_util_s.str.is_replace(n) ||
            m_util_s.str.is_extract(n) ||
            m_util_s.str.is_at(n) ||
            m_util_s.str.is_empty(n) ||
            m_util_s.str.is_string(n) ||
            m_util_s.str.is_itos(n) ||
            m_util_s.str.is_stoi(n)) {
            std::cout << "relevant: " << mk_pp(n, get_manager()) << std::endl;

            app *new_var = mk_str_var("a");
            std::cout << "new var: " << mk_pp(new_var, get_manager()) << std::endl;
        }
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
        if (is_word_term(l) && is_word_term(r)) {
            m_word_eq_todo.push_back({l, r});
            STRACE("str", tout << "new eq: " << mk_pp(l, m) << " = " << mk_pp(r, m) << std::endl;);
        }
    }

    void theory_str::new_diseq_eh(theory_var x, theory_var y) {
        ast_manager& m = get_manager();
        const expr_ref l{get_enode(x)->get_owner(), m};
        const expr_ref r{get_enode(y)->get_owner(), m};
        if (is_word_term(l) && is_word_term(r)) {
            m_word_diseq_todo.push_back({l, r});
            STRACE("str",
                   tout << "new diseq: " << mk_pp(l, m) << " != " << mk_pp(r, m) << std::endl;);
        }
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
        using namespace str;
        if (m_word_eq_todo.empty()) return FC_DONE;
        TRACE("str", tout << "final_check level " << get_context().get_scope_level() << std::endl;);

        str::state&& root = mk_state_from_todo();
        STRACE("str", tout << "root built:\n" << root << std::endl;);
        if (root.unsolvable_by_inference() && block_curr_assignment()) {
            return FC_CONTINUE;
        }
        neilsen_transforms solver{std::move(root)};
        if (solver.check() == result::SAT) {
            return FC_DONE;
        } else if (block_curr_assignment()) {
            return FC_CONTINUE;
        } else {
            dump_assignments();
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

    void theory_str::assert_axiom(literal l1, literal l2, literal l3, literal l4, literal l5) {
        context& ctx = get_context();
        literal_vector lits;
        if (l1 == true_literal || l2 == true_literal || l3 == true_literal || l4 == true_literal ||
            l5 == true_literal)
            return;
        if (l1 != null_literal && l1 != false_literal) {
            ctx.mark_as_relevant(l1);
            lits.push_back(l1);
        }
        if (l2 != null_literal && l2 != false_literal) {
            ctx.mark_as_relevant(l2);
            lits.push_back(l2);
        }
        if (l3 != null_literal && l3 != false_literal) {
            ctx.mark_as_relevant(l3);
            lits.push_back(l3);
        }
        if (l4 != null_literal && l4 != false_literal) {
            ctx.mark_as_relevant(l4);
            lits.push_back(l4);
        }
        if (l5 != null_literal && l5 != false_literal) {
            ctx.mark_as_relevant(l5);
            lits.push_back(l5);
        }
        TRACE("seq", ctx.display_literals_verbose(tout << "assert:\n", lits);
                tout << "\n";);
        ctx.mk_th_axiom(get_id(), lits.size(), lits.c_ptr());
    }

    /*
      Note: this is copied from theory_seq.cpp
      TBD: check semantics of extract, a.k.a, substr(s, i ,l)

      let e = extract(s, i, l)

      i is start index, l is length of substring starting at index.

      i < 0 => e = ""
      i >= |s| => e = ""
      l <= 0 => e = ""
      0 <= i < |s| & l > 0 => s = xey, |x| = i, |e| = min(l, |s|-i)

    this translates to:

      0 <= i <= |s| -> s = xey
      0 <= i <= |s| -> len(x) = i
      0 <= i <= |s| & 0 <= l <= |s| - i -> |e| = l
      0 <= i <= |s| & |s| < l + i  -> |e| = |s| - i
      i >= |s| => |e| = 0
      i < 0 => |e| = 0
      l <= 0 => |e| = 0

      It follows that:
      |e| = min(l, |s| - i) for 0 <= i < |s| and 0 < |l|
    */

    void theory_str::add_extract_axiom(expr *e) {
        ast_manager& m = get_manager();
        TRACE("seq", tout << mk_pp(e, m) << "\n";);
        expr *s = nullptr, *i = nullptr, *l = nullptr;
        VERIFY(m_util_s.str.is_extract(e, s, i, l));

        expr_ref x(mk_str_var("x"), m);
        expr_ref ls(m_util_s.str.mk_length(s), m);
        expr_ref lx(m_util_s.str.mk_length(x), m);
        expr_ref le(m_util_s.str.mk_length(e), m);
        expr_ref ls_minus_i_l(m_util_a.mk_sub(m_util_a.mk_sub(ls, i), l), m);
        expr_ref y(mk_str_var("y"), m);
        expr_ref xe(m_util_s.str.mk_concat(x, e), m);
        expr_ref xey(m_util_s.str.mk_concat(xe, y), m);
        expr_ref zero(m_util_a.mk_int(0), m);
        expr_ref i_minus_ls(m_util_a.mk_sub(i, ls), m);

        literal i_ge_0 = mk_literal(m_util_a.mk_ge(i, zero));
        literal ls_le_i = mk_literal(m_util_a.mk_le(i_minus_ls, zero));
        literal li_ge_ls = mk_literal(m_util_a.mk_ge(ls_minus_i_l, zero));
        literal l_ge_zero = mk_literal(m_util_a.mk_ge(l, zero));
        literal ls_le_0 = mk_literal(m_util_a.mk_le(ls, zero));

        assert_axiom(~i_ge_0, ~ls_le_i, mk_eq(xey, s, false));
        assert_axiom(~i_ge_0, ~ls_le_i, mk_eq(lx, i, false));
        assert_axiom(~i_ge_0, ~ls_le_i, ~l_ge_zero, ~li_ge_ls, mk_eq(le, l, false));
        assert_axiom(~i_ge_0, ~ls_le_i, li_ge_ls, mk_eq(le, m_util_a.mk_sub(ls, i), false));
        assert_axiom(~i_ge_0, ~ls_le_i, l_ge_zero, mk_eq(le, zero, false));
        assert_axiom(i_ge_0, mk_eq(le, zero, false));
        assert_axiom(ls_le_i, mk_eq(le, zero, false));
        assert_axiom(~ls_le_0, mk_eq(le, zero, false));
    }

    void theory_str::dump_assignments() const {
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

    bool theory_str::is_theory_str_term(expr *const e) const {
        return m_util_s.str.is_string_term(e);
    }

    bool theory_str::is_word_term(expr *const e) const {
        zstring s;
        if (m_util_s.str.is_string(e, s)) {
            return true;
        } else if (m_util_s.str.is_concat(e)) {
            str::word_term result;
            for (unsigned i = 0; i < to_app(e)->get_num_args(); i++) {
                if (!is_word_term(to_app(e)->get_arg(i))) {
                    return false;
                }
            }
            return true;
        }
        return false;
    }

    app *theory_str::mk_str_var(std::string name) {
        context& ctx = get_context();
        sort *string_sort = m_util_s.str.mk_string_sort();

        //the code below create an array of integer expressions of size one with a fresh integer value
        expr *args[1] = {m_util_a.mk_numeral(rational(m_fresh_id), true)};
        m_fresh_id++;
        unsigned len = 1;

        app *a = m_util_s.mk_skolem(symbol(name.c_str()), len, args, string_sort);
        ctx.internalize(a, false);
        mk_var(ctx.get_enode(a));

        return a;
    }

    literal theory_str::mk_literal(expr *const e) {
        ast_manager& m = get_manager();
        expr_ref ex(e, m);
        m_rewrite(ex);
        context& ctx = get_context();

        std::cout << "internalize " << mk_pp(ex, m) << "\n";

        if (!ctx.e_internalized(ex)) {
            ctx.internalize(ex, false);
        }
        enode *n = ctx.get_enode(ex);
        ctx.mark_as_relevant(n);
        return ctx.get_literal(ex);
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
            result.add_word_eq({mk_word_term(eq.first), mk_word_term(eq.second)});
            STRACE("str", tout << eq.first << " = " << eq.second << std::endl;);
        }
        STRACE("str", tout << "word disequality todo:\n";);
        STRACE("str", if (m_word_diseq_todo.empty()) tout << "--\n";);
        for (const auto& diseq : m_word_diseq_todo) {
            result.add_word_diseq({mk_word_term(diseq.first), mk_word_term(diseq.second)});
            STRACE("str", tout << diseq.first << " != " << diseq.second << '\n';);
        }
        STRACE("str", tout << std::endl;);
        return result;
    }

    bool theory_str::block_curr_assignment() {
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
