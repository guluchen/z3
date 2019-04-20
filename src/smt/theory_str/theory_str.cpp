#include <algorithm>
#include <numeric>
#include <sstream>
#include "ast/ast_pp.h"
#include "ast/rewriter/bool_rewriter.h"
#include "smt/theory_str/theory_str.h"
#include "smt/smt_context.h"
#include "smt/smt_model_generator.h"
#include "smt/theory_lra.h"
#include "smt/theory_arith.h"
#include "smt/smt_context.h"
#include "ast/seq_decl_plugin.h"
#include "ast/reg_decl_plugins.h"


namespace smt {
    bool theory_str::ignore_membership=false;

    namespace str {
        size_t element::var_num=0;
        std::set<element> element::variables= std::set<element>();
        using namespace std::placeholders;

        std::size_t element::hash::operator()(const element& e) const {
            using enum_t = std::underlying_type<t>::type;
            static const auto string_hash{std::hash<std::string>{}};
            static const auto enum_t_hash{std::hash<enum_t>{}};
            const auto n = static_cast<enum_t>(e.type());
            return string_hash(e.value().encode()) ^ enum_t_hash(n);
        }

        const element& element::null() {
            static const element e{element::t::NONE, "", nullptr};
            return e;
        }
        const element& element::multiple() {
            static const element e{element::t::NONE, "m", nullptr};
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
            static const auto element_hash{element::hash{}};

            if(s.typed(element::t::CONST))
                os << s.value();
            else
                os << s.shortname();
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
                result.m_elements.push_back({element::t::CONST, {str[i]}, nullptr});
            }
            return result;
        }

        word_term word_term::from_variable(const zstring& name, expr *e) {
            return {{element::t::VAR, name, e}};
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


        word_term::word_term(std::initializer_list<element> list) {
            m_elements.insert(m_elements.begin(), list.begin(), list.end());
        }
        word_term::word_term(const std::list<element>& list){
            m_elements.insert(m_elements.begin(), list.begin(), list.end());
        }
        std::size_t word_term::count_const() const {
            static const auto& is_const = std::bind(&element::typed, _1, element::t::CONST);
            return (std::size_t) std::count_if(m_elements.begin(), m_elements.end(), is_const);
        }

        std::size_t word_term::count_var(const element& tgt) const {
            SASSERT(tgt.typed(element::t::VAR));

            std::size_t result = 0;
            for (const auto& e : m_elements) {
                result = e == tgt ? result + 1 : result;
            }
            return result;
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

        std::size_t word_equation::count_var(const element& e) const {
            return m_lhs.count_var(e) + m_rhs.count_var(e);
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


        bool word_term::unequalable(const word_term& w1, const word_term& w2, const std::set<element>& non_emp_var )  {
            return (!w1.has_variable() && w1.length() < w2.minimal_model_length(non_emp_var)) ||
                   (!w2.has_variable() && w2.length() < w1.minimal_model_length(non_emp_var)) ||
                   word_term::prefix_const_mismatched(w1, w2) || word_term::suffix_const_mismatched(w1, w2);
        }

        bool word_equation::unsolvable(const std::set<element>& non_empty_var ) const {
                return word_term::unequalable(lhs(),rhs(),non_empty_var);
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

        var_relation::var_relation(const state& s) {
            SASSERT(s.in_definition_form());

            m_heads = s.variables();
            for (const auto& we : s.word_eqs()) {
                const node& n = we.definition_var();
                if (m_record.find(n) != m_record.end()) { // var definition not unique
                    m_valid = false;
                    return;
                }
                nodes&& related = we.definition_body().variables();
                for (const auto& r : related) {
                    m_heads.erase(r);
                }
                m_record.emplace(std::make_pair(n, std::move(related)));
                m_definition.emplace(std::make_pair(n, we.definition_body()));
            }
        }

        bool var_relation::check_straight_line(const node& n) {
            if (m_straight_line.find(n) != m_straight_line.end()) return true;
            if (m_visited.find(n) != m_visited.end()) return false;

            m_visited.insert(n);
            const auto& var_related = m_record.find(n);
            if (var_related != m_record.end()) {
                for (const auto& related : var_related->second) {
                    if (!check_straight_line(related)) return false;
                }
            }
            m_straight_line.insert(n);
            return true;
        }

        bool var_relation::is_straight_line() {
            if (!is_valid()) return false;

            for (const auto& var_related : m_record) {
                if (!check_straight_line(var_related.first)) return false;
            }
            return true;
        };

        memberships::~memberships() = default;

        std::ostream& operator<<(std::ostream& os, const memberships::sptr m) {
            return m->display(os);
        }

        std::size_t basic_memberships::hash() {
            static const auto element_hash{element::hash{}};
            std::size_t result{40099};
            result += m_inconsistent ? 25939 : 0;
            for (const auto& kv : m_record) {
                result += element_hash(kv.first);
            }
            return result;
        }

        std::set<element> basic_memberships::variables() {
            std::set<element> result;
            for (const auto& kv : m_record) {
                result.insert(kv.first);
            }
            return result;
        }

        void basic_memberships::set(const element& var, expr *re) {
            auto fit = m_record.find(var);
            automaton::sptr aut = m_aut_maker->mk_from_re_expr(re, true);
            if (aut->is_empty()) {
                m_inconsistent = true;
            }
            if (fit != m_record.end()) {
                fit->second.ref = aut;
                return;
            }
            m_record.emplace(std::make_pair(var, aut));
        }

        automaton::sptr basic_memberships::get(const element& var) {
            auto fit = m_record.find(var);
            return fit != m_record.end() ? fit->second.ref : nullptr;
        }

        memberships::ptr basic_memberships::assign_empty(const element& var) {
            basic_memberships *result = shallow_copy();
            auto fit = result->m_record.find(var);
            if (fit == result->m_record.end()) {
                return mk_ptr(result);
            }

            if (fit->second.ref->is_final(fit->second.ref->get_init())) {
                result->m_record.erase(var);
            } else {
                result->m_inconsistent = true;
            }
            return mk_ptr(result);
        }

        basic_memberships::ptr basic_memberships::assign_empty_all(const std::set<element>& vars) {
            basic_memberships *result = shallow_copy();
            for (const auto& var : vars) {
                auto fit = result->m_record.find(var);
                if (fit == result->m_record.end()) continue;

                if (fit->second.ref->is_final(fit->second.ref->get_init())) {
                    result->m_record.erase(var);
                } else {
                    result->m_inconsistent = true;
                    break;
                }
            }
            return mk_ptr(result);
        }

        basic_memberships::ptr
        basic_memberships::assign_const(const element& var, const word_term& tgt) {
            basic_memberships *result = shallow_copy();
            auto fit = result->m_record.find(var);
            if (fit == result->m_record.end()) {
                return mk_ptr(result);
            }

            const std::list<element>& es = tgt.content();
            static const auto concat = [](const zstring& acc, const element& e) {
                return acc + e.value();
            };
            const zstring& str = std::accumulate(es.begin(), es.end(), zstring{}, concat);
            const automaton::sptr aut = remove_prefix(fit->second.ref, str);
            if (aut->is_empty()) {
                result->m_inconsistent = true;
            }
            fit->second.ref = aut;
            return mk_ptr(result);
        }

        basic_memberships::ptr
        basic_memberships::assign_as(const element& var, const element& as_var) {
            basic_memberships *result = shallow_copy();
            auto fit_from = result->m_record.find(var);
            if (fit_from == result->m_record.end()) {
                return mk_ptr(result);
            }
            auto fit_to = result->m_record.find(as_var);
            if (fit_to == result->m_record.end()) {
                result->m_record.emplace(std::make_pair(as_var, fit_from->second));
                result->m_record.erase(fit_from);
                return mk_ptr(result);
            }
            automaton::sptr aut = fit_from->second.ref->intersect_with(fit_to->second.ref);
            if (aut->is_empty()) {
                result->m_inconsistent = true;
            }
            fit_to->second.ref = aut; // TODO: see if need to erase fit_from
            return mk_ptr(result);
        }

        std::list<basic_memberships::ptr>
        basic_memberships::assign_prefix(const element& var, const element& ch) {
            std::list<ptr> result;
            basic_memberships *a = shallow_copy();
            auto fit = a->m_record.find(var);
            if (fit == a->m_record.end()) {
                result.emplace_back(mk_ptr(a));
                return result;
            }

            const automaton::sptr aut = remove_prefix(fit->second.ref, ch.value());
            if (aut->is_empty()) {
                a->m_inconsistent = true;
            }
            fit->second.ref = aut;
            result.emplace_back(mk_ptr(a));
            return result;
        }

        std::list<basic_memberships::ptr>
        basic_memberships::assign_prefix_var(const element& var, const element& prefix) {
            std::list<ptr> result;
            auto fit_var = m_record.find(var);
            if (fit_var == m_record.end()) {
                result.emplace_back(mk_ptr(shallow_copy()));
                return result;
            }
            auto fit_prefix = m_record.find(prefix);
            const bool prefix_has_constraint = fit_prefix != m_record.end();
            for (auto& prefix_suffix : fit_var->second.ref->split()) {
                automaton::sptr aut_prefix = std::move(prefix_suffix.first);
                if (prefix_has_constraint) {
                    aut_prefix = aut_prefix->intersect_with(fit_prefix->second.ref);
                    if (aut_prefix->is_empty()) continue;
                }
                automaton::sptr aut_suffix = std::move(prefix_suffix.second);
                basic_memberships *m = shallow_copy();
                m->m_record[prefix].ref = aut_prefix;
                m->m_record[var].ref = aut_suffix;
                result.emplace_back(mk_ptr(m));
            }
            return result;
        }

        std::ostream& basic_memberships::display(std::ostream& os) {
            if (m_inconsistent) {
                os << "(membership inconsistent)\n";
            }
            for (const auto& var_lang : m_record) {
                os << var_lang.first << " {\n" << var_lang.second.ref << "}\n";
            }
            return os << std::flush;
        }

        bool basic_memberships::operator==(const memberships& other) {
            const auto o = static_cast<const basic_memberships *>(&other);
            return m_inconsistent == o->m_inconsistent && m_record == o->m_record;
        }

        basic_memberships *basic_memberships::shallow_copy() const {
            basic_memberships *copy = new basic_memberships(m_aut_maker);
            copy->m_inconsistent = m_inconsistent;
            copy->m_record.insert(m_record.begin(), m_record.end());
            return copy;
        }

        memberships::ptr basic_memberships::mk_ptr(basic_memberships *m) const {
            return ptr{m};
        }

        automaton::sptr
        basic_memberships::remove_prefix(automaton::sptr a, const zstring& prefix) const {
            std::list<automaton::ptr> as = a->remove_prefix(prefix);
            const automaton::sptr empty = m_aut_maker->mk_empty();
            static const auto mk_union = [](automaton::sptr a1, automaton::ptr& a2) {
                return a1->union_with(std::move(a2));
            };
            return std::accumulate(as.begin(), as.end(), empty, mk_union)->determinize();
        }

        std::size_t state::hash::operator()(const state& s) const {
            static const auto word_equation_hash{word_equation::hash{}};
            std::size_t result{22447};
            result += (s.get_strategy()==state::transform_strategy::allow_empty_var)? 10093 : 0;
            for (const auto& we : s.m_eq_wes) {
                result += word_equation_hash(we);
            }
            if(!theory_str::ignore_membership) {
                for (const auto& we : s.m_diseq_wes) {
                    result += word_equation_hash(we);
                }
                result += s.m_memberships->hash();
            }
            return result;
        }

        std::set<element> state::variables() const {
            std::set<element> result;
            for (const auto& we : m_eq_wes) {
                for (const auto& v : we.variables()) {
                    result.insert(v);
                }
            }
            for (const auto& we : m_diseq_wes) {
                for (const auto& v : we.variables()) {
                    result.insert(v);
                }
            }
            for (const auto& v : m_memberships->variables()) {
                result.insert(v);
            }
            return result;
        }

        std::vector<std::vector<word_term>> state::eq_classes() const {
            std::map<word_term, std::size_t> word_class_tbl;
            std::vector<std::vector<word_term>> classes;
            for (const auto& we : m_eq_wes) {
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
            return m_eq_wes.empty() ? word_equation::null() : *m_eq_wes.begin();
        }

        const word_equation& state::only_one_eq_left() const {
            return m_eq_wes.size() == 1 ? *m_eq_wes.begin() : word_equation::null();
        }

        var_relation state::var_rel_graph() const {
            SASSERT(in_definition_form());

            return var_relation{*this};
        }

        bool state::in_definition_form() const {
            static const auto& in_def_form = std::mem_fn(&word_equation::in_definition_form);
            return std::all_of(m_eq_wes.begin(), m_eq_wes.end(), in_def_form);
        }

        bool state::eq_classes_inconsistent() const {
            const auto& unequalable = word_term::unequalable;
            for (const auto& cls : eq_classes()) {
                if (cls.size() == 2) {
                    if (unequalable(cls.at(0), cls.at(1), m_non_empty_var)) return true;
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
                    if (unequalable(selected.at(0), selected.at(1), m_non_empty_var)) return true;
                } while (std::next_permutation(select.begin(), select.end()));
            }
            return false;
        }

        bool state::diseq_inconsistent() const {
            return !m_diseq_wes.empty() && m_diseq_wes.begin()->empty();
        }

        bool state::unsolvable_by_check() const {
            const auto& unsolvable = std::bind(&word_equation::unsolvable, _1, m_non_empty_var);
            return std::any_of(m_eq_wes.begin(), m_eq_wes.end(), unsolvable) ||
                   diseq_inconsistent() || m_memberships->inconsistent();
        }

        bool state::unsolvable_by_inference() const {
            return diseq_inconsistent() || eq_classes_inconsistent() ||
                   m_memberships->inconsistent();
        }

        bool state::quadratic() const {
            for (const auto& v : variables()) {
                std::size_t count = 0;
                for (const auto& we : m_eq_wes) {
                    count += we.count_var(v);
                }
                if (count > 2) return false;
            }
            return true;
        }

        void state::add_word_eq(const word_equation& we) {
            SASSERT(we);

            if (we.empty()) return;
            word_equation&& trimmed = we.trim_prefix();
            if (trimmed.empty()) return;
            m_eq_wes.insert(std::move(trimmed));
            if(m_strategy==transform_strategy::not_allow_empty_var){
                for(auto& v : we.variables()){
                    m_non_empty_var.insert(v);
                }
            }
        }

        void state::add_word_diseq(const word_equation& we) {
            SASSERT(we);

            word_equation&& trimmed = we.trim_prefix();
            //update length bound

            if(we.in_definition_form() && we.definition_body().length()==0 && get_strategy()==state::transform_strategy::dynamic_empty_var_detection){
                m_non_empty_var.insert(we.definition_var());
            }
//            std::cout<<we<<" is in definition form "<<we.in_definition_form()<<" and its length of definition body is "<<we.definition_body().length()<<std::endl;
            if (trimmed.unsolvable(m_non_empty_var)) return;

            m_diseq_wes.insert(std::move(trimmed));


        }


        void str::state::remove_useless_diseq(){
            std::set<word_equation> to_remove;

//            for(auto& v: m_lower_bound){
//                std::cout<<v.first<<"->"<<v.second<<std::endl;
//            }
//

            for(auto & diseq:m_diseq_wes){
                if(diseq.unsolvable(m_non_empty_var)) to_remove.insert(diseq);
            }
            for(auto & rm_diseq:to_remove){
                m_diseq_wes.erase(rm_diseq);
            }

        }

        void state::add_membership(const element& var, expr *re) {
            m_memberships->set(var, re);
        }

        state state::assign_empty(const element& var, const element& non_zero_var) const {
            SASSERT(var.typed(element::t::VAR));

            state result{m_memberships->assign_empty(var)};
            result.set_strategy(m_strategy);
            result.m_non_empty_var=m_non_empty_var;
            result.m_non_empty_var.insert(non_zero_var);
            for (const auto& we : m_eq_wes) {
                result.add_word_eq(we.remove(var));
            }
            for (const auto& we : m_diseq_wes) {
                result.add_word_diseq(we.remove(var));
            }
            return result;
        }

        state state::assign_empty_all(const std::set<element>& vars) const {
            static const auto& is_var = std::bind(&element::typed, _1, element::t::VAR);
            SASSERT(std::all_of(vars.begin(), vars.end(), is_var));

            state result{m_memberships->assign_empty_all(vars)};
            result.set_strategy(m_strategy);
            result.m_non_empty_var=m_non_empty_var;

            for (std::set<element>::iterator it(vars.begin()); it != vars.end(); ++it)
            {
                result.m_non_empty_var.erase(*it);
            }

            for (const auto& we : m_eq_wes) {
                result.add_word_eq(we.remove_all(vars));
            }
            for (const auto& we : m_diseq_wes) {
                result.add_word_diseq(we.remove_all(vars));
            }
            return result;
        }

        state state::assign_const(const element& var, const word_term& tgt) const {
            static const auto& is_const = std::bind(&element::typed, _1, element::t::CONST);
            SASSERT(var.typed(element::t::VAR));
            SASSERT(std::all_of(tgt.content().begin(), tgt.content().end(), is_const));

            state result{m_memberships->assign_const(var, tgt)};
            result.set_strategy(m_strategy);
            result.m_non_empty_var=m_non_empty_var;

            for (const auto& we : m_eq_wes) {
                result.add_word_eq(we.replace(var, tgt));
            }
            for (const auto& we : m_diseq_wes) {
                result.add_word_diseq(we.replace(var, tgt));
            }
            return result;
        }

        state state::assign_as(const element& var, const element& as_var) const {
            SASSERT(var.typed(element::t::VAR) && as_var.typed(element::t::VAR));

            state result{m_memberships->assign_as(var, as_var)};
            result.set_strategy(m_strategy);
            result.m_non_empty_var=m_non_empty_var;
            result.m_non_empty_var.insert(as_var);

            for (const auto& we : m_eq_wes) {
                result.add_word_eq(we.replace(var, {as_var}));
            }
            for (const auto& we : m_diseq_wes) {
                result.add_word_diseq(we.replace(var, {as_var}));
            }
            return result;
        }

        std::list<state> state::assign_prefix(const element& var, const element& ch) const {
            SASSERT(var.typed(element::t::VAR) && ch.typed(element::t::CONST));

            std::list<word_equation> wes;
            for (const auto& we : m_eq_wes) {
                wes.emplace_back(we.replace(var, {ch, var}));
            }
            std::list<word_equation> wines;
            for (const auto& wine : m_diseq_wes) {
                wines.emplace_back(wine.replace(var, {ch, var}));
            }
            std::list<state> result;
            for (auto& m : m_memberships->assign_prefix(var, ch)) {
                state s{std::move(m)};
                s.set_strategy(m_strategy);
                s.m_non_empty_var=m_non_empty_var;

                for (const auto& we : wes) {
                    s.add_word_eq(we);
                }
                for (const auto& wine : wines) {
                    s.add_word_diseq(wine);
                }
                result.emplace_back(std::move(s));
            }
            return result;
        }

        std::list<state> state::assign_prefix_var(const element& var, const element& prefix) const {
            SASSERT(var.typed(element::t::VAR) && prefix.typed(element::t::VAR));

            std::list<word_equation> wes;
            for (const auto& we : m_eq_wes) {
                wes.emplace_back(we.replace(var, {prefix, var}));
            }
            std::list<word_equation> wines;
            for (const auto& wine : m_diseq_wes) {
                wines.emplace_back(wine.replace(var, {prefix, var}));
            }
            std::list<state> result;
            for (auto& m : m_memberships->assign_prefix_var(var, prefix)) {
                state s{std::move(m)};
                s.set_strategy(m_strategy);
                s.m_non_empty_var=m_non_empty_var;

                for (const auto& we : wes) {
                    s.add_word_eq(we);
                }
                for (const auto& wine : wines) {
                    s.add_word_diseq(wine);
                }
                result.emplace_back(std::move(s));
            }
            return result;
        }

        bool state::operator==(const state& other) const {
            return m_strategy == other.m_strategy &&
                   m_eq_wes == other.m_eq_wes ;//&&
                   m_diseq_wes == other.m_diseq_wes &&
                   (theory_str::ignore_membership?
                   true:(*m_memberships == *other.m_memberships));

        }

        std::ostream& operator<<(std::ostream& os, const state& s) {
            std::set<element> vars;


            if (s.m_eq_wes.empty()) {
                os << "(no word equation left)" << std::endl;
            }
            for (const auto& we : s.m_eq_wes) {
                os << we << '\n';
                for(auto& v:we.variables()){
                    vars.insert(v);
                }
            }
            for (const auto& we : s.m_diseq_wes) {
                os << "not (" << we << ")\n";
            }
            os << s.m_memberships<<std::endl;

            return os << std::flush;
        }

        solver::move solver::move::add_record(const element& e) const {
            std::vector<element> r{m_record};
            r.push_back(e);
            return {m_from, m_type, std::move(r)};
        };

        solver::mk_move::mk_move(const state& s, const word_equation& src)
                : m_state{s}, m_src{src} {}

        std::list<solver::action> solver::mk_move::operator()() {



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

        bool solver::mk_move::src_vars_empty() {
            return !(m_state.get_strategy()==state::transform_strategy ::not_allow_empty_var)&& m_src.lhs().empty();
        }

        bool solver::mk_move::src_var_is_const() {
            const word_term& def_body = m_src.definition_body();
            return def_body && !def_body.has_variable();
        }

        solver::action solver::mk_move::prop_empty() {
            const std::set<element> empty_vars{m_src.rhs().variables()};
            const std::vector<element> record{empty_vars.begin(), empty_vars.end()};
            move m{m_state, move::t::TO_EMPTY, record};
            return std::make_pair(std::move(m), m_state.assign_empty_all(empty_vars));
        }

        solver::action solver::mk_move::prop_const() {
            const element& var = m_src.definition_var();
            const word_term& def = m_src.definition_body();
            std::vector<element> record{var};
            record.insert(record.end(), def.content().begin(), def.content().end());
            move m{m_state, move::t::TO_CONST, record};
            return std::make_pair(std::move(m), m_state.assign_const(var, def));
        }

        std::list<solver::action> solver::mk_move::handle_two_var() {
            const element::pair& hh = m_src.heads();
            const element& x = hh.first;
            const element& y = hh.second;
            std::list<action> result;
            for (auto& s : m_state.assign_prefix_var(x, y)) {
                move m{m_state, move::t::TO_VAR_VAR, {x, y}};
                if(m_state.get_strategy()==state::transform_strategy::dynamic_empty_var_detection){
                    s.m_non_empty_var.insert(x);
                    s.m_non_empty_var.insert(y);
                }
                result.emplace_back(std::make_pair(std::move(m), std::move(s)));
            }
            for (auto& s : m_state.assign_prefix_var(y, x)) {
                move m{m_state, move::t::TO_VAR_VAR, {y, x}};
                if(m_state.get_strategy()==state::transform_strategy::dynamic_empty_var_detection){
                    s.m_non_empty_var.insert(x);
                    s.m_non_empty_var.insert(y);
                }
                result.emplace_back(std::make_pair(std::move(m), std::move(s)));
            }
            if (m_state.get_strategy()==state::transform_strategy::allow_empty_var) {
                move mx{m_state, move::t::TO_EMPTY, {x}};
                result.emplace_back(std::make_pair(std::move(mx), m_state.assign_empty(x)));
                move my{m_state, move::t::TO_EMPTY, {y}};
                result.emplace_back(std::make_pair(std::move(my), m_state.assign_empty(y)));
            } else if (m_state.get_strategy()==state::transform_strategy::not_allow_empty_var) {
                move m{m_state, move::t::TO_VAR, {x, y}};
                result.emplace_back(std::make_pair(std::move(m), m_state.assign_as(x, y)));
            }else{
                if(!m_state.is_non_empty_var(x)) {
                    move mx{m_state, move::t::TO_EMPTY, {x}};
                    result.emplace_back(std::make_pair(std::move(mx), m_state.assign_empty(x)));
                }
                if(!m_state.is_non_empty_var(y)) {
                    move my{m_state, move::t::TO_EMPTY, {y}};
                    result.emplace_back(std::make_pair(std::move(my), m_state.assign_empty(y)));
                }
                move m{m_state, move::t::TO_VAR, {x, y}};
                result.emplace_back(std::make_pair(std::move(m), m_state.assign_as(x, y)));
            }
            return result;
        }

        std::list<solver::action> solver::mk_move::handle_one_var() {
            const element::pair& hh = m_src.heads();
            const bool var_const_headed = hh.first.typed(element::t::VAR);
            const element& v = var_const_headed ? hh.first : hh.second;
            const element& c = var_const_headed ? hh.second : hh.first;
            std::list<action> result;
            for (auto&& s : m_state.assign_prefix(v, c)) {
                move m{m_state, move::t::TO_CHAR_VAR, {v, c}};
                result.emplace_back(std::make_pair(std::move(m), std::move(s)));
            }
            if (m_state.get_strategy()==state::transform_strategy::allow_empty_var) {
                move m{m_state, move::t::TO_EMPTY, {v}};
                result.emplace_back(std::make_pair(std::move(m), m_state.assign_empty(v)));
            } else if (m_state.get_strategy()==state::transform_strategy::not_allow_empty_var) {
                move m{m_state, move::t::TO_CONST, {v, c}};
                result.emplace_back(std::make_pair(std::move(m), m_state.assign_const(v, {c})));
            }else{
                if(!m_state.is_non_empty_var(v)) {
                    move m{m_state, move::t::TO_EMPTY, {v}};
                    result.emplace_back(std::make_pair(std::move(m), m_state.assign_empty(v)));
                }
                move m{m_state, move::t::TO_CONST, {v, c}};
                result.emplace_back(std::make_pair(std::move(m), m_state.assign_const(v, {c})));

            }
            return result;
        }

        bool solver::record_graph::contains(const state& s) const {
//            STRACE("str", tout<<"[check contains]\n"<<s<<std::endl;);
//
//
//            for(auto& c : m_backward_def){
//                STRACE("str", tout<<"[state]\n"<<c.first<<std::endl;);
//            }
            return m_backward_def.find(s) != m_backward_def.end();
        }

        const std::list<solver::move>&
        solver::record_graph::incoming_moves(const state& s) const {
            SASSERT(contains(s));
            return m_backward_def.find(s)->second;
        }

        void solver::record_graph::add_move(move&& m, const state& s) {
            SASSERT(contains(m.m_from));
            SASSERT(contains(s));
            m_backward_def[s].push_back(std::move(m));
        }

        const state& solver::record_graph::add_state(state&& s) {
            SASSERT(!contains(s));
            auto&& pair = std::make_pair(std::move(s), std::list<move>{});
            return m_backward_def.emplace(std::move(pair)).first->first;
        }

        solver::solver(state&& root, automaton_factory::sptr af)
                : m_rec_root{m_records.add_state(std::move(root))}, m_aut_maker{std::move(af)} {
            m_pending.push(m_rec_root);
        }

        bool solver::should_explore_all() const {
            return true;
        }

        result solver::check() {
            if (in_status(result::SAT)) return m_status;
            SASSERT(m_pending.size() == 1);
            if (!check_linear_membership(m_pending.top())) return m_status = result::UNSAT;
            STRACE("str", tout << "[Check SAT]\n";);
            while (!m_pending.empty()) {
                const state& curr_s = m_pending.top();
                m_pending.pop();


                STRACE("str", tout << "from:\n" << curr_s << '\n';);
                for (auto& action : transform(curr_s)) {
                    if (m_records.contains(action.second)) {
                        m_records.add_move(std::move(action.first), action.second);
                        STRACE("str", tout << "already visited:\n" << action.second << '\n';);
                        continue;
                    }
                    const state& s = m_records.add_state(std::move(action.second));
                    m_records.add_move(std::move(action.first), s);
                    if (s.unsolvable_by_inference()) {
                        STRACE("str", tout << "failed:\n" << s << '\n';);
                        continue;
                    }

                    if (s.in_definition_form()) {
                        var_relation&& var_rel = s.var_rel_graph();
                        if (var_rel.is_straight_line() &&
                            check_straight_line_membership(var_rel, s.get_memberships())) {
                            if (finish_after_found(s)) return m_status;
                            continue;
                        }
                    }


//                    const word_equation& only_one_left = s.only_one_eq_left();
//                    if (only_one_left && only_one_left.in_definition_form()) {
//                        // solved form check failed, the we in definition form must be recursive
//                        const word_equation& last_we_recursive_def = only_one_left;
//                        if (!last_we_recursive_def.definition_body().has_constant()) {
//                            if (finish_after_found(s)) return m_status;
//                            continue;
//                        }
//                        STRACE("str", tout << "failed:\n" << s << '\n';);
//                        continue;
//                    }
                    STRACE("str", tout << "to:\n" << s << '\n';);

                    if(s.word_eq_num() != 0)
                        m_pending.push(s);
                }

            }

            return m_status = m_rec_success_leaves.empty() ? result::UNSAT : result::SAT;
        }
        string element::abbreviation_to_fullname(){
            string ret;
            for(auto& var:element::variables){
                ret+=var.shortname();
                ret+=" <=> ";
                ret+=var.m_value.encode();
                ret+="\n";
            }
            return ret;

        }

        automaton::sptr
        solver::derive_var_membership(const var_relation& g, memberships::sptr m,
                                      const element& var) {
            SASSERT(g.is_valid());

            const auto& def_table = g.definition_table();
            const auto fit = def_table.find(var);
            if (fit == def_table.end()) {
                return m_aut_maker->mk_universe();
            }
            const auto& def = fit->second;
            std::list<automaton::sptr> as;
            zstring str;
            for (const auto& e : def.content()) {
                if (e.typed(element::t::VAR)) {
                    if (!str.empty()) {
                        as.emplace_back(m_aut_maker->mk_from_word(str));
                        str = zstring{};
                    }
                    as.emplace_back(derive_var_membership(g, m, e));
                    continue;
                } else if (e.typed(element::t::CONST)) {
                    str = str + e.value();
                    continue;
                }
            }
            if (!str.empty()) {
                as.emplace_back(m_aut_maker->mk_from_word(str));
            }
            static const auto concat = [](automaton::sptr a1, automaton::sptr a2) {
                return a1->append(a2);
            };
            return std::accumulate(as.begin(), as.end(), m_aut_maker->mk_from_word({}), concat);
        }

        bool solver::check_straight_line_membership(const var_relation& g, memberships::sptr m) {
            SASSERT(g.is_valid());
            if (m->empty()) return true;

            for (const auto& h : g.heads()) {
                automaton::sptr lhs = m->get(h);
                automaton::sptr rhs = derive_var_membership(g, m, h);
                if(!lhs) {
                    if(rhs->is_empty()) return false;
                    else continue;
                }
                if (lhs->intersect_with(rhs)->is_empty()) return false;

            }
            return true;
        }

        automaton::sptr solver::concat_simple_membership(memberships::sptr m, const word_term& w) {
            std::list<automaton::sptr> as;
            zstring str;
            for (const auto& e : w.content()) {
                if (e.typed(element::t::VAR)) {
                    if (!str.empty()) {
                        as.emplace_back(m_aut_maker->mk_from_word(str));
                        str = zstring{};
                    }
                    automaton::sptr a = m->get(e);
                    as.emplace_back(a ? a : m_aut_maker->mk_universe());
                    continue;
                } else if (e.typed(element::t::CONST)) {
                    str = str + e.value();
                    continue;
                }
            }
            if (!str.empty()) {
                as.emplace_back(m_aut_maker->mk_from_word(str));
            }
            static const auto concat = [](automaton::sptr a1, automaton::sptr a2) {
                return a1->append(a2);
            };
            return std::accumulate(as.begin(), as.end(), m_aut_maker->mk_from_word({}), concat);
        }

        bool solver::check_linear_membership(const state& s) {
            if (s.get_memberships()->empty()) {
                return true;
            }
            for (const auto& we : s.word_eqs()) {
                automaton::sptr lhs = concat_simple_membership(s.get_memberships(), we.lhs());
                automaton::sptr rhs = concat_simple_membership(s.get_memberships(), we.rhs());
                if (lhs->intersect_with(rhs)->is_empty()) return false;
            }
            return true;
        }

        bool solver::finish_after_found(const state& s) {
            STRACE("str", tout << "[Success Leaf]\n" << s << '\n';);
            m_rec_success_leaves.emplace_back(s);
            if (!should_explore_all()) {
                m_status = result::SAT;
                return true;
            }
            return false;
        }


        std::list<solver::action> solver::transform(const state& s) const {
            SASSERT(!s.unsolvable_by_check() && s.word_eq_num() != 0);
            // no diseq-only handling for now
            return mk_move{s, s.smallest_eq()}();
        }

    }

    namespace {
        bool IN_CHECK_FINAL = false;
    }

    theory_str::theory_str(ast_manager& m, const theory_str_params& params)
            : theory{m.mk_family_id("seq")}, m_params{params}, m_rewrite{m}, m_util_a{m},
              m_util_s{m}, search_started{false},m_scope_level{0},m_trail{m},m_delayed_axiom_setup_terms{m},
              m_delayed_assertions_todo{m},m_persisted_axiom_todo{m},contains_map{m},string_int_conversion_terms{m},
              m_fresh_id(0),m_trail_stack{*this},m_find{*this}{}

    void theory_str::display(std::ostream& os) const {
        os << "theory_str display" << std::endl;
    }

    void theory_str::init(context *ctx) {
        theory::init(ctx);
        STRACE("str", if (!IN_CHECK_FINAL) tout << "init\n";);
    }

    void theory_str::add_theory_assumptions(expr_ref_vector& assumptions) {
        STRACE("str", if (!IN_CHECK_FINAL) tout << "add_theory_assumptions\n";);
    }

    theory_var theory_str::mk_var(enode *const n) {
        STRACE("str", tout << "mk_var: " << mk_pp(n->get_owner(), get_manager()) << '\n';);
        if (!is_string_sort(n->get_owner()) && !is_regex_sort(n->get_owner())) {
            return null_theory_var;
        }
        if (is_attached_to_var(n)) {
            const theory_var v = n->get_th_var(get_id());
            STRACE("str", tout << "already attached to theory_var #" << v << '\n';);
            return v;
        }

        context& ctx = get_context();
        const theory_var v = theory::mk_var(n);
        ctx.attach_th_var(n, this, v);
        ctx.mark_as_relevant(n);
        STRACE("str", tout << "new theory_var #" << v << '\n';);
        return v;
    }
    app * theory_str::mk_contains(expr * haystack, expr * needle) {
        app * contains = m_util_s.str.mk_contains(haystack, needle); // TODO double-check semantics/argument order
        m_trail.push_back(contains);
        // immediately force internalization so that axiom setup does not fail
        get_context().internalize(contains, false);
        set_up_axioms(contains);
        return contains;
    }

    // note, this invokes "special-case" handling for the start index being 0
    app * theory_str::mk_indexof(expr * haystack, expr * needle) {
        app * indexof = m_util_s.str.mk_index(haystack, needle, mk_int(0));
        m_trail.push_back(indexof);
        // immediately force internalization so that axiom setup does not fail
        get_context().internalize(indexof, false);
        set_up_axioms(indexof);
        return indexof;
    }
    bool theory_str::internalize_atom(app *const atom, const bool gate_ctx) {
        (void) gate_ctx;
        STRACE("str", tout << "internalize_atom: gate_ctx is " << gate_ctx << ", "
                           << mk_pp(atom, get_manager()) << '\n';);
        context& ctx = get_context();
        if (ctx.b_internalized(atom)) {
            STRACE("str", tout << "done before\n";);
            return true;
        }
        return internalize_term(atom);
    }

    bool theory_str::internalize_term(app *const term) {
        ast_manager& m = get_manager();
        context& ctx = get_context();
        SASSERT(is_of_this_theory(term));
        if (ctx.e_internalized(term)) {
            enode *e = ctx.get_enode(term);
            mk_var(e);
            return true;
        }
        for (auto e : *term) {
            if (!ctx.e_internalized(e)) {
                ctx.internalize(e, false);
            }
            enode *n = ctx.get_enode(e);
            ctx.mark_as_relevant(n);
            mk_var(n);
        }
        if (m.is_bool(term)) {
            bool_var bv = ctx.mk_bool_var(term);
            ctx.set_var_theory(bv, get_id());
            ctx.mark_as_relevant(bv);
        }

        enode *e = nullptr;
        if (ctx.e_internalized(term)) {
            e = ctx.get_enode(term);
        } else {
            e = ctx.mk_enode(term, false, m.is_bool(term), true);
        }
        mk_var(e);
        return true;
    }


    void theory_str::init_search_eh() {
        context & ctx = get_context();
        TRACE("str",
              tout << __FUNCTION__ << ": dumping all asserted formulas:" << std::endl;
                      unsigned nFormulas = ctx.get_num_asserted_formulas();
                      for (unsigned i = 0; i < nFormulas; ++i) {
                          expr *ex = ctx.get_asserted_formula(i);
                          tout << mk_pp(ex, get_manager()) << (ctx.is_relevant(ex) ? " (rel)" : " (NOT REL)")
                               << std::endl;
                      }
        );
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
    void theory_str::set_up_axioms(expr * ex) {
        ast_manager &m = get_manager();
        context &ctx = get_context();

        sort *ex_sort = m.get_sort(ex);
        sort *str_sort = m_util_s.str.mk_string_sort();
        sort *bool_sort = m.mk_bool_sort();

        family_id m_arith_fid = m.mk_family_id("arith");
        sort *int_sort = m.mk_sort(m_arith_fid, INT_SORT);
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": " << mk_pp(ex, m) << std::endl;);

        if (ex_sort == str_sort) {
            STRACE("str", tout << __FUNCTION__ << ": " << mk_ismt2_pp(ex, get_manager()) <<
                               ": expr is of sort String" << std::endl;);
            // set up basic string axioms
            enode *n = ctx.get_enode(ex);
            SASSERT(n);
            m_basicstr_axiom_todo.push_back(n);
            STRACE("str", tout << "add " << mk_pp(ex, m) << " to m_basicstr_axiom_todo" << std::endl;);


            if (is_app(ex)) {
                app *ap = to_app(ex);
                if (m_util_s.str.is_concat(ap)) {
                    // if ex is a concat, set up concat axioms later
                    m_concat_axiom_todo.push_back(n);

                } else if (m_util_s.str.is_length(ap)) {
                    // if the argument is a variable,
                    // keep track of this for later, we'll need it during model gen
                    expr *var = ap->get_arg(0);
                    app *aVar = to_app(var);
                    if (aVar->get_num_args() == 0 && !m_util_s.str.is_string(aVar)) {
                        input_var_in_len.insert(var);
                    }
                } else if (m_util_s.str.is_at(ap) || m_util_s.str.is_extract(ap) || m_util_s.str.is_replace(ap)) {
                    m_library_aware_axiom_todo.push_back(n);
                } else if (m_util_s.str.is_itos(ap)) {
                    TRACE("str",
                          tout << "found string-integer conversion term: " << mk_pp(ex, get_manager()) << std::endl;);
                    string_int_conversion_terms.push_back(ap);
                    m_library_aware_axiom_todo.push_back(n);
                } else if (ap->get_num_args() == 0 && !m_util_s.str.is_string(ap)) {
                    // if ex is a variable, add it to our list of variables
                    STRACE("str", tout << "tracking variable " << mk_ismt2_pp(ap, get_manager()) << std::endl;);
                    variable_set.insert(ex);
                    ctx.mark_as_relevant(ex);
                    // this might help??
                    theory_var v = mk_var(n);
                    STRACE("str", tout << "variable " << mk_ismt2_pp(ap, get_manager()) << " is #" << v << std::endl;);
                    (void) v;
                }
            }
        } else if (ex_sort == bool_sort && !is_quantifier(ex)) {
            STRACE("str", tout << __FUNCTION__ <<  ": " << mk_ismt2_pp(ex, get_manager()) <<
                               ": expr is of sort Bool" << std::endl;);
            // set up axioms for boolean terms

            ensure_enode(ex);
            if (ctx.e_internalized(ex)) {
                enode *n = ctx.get_enode(ex);
                SASSERT(n);

                if (is_app(ex)) {
                    app *ap = to_app(ex);
                    if (m_util_s.str.is_prefix(ap) || m_util_s.str.is_suffix(ap) || m_util_s.str.is_contains(ap) || m_util_s.str.is_in_re(ap)) {
                        m_library_aware_axiom_todo.push_back(n);
                    }
                }
            } else {
                STRACE("str", tout << "WARNING: Bool term " << mk_ismt2_pp(ex, get_manager())
                                   << " not internalized. Delaying axiom setup to prevent a crash." << std::endl;);
                ENSURE(!search_started); // infinite loop prevention
                m_delayed_axiom_setup_terms.push_back(ex);
                return;
            }
        } else if (ex_sort == int_sort) {
            STRACE("str", tout << __FUNCTION__ <<  ": " << mk_ismt2_pp(ex, get_manager()) <<
                               ": expr is of sort Int" << std::endl;);
            // set up axioms for integer terms
            enode *n = ensure_enode(ex);
            SASSERT(n);

            if (is_app(ex)) {
                app *ap = to_app(ex);
                if (m_util_s.str.is_index(ap)) {
                    m_library_aware_axiom_todo.push_back(n);
                } else if (m_util_s.str.is_stoi(ap)) {
                    STRACE("str",
                           tout << "found string-integer conversion term: " << mk_pp(ex, get_manager()) << std::endl;);
                    string_int_conversion_terms.push_back(ap);
                    m_library_aware_axiom_todo.push_back(n);
                }
            }
        }
        else if (is_app(ex)){
            app *ap = to_app(ex);
            if (m_util_s.re.is_star(ap)
                || m_util_s.re.is_plus(ap)
                || m_util_s.re.is_concat(ap)
                || m_util_s.re.is_union(ap)
                || m_util_s.re.is_complement(ap)
                || m_util_s.re.is_empty(ap)
                || m_util_s.re.is_full_char(ap)
                || m_util_s.re.is_intersection(ap)
                || m_util_s.re.is_range(ap)
                || m_util_s.re.is_to_re(ap)) {
            }
            else {
                STRACE("str", tout << __FUNCTION__ <<  ": " << mk_ismt2_pp(ex, get_manager()) <<
                                   ": expr is of wrong sort, ignoring" << std::endl;);
            }
        }
        else {
            STRACE("str", tout << __FUNCTION__ <<  ": " << mk_ismt2_pp(ex, get_manager()) <<
                               ": expr is of wrong sort, ignoring" << std::endl;);
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
    void theory_str::relevant_eh(app *const n) {
        STRACE("str", tout << "relevant: " << mk_pp(n, get_manager()) << '\n';);
    }
    void theory_str::assign_eh(bool_var v, const bool is_true) {
        ast_manager& m = get_manager();
        STRACE("str", tout << "assign: bool_var #" << v << " is " << is_true << ", "
                           << mk_pp(get_context().bool_var2expr(v), m) << '\n';);
        context &ctx = get_context();
        expr *e = ctx.bool_var2expr(v);
        if(!axiomatized_terms.contains(e)) {
            axiomatized_terms.insert(e);
            if (is_true) {
                m_block_todo.push_back({m.mk_not(e),m});
            } else {
                m_block_todo.push_back({e,m});
            }
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


    void theory_str::new_eq_eh(theory_var x, theory_var y) {
        ast_manager& m = get_manager();
        const expr_ref l{get_enode(x)->get_owner(), m};
        const expr_ref r{get_enode(y)->get_owner(), m};
        zstring s;

        expr_ref l_eq_r = {m.mk_eq(l, r),m};
        expr_ref l_not_eq_r = {m.mk_not(l_eq_r),m};
        if(!axiomatized_terms.contains(l_not_eq_r)){
            axiomatized_terms.insert(l_not_eq_r);
            m_block_todo.push_back(l_not_eq_r);
            if (m_util_s.str.is_string(l, s) && !m_util_s.str.is_concat(r)) {
                expr *re = m_util_s.re.mk_to_re(l);
                if (s.length() != 0) {
                    std::stringstream ss;
                    ss << mk_pp(r, m);
                    m_non_empty_var.push_back({str::element::t::VAR, ss.str().data(), r});
                }
                m_membership_todo.push_back({{r,  m},
                                             {re, m}});
            } else if (m_util_s.str.is_string(r, s) && !m_util_s.str.is_concat(l)) {
                expr *re = m_util_s.re.mk_to_re(r);
                if (s.length() != 0) {
                    std::stringstream ss;
                    ss << mk_pp(l, m);
                    m_non_empty_var.push_back({str::element::t::VAR, ss.str().data(), l});
                }
                m_membership_todo.push_back({{l,  m},
                                             {re, m}});
            } else {
                m_word_eq_todo.push_back({l, r});
            }
            STRACE("str", tout << "new_eq: " << l << " = " << r << '\n';);
        }
    }


    void theory_str::new_diseq_eh(theory_var x, theory_var y) {
        ast_manager& m = get_manager();
        const expr_ref l{get_enode(x)->get_owner(), m};
        const expr_ref r{get_enode(y)->get_owner(), m};
        expr_ref l_eq_r = {m.mk_eq(l, r),m};

        if(!axiomatized_terms.contains(l_eq_r)) {
            axiomatized_terms.insert(l_eq_r);
            m_block_todo.push_back(l_eq_r);

            zstring s;
            if (m_util_s.str.is_string(l, s) && !m_util_s.str.is_concat(r)) {
                expr *re = m_util_s.re.mk_complement(m_util_s.re.mk_to_re(l));
                if (s.length() == 0) {
                    std::stringstream ss;
                    ss << mk_pp(r, m);
                    m_non_empty_var.push_back({str::element::t::VAR, ss.str().data(), r});
                }
                m_membership_todo.push_back({{r,  m},
                                             {re, m}});
            } else if (m_util_s.str.is_string(r, s) && !m_util_s.str.is_concat(l)) {
                expr *re = m_util_s.re.mk_complement(m_util_s.re.mk_to_re(r));
                if (s.length() == 0) {
                    std::stringstream ss;
                    ss << mk_pp(l, m);
                    m_non_empty_var.push_back({str::element::t::VAR, ss.str().data(), l});
                }
                m_membership_todo.push_back({{l,  m},
                                             {re, m}});
            } else {
                m_word_diseq_todo.push_back({l, r});
            }

//        //add lower bound from solvers
//
//        context& ctx = get_context();
//        expr_ref el(m_util_s.str.mk_length(l), m);
//        expr_ref er(m_util_s.str.mk_length(r), m);
//        expr_ref _lo(m);
//        family_id afid = m_util_a.get_family_id();
//        for(const expr_ref& e :{el,er}) {
//            theory_mi_arith* tha = get_th_arith<theory_mi_arith>(ctx, afid, e);
//            if (tha && tha->get_lower(ctx.get_enode(e), _lo)) { std::cout << "low of "<< mk_pp(e,m) <<" = " << _lo<<std::endl;}
//            theory_i_arith* thi = get_th_arith<theory_i_arith>(ctx, afid, e);
//            if (thi && thi->get_lower(ctx.get_enode(e), _lo)) { std::cout << "low of "<< mk_pp(e,m) <<" = " << _lo<<std::endl;}
//            theory_lra* thr = get_th_arith<theory_lra>(ctx, afid, e);
//            if (thr && thr->get_lower(ctx.get_enode(e), _lo)) { std::cout << "low of "<< mk_pp(e,m) <<" = " << _lo<<std::endl;}
//        }
//
            STRACE("str", tout << "new_diseq: " << l << " != " << r << '\n';);
        }
    }

    bool theory_str::can_propagate() {
        return !m_basicstr_axiom_todo.empty() || !m_str_eq_todo.empty()
               || !m_concat_axiom_todo.empty()
               || !m_library_aware_axiom_todo.empty()
               || !m_delayed_axiom_setup_terms.empty()
               || !m_persisted_axiom_todo.empty()
               || (search_started && !m_delayed_assertions_todo.empty())
                ;
    }

    void theory_str::propagate() {
        context & ctx = get_context();
        while (can_propagate()) {
            TRACE("str", tout << std::endl;);

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

            for (auto const& el : m_concat_axiom_todo) {
                instantiate_concat_axiom(el);
            }
            m_concat_axiom_todo.reset();

            while(true) {
                // Special handling: terms can recursively set up other terms
                // (e.g. indexof can instantiate other indexof terms).
                // - Copy the list so it can potentially be modified during setup.
                // - Don't clear this list if new ones are added in the process;
                //   instead, set up all the new terms before proceeding.
                // TODO see if any other propagate() worklists need this kind of handling
                // TODO we really only need to check the new ones on each pass
                unsigned start_count = m_library_aware_axiom_todo.size();
                ptr_vector<enode> axioms_tmp(m_library_aware_axiom_todo);
                for (auto const& e : axioms_tmp) {
                    app * a = e->get_owner();
                    if (m_util_s.str.is_stoi(a)) {
                    } else if (m_util_s.str.is_itos(a)) {
                    } else if (m_util_s.str.is_at(a)) {
                        instantiate_axiom_charAt(e);
                    } else if (m_util_s.str.is_prefix(a)) {
                        instantiate_axiom_prefixof(e);
                    } else if (m_util_s.str.is_suffix(a)) {
                        instantiate_axiom_suffixof(e);
                    } else if (m_util_s.str.is_contains(a)) {
                        instantiate_axiom_contains(e);
                    } else if (m_util_s.str.is_index(a)) {
                        instantiate_axiom_indexof(e);
                    } else if (m_util_s.str.is_extract(a)) {
                        instantiate_axiom_substr(e);
                    } else if (m_util_s.str.is_replace(a)) {
                        instantiate_axiom_replace(e);
                    } else if (m_util_s.str.is_in_re(a)) {
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
            sort * str_sort = m_util_s.str.mk_string_sort();
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

        if (m_util_s.str.is_string(a_str)) {
            expr_ref len_str(m);
            len_str = mk_strlen(a_str);
            SASSERT(len_str);

            zstring strconst;
            m_util_s.str.is_string(str->get_owner(), strconst);
            STRACE("str", tout <<  __FUNCTION__ << ":\"" << strconst.encode().c_str() << "\"" << std::endl;);
            unsigned int l = strconst.length();
            expr_ref len(m_util_a.mk_numeral(rational(l), true), m);

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
                zero = m_util_a.mk_numeral(rational(0), true);
                SASSERT(zero);
                // build LHS >= RHS and assert
                app * lhs_ge_rhs = m_util_a.mk_ge(len_str, zero);
                SASSERT(lhs_ge_rhs);
                STRACE("str", tout << "string axiom 1: " << mk_ismt2_pp(lhs_ge_rhs, m) << std::endl;);
                assert_axiom(lhs_ge_rhs);
            }

            // build axiom 2: Length(a_str) == 0 <=> a_str == ""
            {
                // build LHS of iff
                expr_ref len_str(m);
                len_str = mk_strlen(a_str);
                SASSERT(len_str);
                expr_ref zero(m);
                zero = m_util_a.mk_numeral(rational(0), true);
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
        SASSERT(m_util_s.str.is_concat(a_cat));

        ast_manager & m = get_manager();

        TRACE("str", tout << __FUNCTION__ << ":" << mk_ismt2_pp(a_cat, m) << std::endl;);

        // build LHS
        expr_ref len_xy(m);
        len_xy = mk_strlen(a_cat);
        SASSERT(len_xy);

        // build RHS: start by extracting x and y from Concat(x, y)
        SASSERT(a_cat->get_num_args() == 2);
        app * a_x = to_app(a_cat->get_arg(0));
        app * a_y = to_app(a_cat->get_arg(1));
        concat_astNode_map.insert(a_x, a_y, a_cat);
        expr_ref len_x(m);
        len_x = mk_strlen(a_x);
        SASSERT(len_x);

        expr_ref len_y(m);
        len_y = mk_strlen(a_y);
        SASSERT(len_y);

        // now build len_x + len_y
        expr_ref len_x_plus_len_y(m);
        len_x_plus_len_y = m_util_a.mk_add(len_x, len_y);
        SASSERT(len_x_plus_len_y);

        // finally assert equality between the two subexpressions
        app * eq = m.mk_eq(len_xy, len_x_plus_len_y);
        SASSERT(eq);
        assert_axiom(eq);
    }

    void theory_str::instantiate_axiom_prefixof(enode * e) {
        context & ctx = get_context();
        ast_manager & m = get_manager();

        app * expr = e->get_owner();
        if (axiomatized_terms.contains(expr)) {
            TRACE("str", tout << "already set up prefixof axiom for " << mk_pp(expr, m) << std::endl;);
            return;
        }
        axiomatized_terms.insert(expr);

        TRACE("str", tout << "instantiate prefixof axiom for " << mk_pp(expr, m) << std::endl;);

        expr_ref ts0(mk_str_var("pre_prefix"), m);
        expr_ref ts1(mk_str_var("post_prefix"), m);

        expr_ref_vector innerItems(m);
        innerItems.push_back(ctx.mk_eq_atom(expr->get_arg(1), mk_concat(ts0, ts1)));
        innerItems.push_back(ctx.mk_eq_atom(mk_strlen(ts0), mk_strlen(expr->get_arg(0))));
        innerItems.push_back(m.mk_ite(ctx.mk_eq_atom(ts0, expr->get_arg(0)), expr, mk_not(m, expr)));
        expr_ref then1(m.mk_and(innerItems.size(), innerItems.c_ptr()), m);
        SASSERT(then1);

        // the top-level condition is Length(arg0) >= Length(arg1)
        expr_ref topLevelCond(
                m_util_a.mk_ge(
                        m_util_a.mk_add(
                                mk_strlen(expr->get_arg(1)), m_util_a.mk_mul(mk_int(-1), mk_strlen(expr->get_arg(0)))),
                        mk_int(0))
                , m);
        SASSERT(topLevelCond);

        expr_ref finalAxiom(m.mk_ite(topLevelCond, then1, mk_not(m, expr)), m);
        SASSERT(finalAxiom);
        assert_axiom(finalAxiom);
    }

    void theory_str::instantiate_axiom_suffixof(enode * e) {
        context & ctx = get_context();
        ast_manager & m = get_manager();

        app * expr = e->get_owner();
        if (axiomatized_terms.contains(expr)) {
            TRACE("str", tout << "already set up suffixof axiom for " << mk_pp(expr, m) << std::endl;);
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
        SASSERT(then1);

        // the top-level condition is Length(arg0) >= Length(arg1)
        expr_ref topLevelCond(
                m_util_a.mk_ge(
                        m_util_a.mk_add(
                                mk_strlen(expr->get_arg(1)), m_util_a.mk_mul(mk_int(-1), mk_strlen(expr->get_arg(0)))),
                        mk_int(0))
                , m);
        SASSERT(topLevelCond);

        expr_ref finalAxiom(m.mk_ite(topLevelCond, then1, mk_not(m, expr)), m);
        SASSERT(finalAxiom);
        assert_axiom(finalAxiom);
    }

    void theory_str::instantiate_axiom_contains(enode * e) {
        context & ctx = get_context();
        ast_manager & m = get_manager();

        app * ex = e->get_owner();
        if (axiomatized_terms.contains(ex)) {
            TRACE("str", tout << "already set up Contains axiom for " << mk_pp(ex, m) << std::endl;);
            return;
        }
        axiomatized_terms.insert(ex);

        // quick path, because this is necessary due to rewriter behaviour
        // at minimum it should fix z3str/concat-006.smt2
        zstring haystackStr, needleStr;
        if (m_util_s.str.is_string(ex->get_arg(0), haystackStr) && m_util_s.str.is_string(ex->get_arg(1), needleStr)) {
            TRACE("str", tout << "eval constant Contains term " << mk_pp(ex, m) << std::endl;);
            if (haystackStr.contains(needleStr)) {
                assert_axiom(ex);
            } else {
                assert_axiom(mk_not(m, ex));
            }
            return;
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

        TRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": " << mk_pp(ex, m) << std::endl;);

        std::pair<app*, app*> value = std::make_pair<app*, app*>(mk_str_var("pre_contain"), mk_str_var("post_contain"));
        expr_ref haystack(ex->get_arg(0), m), needle(ex->get_arg(1), m);
        app* a = m_util_s.str.mk_contains(haystack, needle);
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

        expr_ref breakdownAssert(ctx.mk_eq_atom(ex, ctx.mk_eq_atom(ex->get_arg(0), mk_concat(ts0, mk_concat(ex->get_arg(1), ts1)))), m);
        SASSERT(breakdownAssert);
        assert_axiom(breakdownAssert);
    }

    void theory_str::instantiate_axiom_charAt(enode * e) {
        context &ctx = get_context();
        ast_manager &m = get_manager();
        expr *arg0, *arg1;
        app *expr = e->get_owner();
        if (axiomatized_terms.contains(expr)) {
            TRACE("str", tout << "already set up CharAt axiom for " << mk_pp(expr, m) << std::endl;);
            return;
        }
        axiomatized_terms.insert(expr);
        VERIFY(m_util_s.str.is_at(expr, arg0, arg1));

        TRACE("str", tout << __FUNCTION__ << ":" << mk_pp(expr, m) << std::endl;);

        expr_ref ts0(mk_str_var("ts0"), m);
        expr_ref ts1(mk_str_var("ts1"), m);
        expr_ref ts2(mk_str_var("ts2"), m);

        expr_ref cond(m.mk_and(
                m_util_a.mk_ge(arg1, mk_int(0)),
                m_util_a.mk_lt(arg1, mk_strlen(arg0))), m);

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

    void theory_str::instantiate_axiom_indexof(enode * e) {
        context & ctx = get_context();
        ast_manager & m = get_manager();

        app * ex = e->get_owner();
        if (axiomatized_terms.contains(ex)) {
            TRACE("str", tout << "already set up str.indexof axiom for " << mk_pp(ex, m) << std::endl;);
            return;
        }
        SASSERT(ex->get_num_args() == 3);
        // if the third argument is exactly the integer 0, we can use this "simple" indexof;
        // otherwise, we call the "extended" version
        expr * startingPosition = ex->get_arg(2);
        rational startingInteger;
        if (!m_util_a.is_numeral(startingPosition, startingInteger) || !startingInteger.is_zero()) {
            // "extended" indexof term with prefix
            instantiate_axiom_indexof_extended(e);
            return;
        }
        axiomatized_terms.insert(ex);

        TRACE("str", tout << __FUNCTION__ << ":" << mk_pp(ex, m) << std::endl;);
        std::pair<app*, app*> value = std::make_pair<app*, app*>(mk_str_var("x1"), mk_str_var("x2"));
        expr_ref haystack(ex->get_arg(0), m), needle(ex->get_arg(1), m);
        app* a = m_util_s.str.mk_contains(haystack, needle);
        enode* key = ensure_enode(a);
        if (contain_split_map.contains(key)) {
            std::pair<enode *, enode *> tmpvalue = contain_split_map[key];
            value = std::make_pair<app *, app *>(tmpvalue.first->get_owner(), tmpvalue.second->get_owner());
        }
        else {
            contain_split_map.insert(key, std::make_pair(ctx.get_enode(value.first), ctx.get_enode(value.second)));
        }

        expr_ref x1(value.first, m);
        expr_ref x2(value.second, m);
        expr_ref indexAst(mk_int_var("index"), m);

        expr_ref condAst(mk_contains(ex->get_arg(0), ex->get_arg(1)), m);
        SASSERT(condAst);

        // -----------------------
        // true branch
        expr_ref_vector thenItems(m);
        //  args[0] = x1 . args[1] . x2
        thenItems.push_back(ctx.mk_eq_atom(ex->get_arg(0), mk_concat(x1, mk_concat(ex->get_arg(1), x2))));
        //  indexAst = |x1|
        thenItems.push_back(ctx.mk_eq_atom(indexAst, mk_strlen(x1)));

        bool simpleCase = false;
        zstring needleStr;
        if (m_util_s.str.is_string(ex->get_arg(1), needleStr)) {
            if (needleStr.length() == 1) {
                simpleCase = true;
            }
        }

        if (simpleCase){
            thenItems.push_back(mk_not(m, mk_contains(x1, ex->get_arg(1))));
        }
        else {
            //     args[0]  = x3 . x4
            //  /\ |x3| = |x1| + |args[1]| - 1
            //  /\ ! contains(x3, args[1])
            expr_ref x3(mk_str_var("x3"), m);
            expr_ref x4(mk_str_var("x4"), m);
            expr_ref tmpLen(m_util_a.mk_add(indexAst, mk_strlen(ex->get_arg(1)), mk_int(-1)), m);
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
            expr_ref premise(m_util_s.str.mk_contains(haystack, needle), m);
            ctx.internalize(premise, false);
            expr_ref conclusion(m_util_a.mk_ge(ex, zeroAst), m);
            expr_ref containsAxiom(ctx.mk_eq_atom(premise, conclusion), m);
            SASSERT(containsAxiom);

            // we can't assert this during init_search as it breaks an invariant if the instance becomes inconsistent
            m_delayed_axiom_setup_terms.push_back(containsAxiom);
        }
    }

    void theory_str::instantiate_axiom_indexof_extended(enode * _e) {
        context & ctx = get_context();
        ast_manager & m = get_manager();

        app * e = _e->get_owner();
        if (axiomatized_terms.contains(e)) {
            TRACE("str", tout << "already set up extended str.indexof axiom for " << mk_pp(e, m) << std::endl;);
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

        expr * H = nullptr; // "haystack"
        expr * N = nullptr; // "needle"
        expr * i = nullptr; // start index
        m_util_s.str.is_index(e, H, N, i);

        expr_ref minus_one(m_util_a.mk_numeral(rational::minus_one(), true), m);
        expr_ref zero(m_util_a.mk_numeral(rational::zero(), true), m);

        // case split

        // case 1: i < 0
        {
            expr_ref premise(m_util_a.mk_le(i, minus_one), m);
            expr_ref conclusion(ctx.mk_eq_atom(e, minus_one), m);
            assert_implication(premise, conclusion);
        }

        // case 2: i = 0
        {
            expr_ref premise(ctx.mk_eq_atom(i, zero), m);
            // reduction to simpler case
            expr_ref conclusion(ctx.mk_eq_atom(e, mk_indexof(H, N)), m);
            assert_implication(premise, conclusion);
        }

        // case 3: i >= len(H)
        {
            //expr_ref _premise(m_util_a.mk_ge(i, mk_strlen(H)), m);
            //expr_ref premise(_premise);
            //th_rewriter rw(m);
            //rw(premise);
            expr_ref premise(m_util_a.mk_ge(m_util_a.mk_add(i, m_util_a.mk_mul(minus_one, mk_strlen(H))), zero), m);
            expr_ref conclusion(ctx.mk_eq_atom(e, minus_one), m);
            assert_implication(premise, conclusion);
        }

        // case 4: 0 < i < len(H)
        {
            expr_ref premise1(m_util_a.mk_gt(i, zero), m);
            //expr_ref premise2(m_util_a.mk_lt(i, mk_strlen(H)), m);
            expr_ref premise2(m.mk_not(m_util_a.mk_ge(m_util_a.mk_add(i, m_util_a.mk_mul(minus_one, mk_strlen(H))), zero)), m);
            expr_ref _premise(m.mk_and(premise1, premise2), m);
            expr_ref premise(_premise);
            th_rewriter rw(m);
            rw(premise);

            expr_ref hd(mk_str_var("hd"), m);
            expr_ref tl(mk_str_var("tl"), m);

            expr_ref_vector conclusion_terms(m);
            conclusion_terms.push_back(ctx.mk_eq_atom(H, mk_concat(hd, tl)));
            conclusion_terms.push_back(ctx.mk_eq_atom(mk_strlen(hd), i));
            conclusion_terms.push_back(ctx.mk_eq_atom(e, mk_indexof(tl, N)));

            expr_ref conclusion(mk_and(conclusion_terms), m);
            assert_implication(premise, conclusion);
        }

        {
            // heuristic: integrate with str.contains information
            // (but don't introduce it if it isn't already in the instance)
            // (0 <= i < len(H)) ==> (H contains N) <==> (H indexof N, i) >= 0
            expr_ref precondition1(m_util_a.mk_gt(i, minus_one), m);
            //expr_ref precondition2(m_util_a.mk_lt(i, mk_strlen(H)), m);
            expr_ref precondition2(m.mk_not(m_util_a.mk_ge(m_util_a.mk_add(i, m_util_a.mk_mul(minus_one, mk_strlen(H))), zero)), m);
            expr_ref _precondition(m.mk_and(precondition1, precondition2), m);
            expr_ref precondition(_precondition);
            th_rewriter rw(m);
            rw(precondition);

            expr_ref premise(m_util_s.str.mk_contains(H, N), m);
            ctx.internalize(premise, false);
            expr_ref conclusion(m_util_a.mk_ge(e, zero), m);
            expr_ref containsAxiom(ctx.mk_eq_atom(premise, conclusion), m);
            expr_ref finalAxiom(rewrite_implication(precondition, containsAxiom), m);
            SASSERT(finalAxiom);
            // we can't assert this during init_search as it breaks an invariant if the instance becomes inconsistent
            m_delayed_assertions_todo.push_back(finalAxiom);
        }
    }

    expr * theory_str::rewrite_implication(expr * premise, expr * conclusion) {
        ast_manager & m = get_manager();
        return m.mk_or(mk_not(m, premise), conclusion);
    }

    void theory_str::assert_implication(expr * premise, expr * conclusion) {
        ast_manager & m = get_manager();
        TRACE("str", tout << __FUNCTION__ << ":" << mk_ismt2_pp(premise, m) << " -> " << mk_ismt2_pp(conclusion, m) << std::endl;);
        expr_ref axiom(m.mk_or(mk_not(m, premise), conclusion), m);
        assert_axiom(axiom);
    }

    // TODO: if the first argument is 0, simplify the constraint
    void theory_str::instantiate_axiom_substr(enode * e) {
        context & ctx = get_context();
        ast_manager & m = get_manager();
        expr* substrBase = nullptr;
        expr* substrPos = nullptr;
        expr* substrLen = nullptr;

        app * expr = e->get_owner();
        if (axiomatized_terms.contains(expr)) {
            TRACE("str", tout << "already set up Substr axiom for " << mk_pp(expr, m) << std::endl;);
            return;
        }
        axiomatized_terms.insert(expr);

        TRACE("str", tout << __FUNCTION__ << ":" << mk_pp(expr, m) << std::endl;);

        VERIFY(m_util_s.str.is_extract(expr, substrBase, substrPos, substrLen));

        expr_ref zero(m_util_a.mk_numeral(rational::zero(), true), m);
        expr_ref minusOne(m_util_a.mk_numeral(rational::minus_one(), true), m);
        SASSERT(zero);
        SASSERT(minusOne);

        expr_ref_vector argumentsValid_terms(m);
        // pos >= 0
        argumentsValid_terms.push_back(m_util_a.mk_ge(substrPos, zero));
        // pos < strlen(base)
        // --> pos + -1*strlen(base) < 0
        argumentsValid_terms.push_back(mk_not(m, m_util_a.mk_ge(
                m_util_a.mk_add(substrPos, m_util_a.mk_mul(minusOne, mk_strlen(substrBase))),
                zero)));

        // len >= 0
        argumentsValid_terms.push_back(m_util_a.mk_ge(substrLen, zero));


        // (pos+len) >= strlen(base)
        // --> pos + len + -1*strlen(base) >= 0
        expr_ref lenOutOfBounds(m_util_a.mk_ge(
                m_util_a.mk_add(substrPos, substrLen, m_util_a.mk_mul(minusOne, mk_strlen(substrBase))),
                zero), m);
        expr_ref argumentsValid = mk_and(argumentsValid_terms);

        // Case 1: pos < 0 or pos >= strlen(base) or len < 0
        // ==> (Substr ...) = ""
        expr_ref case1_premise(m.mk_not(argumentsValid), m);
        expr_ref case1_conclusion(ctx.mk_eq_atom(expr, mk_string("")), m);
        expr_ref case1(m.mk_implies(case1_premise, case1_conclusion), m);

        // Case 2: (pos >= 0 and pos < strlen(base) and len >= 0) and (pos+len) >= strlen(base)
        // ==> base = t0.t1 AND len(t0) = pos AND (Substr ...) = t1
        expr_ref t0(mk_str_var("t0"), m);
        expr_ref t1(mk_str_var("t1"), m);
        expr_ref case2_conclusion(m.mk_and(
                ctx.mk_eq_atom(substrBase, mk_concat(t0,t1)),
                ctx.mk_eq_atom(mk_strlen(t0), substrPos),
                ctx.mk_eq_atom(expr, t1)), m);
        expr_ref case2(m.mk_implies(m.mk_and(argumentsValid, lenOutOfBounds), case2_conclusion), m);

        // Case 3: (pos >= 0 and pos < strlen(base) and len >= 0) and (pos+len) < strlen(base)
        // ==> base = t2.t3.t4 AND len(t2) = pos AND len(t3) = len AND (Substr ...) = t3

        expr_ref t2(mk_str_var("t2"), m);
        expr_ref t3(mk_str_var("t3"), m);
        expr_ref t4(mk_str_var("t4"), m);
        expr_ref_vector case3_conclusion_terms(m);
        case3_conclusion_terms.push_back(ctx.mk_eq_atom(substrBase, mk_concat(t2, mk_concat(t3, t4))));
        case3_conclusion_terms.push_back(ctx.mk_eq_atom(mk_strlen(t2), substrPos));
        case3_conclusion_terms.push_back(ctx.mk_eq_atom(mk_strlen(t3), substrLen));
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

    void theory_str::instantiate_axiom_replace(enode * e) {
        context & ctx = get_context();
        ast_manager & m = get_manager();

        app * expr = e->get_owner();
        if (axiomatized_terms.contains(expr)) {
            TRACE("str", tout << "already set up Replace axiom for " << mk_pp(expr, m) << std::endl;);
            return;
        }
        axiomatized_terms.insert(expr);

        TRACE("str", tout << __FUNCTION__ << ":" << mk_pp(expr, m) << std::endl;);
        std::pair<app*, app*> value = std::make_pair<app*, app*>(mk_str_var("x1"), mk_str_var("x2"));
        expr_ref haystack(expr->get_arg(0), m), needle(expr->get_arg(1), m);
        app* a = m_util_s.str.mk_contains(haystack, needle);
        enode* key = ensure_enode(a);
        if (contain_split_map.contains(key)) {
            std::pair<enode *, enode *> tmpvalue = contain_split_map[key];
            value = std::make_pair<app *, app *>(tmpvalue.first->get_owner(), tmpvalue.second->get_owner());
        }
        else {
            contain_split_map.insert(key, std::make_pair(ctx.get_enode(value.first), ctx.get_enode(value.second)));
        }

        expr_ref x1(value.first, m);
        expr_ref x2(value.second, m);
        expr_ref i1(mk_int_var("i1"), m);
        expr_ref result(mk_str_var("result"), m);

        // condAst = Contains(args[0], args[1])
        expr_ref condAst(mk_contains(expr->get_arg(0), expr->get_arg(1)), m);
        // -----------------------
        // true branch
        expr_ref_vector thenItems(m);
        //  args[0] = x1 . args[1] . x2
        thenItems.push_back(ctx.mk_eq_atom(expr->get_arg(0), mk_concat(x1, mk_concat(expr->get_arg(1), x2))));
        //  i1 = |x1|
        thenItems.push_back(ctx.mk_eq_atom(i1, mk_strlen(x1)));

        bool simpleCase = false;
        zstring needleStr;
        if (m_util_s.str.is_string(expr->get_arg(1), needleStr)) {
            if (needleStr.length() == 1) {
                simpleCase = true;
            }
        }

        if (simpleCase) {
            thenItems.push_back(mk_not(m, mk_contains(x1, expr->get_arg(1))));
        }
        else {
            //  args[0]  = x3 . x4 /\ |x3| = |x1| + |args[1]| - 1 /\ ! contains(x3, args[1])
            expr_ref x3(mk_str_var("x3"), m);
            expr_ref x4(mk_str_var("x4"), m);
            expr_ref tmpLen(m_util_a.mk_add(i1, mk_strlen(expr->get_arg(1)), mk_int(-1)), m);
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
        expr *s = nullptr, *re = nullptr;
        VERIFY(m_util_s.str.is_in_re(ex, s, re));
        expr_ref r{re, m};
        m_membership_todo.push_back({{s, m}, r});
    }

    void theory_str::track_variable_scope(expr * var) {
        if (internal_variable_scope_levels.find(m_scope_level) == internal_variable_scope_levels.end()) {
            internal_variable_scope_levels[m_scope_level] = obj_hashtable<expr>();
        }
        internal_variable_scope_levels[m_scope_level].insert(var);
    }
    app * theory_str::get_ast(theory_var v) {
        return get_enode(v)->get_owner();
    }
    app * theory_str::mk_strlen(expr * e) {
        return m_util_s.str.mk_length(e);
    }

    app * theory_str::mk_int(rational & q) {
        return m_util_a.mk_numeral(q, true);
    }
    app * theory_str::mk_int(int n) {
        return m_util_a.mk_numeral(rational(n), true);
    }

    expr * theory_str::mk_string(const char * str) {
        symbol sym(str);
        return m_util_s.str.mk_string(sym);
    }
    expr * theory_str::mk_string(zstring const& str) {
        return m_util_s.str.mk_string(str);
    }

    void theory_str::push_scope_eh() {
        m_scope_level += 1;
        m_word_eq_todo.push_scope();
        m_word_diseq_todo.push_scope();
        m_membership_todo.push_scope();
        m_non_empty_var.push_scope();
        m_block_todo.push_scope();
        STRACE("str", if (!IN_CHECK_FINAL) tout << "push_scope: " << m_scope_level << '\n';);
    }

    void theory_str::pop_scope_eh(const unsigned num_scopes) {
        m_scope_level -= num_scopes;
        m_word_eq_todo.pop_scope(num_scopes);
        m_word_diseq_todo.pop_scope(num_scopes);
        m_membership_todo.pop_scope(num_scopes);
        m_non_empty_var.pop_scope(num_scopes);
        m_block_todo.pop_scope(num_scopes);
        m_rewrite.reset();
        STRACE("str", if (!IN_CHECK_FINAL)
            tout << "pop_scope: " << num_scopes << " (back to level " << m_scope_level << ")\n";);
    }

    void theory_str::reset_eh() {
        STRACE("str", tout << "reset" << '\n';);
    }


    bool theory_str::lenc_check_sat(expr *e) {
        std::cout << "~~~~~ lenc_check_sat start ~~~~~~~~~\n";  // test_hlin
        str::zaut::symbol_solver csolver(get_manager(), get_context().get_fparams());
        lbool chk_res = csolver.check_sat(e);
        STRACE("str", tout << std::boolalpha << "lenc_check_sat result = " << chk_res << std::endl;);
        std::cout << std::boolalpha << "lenc_check_sat result = " << chk_res << std::endl;
        std::cout << "~~~~~ lenc_check_sat end ~~~~~~~~~~~\n";  // test_hlin
        return chk_res;
    }

    bool theory_str::check_counter_system_lenc(smt::str::solver &solver) {
        using namespace str;
        counter_system cs = counter_system(solver);
        cs.print_counter_system();  // STRACE output
        cs.print_var_expr(get_manager());  // STRACE output

        STRACE("str", tout << "[ABSTRACTION INTERPRETATION]\n";);
        apron_counter_system ap_cs = apron_counter_system(cs);
        STRACE("str", tout << "apron_counter_system constructed..." << std::endl;);
        // ap_cs.print_apron_counter_system();  // standard output only (because of apron library)
        STRACE("str", tout << "apron_counter_system abstraction starting..." << std::endl;);
        ap_cs.run_abstraction();
        STRACE("str", tout << "apron_counter_system abstraction finished..." << std::endl;);
        // make length constraints from the result of abstraction interpretation
        STRACE("str", tout << "generating length constraints..." << std::endl;);
        length_constraint lenc = length_constraint(ap_cs.get_ap_manager(), &ap_cs.get_final_node().get_abs(),
                                                   ap_cs.get_var_expr());
        lenc.pretty_print(get_manager());
        if (!lenc.empty()) {
            expr *lenc_res = lenc.export_z3exp(m_util_a, m_util_s);
            std::cout << "length constraint from counter system:\n" << mk_pp(lenc_res, get_manager()) << std::endl;  // keep stdout for test
            STRACE("str", tout << "length constraint from counter system:\n" << mk_pp(lenc_res, get_manager()) << std::endl;);
            return lenc_check_sat(lenc_res);
//            add_axiom(lenc_res);
//            return true;
        }
        else {  // if generated no length constraint, return true(sat)
            return true;
        }
    }



    void str::word_term::update_next_and_previous_element_maps(const word_term& w,
            std::map<element,element> &next, std::map<element,element> &previous){
        if(w.length()==0) return;
        next.insert({w.get(w.length()-1),str::element::null()});
        previous.insert({w.get(0),str::element::null()});

        for (size_t index = 0; index < w.length() - 1; index++) {
            if (next.count(w.get(index))) {
                if(next.at(w.get(index)) != w.get(index + 1) ) {
                    next.at(w.get(index)) = str::element::multiple();
                }
            } else {
                next.insert({w.get(index),w.get(index + 1)});
                //std::cout<<"just added "<<index<<" to next: "<<w.get(index)<<","<<w.get(index + 1)<<std::endl;
            }
        }
        for (size_t index = 1; index < w.length(); index++) {
            if (previous.count(w.get(index))) {
                if(previous.at(w.get(index)) != w.get(index - 1) ) {
                    previous.at(w.get(index)) = str::element::multiple();
                }
            } else {
                previous.insert({w.get(index),w.get(index - 1)});
            }
        }

    }


    void str::state::merge_elements(){
        bool on_screen=true;

        std::map<element,element> next;
        std::map<element,element> previous;
        std::set<word_equation> m_all_wes(m_eq_wes);
        m_all_wes.insert(m_diseq_wes.begin(),m_diseq_wes.end());


        for(const word_equation& word_eq:m_all_wes) {
            if(on_screen) std::cout<<word_eq.lhs()<<","<<word_eq.rhs()<<std::endl;

            word_term::update_next_and_previous_element_maps(word_eq.lhs(),next,previous);
            word_term::update_next_and_previous_element_maps(word_eq.rhs(),next,previous);
        }
        std::set<element> in_tail;


        std::map<element,element> merge_map(next);
        for(auto& p:next){
            if(on_screen) std::cout<<"next: "<<p.first<<","<<p.second<<std::endl;
            if((!previous.count(p.second)) || (previous.at(p.second)==element::multiple())){
                merge_map.erase(p.first);
            }
        }

        for(auto& p:merge_map) {//those cannot be the head of a seq. of elelemnts be merged
            if(on_screen) std::cout<<"merge: "<<p.first<<","<<p.second<<std::endl;

            in_tail.insert(p.second);
        }

        for(auto& p:merge_map){
            if(!in_tail.count(p.first)){//p is potentially the head of a seq. of elements to be merged
                std::list<element> to_merge;

                element to_append=p.first;
                do{
                    if(on_screen) std::cout<<to_append<<std::flush;

                    to_merge.push_back(to_append);
                    to_append = merge_map.at(to_append);
                }while(merge_map.count(to_append));
                if(on_screen) std::cout<<to_append<<std::endl;

                if(to_append!=element::null()) to_merge.push_back(to_append);

                merge_list_of_elements(m_eq_wes,to_merge);
                merge_list_of_elements(m_diseq_wes,to_merge);
//               TODO: update membership constraints for merged elements
//                element merged(to_merge);
//                m_memberships
            }
        }
    };

    str::word_term str::word_term::merge_list_of_elements(const std::list<element>& to_merge) const{
        element merged(to_merge);
        std::list<element> ret;
        for(int index=0;index<length();index++){
            if(get(index)==to_merge.front()){
                ret.push_back(merged);
                index+=(to_merge.size()-1);
            }else{
                ret.push_back(get(index));
            }
        }
        word_term merged_wt(ret);
        return merged_wt;
    }
    str::word_equation str::word_equation::merge_list_of_elements(const std::list<element>& to_merge) const{


        return {lhs().merge_list_of_elements(to_merge),rhs().merge_list_of_elements(to_merge)};
    }


    void str::state::merge_list_of_elements(std::set<word_equation>& w, const std::list<element>& to_merge) {
        std::set<word_equation> to_add,to_remove;
        for(const word_equation& word_eq:w) {
            word_equation new_word_eq=word_eq.merge_list_of_elements(to_merge);
            if(new_word_eq != word_equation::null()){
                to_add.insert(new_word_eq);
                to_remove.insert(word_eq);
            }
        }
        for(auto& rm_word_eq:to_remove) w.erase(rm_word_eq);
        for(auto& add_word_eq:to_add) w.insert(add_word_eq);
    }

    str::element::element(const std::list<element>& list):m_type{element::t::VAR}{

        for(std::list<element>::const_iterator it=list.begin(); it != list.end(); ++it){

            if(it->m_type==t::VAR){
                m_shortname = m_shortname + it->m_shortname;
            }else{
                m_shortname = m_shortname + it->m_value.encode();
            }
            m_value = m_value + it->m_value;
            m_expr.push_back(it->m_expr.front());
        }
    }

    final_check_status theory_str::final_check_eh() {
        ast_manager& m = get_manager();
//        expr *refinement = nullptr;
//        for(const auto& e:m_block_todo){
//            std::cout<<mk_pp(e,m)<<std::endl;
//            refinement = refinement == nullptr ? e : m.mk_or(refinement, e);
//        }
//        if (refinement != nullptr) {
//            std::cout<<mk_pp(refinement,m)<<std::endl;
//            assert_axiom(refinement);
//        }
//        return FC_CONTINUE;

        using namespace str;
//        print_ctx(get_context());  // test_hlin
        if (m_word_eq_todo.empty()) return FC_DONE;
        TRACE("str", tout << "final_check: level " << get_context().get_scope_level() << '\n';);
        IN_CHECK_FINAL = true;

        if (!m_aut_imp) m_aut_imp = std::make_shared<zaut_adaptor>(get_manager(), get_context());
        state&& root = mk_state_from_todo();
        for(auto& e:m_non_empty_var) root.m_non_empty_var.insert(e);
        STRACE("str", tout << "[Abbreviation <=> Fullname]\n"<<element::abbreviation_to_fullname(););

        STRACE("str", tout << "root original:\n" << root <<std::endl;);
        root.remove_single_variable_word_term();
        STRACE("str", tout << "root removed single var:\n" << root <<std::endl;);
        root.merge_elements();
        STRACE("str", tout << "root merged:\n" << root <<std::endl;);


        if(root.word_eqs().size()==0) return FC_DONE;
        STRACE("str", tout << "root built:\n" << root << '\n';);
        if (root.unsolvable_by_inference()) {
            block_curr_assignment();
            IN_CHECK_FINAL = false;
            return FC_CONTINUE;
        }

        solver solver{std::move(root), m_aut_imp};
        if (solver.check() == result::SAT) {
            STRACE("str", tout << "graph size: #state=" << solver.get_graph().access_map().size() << '\n';);
            STRACE("str", tout << "root state quadratic? " << solver.get_root().get().quadratic() << '\n';);
            // stdout for test: print graph size then exit
            std::cout << "graph construction summary:\n";
            std::cout << "#states total = " << solver.get_graph().access_map().size() << '\n';
            std::cout << "root state quadratic? " << solver.get_root().get().quadratic() << '\n';

            bool cs_lenc_check_res = false;//check_counter_system_lenc(solver);

            TRACE("str", tout << "final_check ends\n";);

            if (cs_lenc_check_res) {
                IN_CHECK_FINAL = false;
                return FC_DONE;
            }  // will leave this if block if lenc_check_sat returns false
        }
        block_curr_assignment();
        TRACE("str", tout << "final_check ends\n";);
        IN_CHECK_FINAL = false;
        return FC_CONTINUE;
    }

    model_value_proc *theory_str::mk_value(enode *const n, model_generator& mg) {
        ast_manager& m = get_manager();
        app *const tgt = n->get_owner();
        (void) m;
        STRACE("str", tout << "mk_value: sort is " << mk_pp(m.get_sort(tgt), m) << ", "
                           << mk_pp(tgt, m) << '\n';);
        return alloc(expr_wrapper_proc, tgt);
    }

    void theory_str::init_model(model_generator& mg) {
        STRACE("str", if (!IN_CHECK_FINAL) tout << "init_model\n";);
    }

    void theory_str::finalize_model(model_generator& mg) {
        STRACE("str", if (!IN_CHECK_FINAL) tout << "finalize_model\n";);
    }

    lbool theory_str::validate_unsat_core(expr_ref_vector& unsat_core) {
        return l_undef;
    }

    bool theory_str::is_of_this_theory(expr *const e) const {
        return is_app(e) && to_app(e)->get_family_id() == get_family_id();
    }

    bool theory_str::is_string_sort(expr *const e) const {
        return m_util_s.str.is_string_term(e);
    }

    bool theory_str::is_regex_sort(expr *const e) const {
        return m_util_s.is_re(e);
    }


    expr_ref theory_str::mk_sub(expr *a, expr *b) {
        ast_manager& m = get_manager();

        expr_ref result(m_util_a.mk_sub(a, b), m);
        m_rewrite(result);
        return result;
    }



    literal theory_str::mk_literal(expr *const e) {
        ast_manager& m = get_manager();
        context& ctx = get_context();
        expr_ref ex{e, m};
        m_rewrite(ex);
        if (!ctx.e_internalized(ex)) {
            ctx.internalize(ex, false);
        }
        enode *const n = ctx.get_enode(ex);
        ctx.mark_as_relevant(n);
        return ctx.get_literal(ex);
    }

    bool_var theory_str::mk_bool_var(expr *const e) {
        ast_manager& m = get_manager();
        STRACE("str", tout << "mk_bool_var: " << mk_pp(e, m) << '\n';);
        if (!m.is_bool(e)) {
            return null_bool_var;
        }
        context& ctx = get_context();
        SASSERT(!ctx.b_internalized(e));
        const bool_var& bv = ctx.mk_bool_var(e);
        ctx.set_var_theory(bv, get_id());
        ctx.set_enode_flag(bv, true);
        return bv;
    }

    app * theory_str::mk_int_var(std::string name) {
        context & ctx = get_context();
        ast_manager & m = get_manager();

        sort * int_sort = m.mk_sort(m_util_a.get_family_id(), INT_SORT);
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

    app * theory_str::mk_str_var(std::string name) {
        context & ctx = get_context();

        STRACE("str", tout << __FUNCTION__ << ":" << name << " at scope level " << m_scope_level << std::endl;);

        sort * string_sort = m_util_s.str.mk_string_sort();
        app * a = mk_fresh_const(name.c_str(), string_sort);
        m_trail.push_back(a);

        STRACE("str", tout << "a->get_family_id() = " << a->get_family_id() << std::endl
                           << "this->get_family_id() = " << this->get_family_id() << std::endl;);

        // I have a hunch that this may not get internalized for free...
        ctx.internalize(a, false);
        SASSERT(ctx.get_enode(a) != NULL);
        SASSERT(ctx.e_internalized(a));
        // this might help??
        mk_var(ctx.get_enode(a));
        m_basicstr_axiom_todo.push_back(ctx.get_enode(a));
        STRACE("str", tout << "add " << mk_pp(a, get_manager()) << " to m_basicstr_axiom_todo" << std::endl;);

        variable_set.insert(a);
        internal_variable_set.insert(a);
        track_variable_scope(a);

        return a;
    }
    app * theory_str::mk_fresh_const(char const* name, sort* s) {
        string_buffer<64> buffer;
        buffer << name;
        buffer << "!tmp";
        buffer << m_fresh_id;
        m_fresh_id++;
        return m_util_s.mk_skolem(symbol(buffer.c_str()), 0, nullptr, s);
    }
    str::word_term theory_str::mk_word_term(expr *const e) const {
        using namespace str;
        zstring s;
        if (m_util_s.str.is_string(e, s)) {
            return word_term::from_string(s);
        }
        if (m_util_s.str.is_concat(e)) {
            word_term result;
            for (unsigned i = 0; i < to_app(e)->get_num_args(); i++) {
                result.concat(mk_word_term(to_app(e)->get_arg(i)));
            }
            return result;
        }
        std::stringstream ss;
        ss << mk_pp(e, get_manager());
        return word_term::from_variable({ss.str().data()}, e);
    }

    bool theory_str::is_const_fun(expr *const e) const {
        return is_app(e) && to_app(e)->get_decl()->get_arity() == 0;
    }

    str::state theory_str::mk_state_from_todo() {
        using namespace str;
        state result{std::make_shared<str::basic_memberships>(m_aut_imp)};

        STRACE("str", tout << "[Build State]\nmembership todo:\n";);
        if(!ignore_membership) {
            STRACE("str", if (m_membership_todo.empty()) tout << "--\n";);
            for (const auto &m : m_membership_todo) {
                if (is_const_fun(m.first)) {
                    zstring name{to_app(m.first)->get_decl()->get_name().bare_str()};
                    result.add_membership({element::t::VAR, name, m.first}, m.second);
                } else {
                    std::stringstream ss;
                    ss << mk_pp(m.first, get_manager());
                    result.add_membership({element::t::VAR, ss.str().data(), m.first}, m.second);
                }
                STRACE("str", tout << m.first << " is in " << m.second << '\n';);
            }
        }
        STRACE("str", tout << "word equation todo:\n";);
        STRACE("str", if (m_word_eq_todo.empty()) tout << "--\n";);
        for (const auto& eq : m_word_eq_todo) {
            result.add_word_eq({mk_word_term(eq.first), mk_word_term(eq.second)});
            STRACE("str", tout << eq.first << " = " << eq.second << '\n';);
        }
        STRACE("str", tout << "word disequality todo:\n";);
        STRACE("str", if (m_word_diseq_todo.empty()) tout << "--\n";);
        for (const auto& diseq : m_word_diseq_todo) {
            result.add_word_diseq({mk_word_term(diseq.first), mk_word_term(diseq.second)});
            STRACE("str", tout << diseq.first << " != " << diseq.second << '\n';);
        }

        result.remove_useless_diseq();
        return result;
    }
    void str::state::initialize_eq_class_map(){
        std::map<word_term, word_term> union_find;

        for(auto& eq :m_eq_wes) {
            if(union_find.find(eq.lhs())==union_find.end()) {
                union_find[eq.lhs()] = eq.lhs();
            }
            union_find[eq.rhs()] = union_find[eq.lhs()];
        }

        for(auto& k:union_find){
            auto& member=k.first;
            auto& farther=k.second;
            while(farther!= union_find[farther]){
                farther= union_find[farther];
            }
            eq_class_map[farther].insert(member);
        }
    }
    void str::state::remove_single_variable_word_term() {
        std::set<word_equation> updated_result;

        bool updated =true;


        while (updated) {
            updated = false;
            for(auto &eq:m_eq_wes){
                element source=element::null();
                word_term target;

                if (eq.lhs().length() == 1 && eq.lhs().has_variable() && m_memberships->get(eq.lhs().head())== nullptr ) {
                    source= eq.lhs().head();
                    target= eq.rhs();
                    updated =true;
                } else if (eq.rhs().length() == 1 && eq.rhs().has_variable() && m_memberships->get(eq.rhs().head())== nullptr) {
                    source= eq.rhs().head();
                    target= eq.lhs();
                    updated =true;
                }
                if(updated){
                    for (auto &eq2:m_eq_wes) {
                        word_equation eq3 = eq2.replace(source, target);
                        if (eq3.lhs() != eq3.rhs()) updated_result.insert(eq3);
                    }
                    m_eq_wes = updated_result;
                    updated_result.clear();
                    for (auto &eq2:m_diseq_wes) {
                        word_equation eq3 = eq2.replace(source, target);
                        updated_result.insert(eq3);
                    }
                    m_diseq_wes = updated_result;
                    updated_result.clear();
                    break;
                }
            }
        }
    }


    bool str::state::has_non_quadratic_var(const word_term& wt){
        for(const element& e:wt.content()){
            if(e.typed(element::t::VAR) && var_occurrence[e]>2){
                return true;
            }
        }
        return false;
    }

    //best effort implementation to make the word equation quadratic
    void str::state::quadratify(){
        using namespace std;

        STRACE("str", tout << "\noriginal:\n" << *this << '\n';);
        remove_single_variable_word_term();

        STRACE("str", tout << "\nremoved single variable word terms:\n" << *this << '\n';);

        initialize_eq_class_map();

        set<word_equation> result;
        for(auto &k: eq_class_map) {
            set<word_term>::iterator cur=k.second.begin();
            set<word_term>::iterator next=++k.second.begin();

            bool selected=false;
            while(next!=eq_class_map[k.first].end()) {
                if(has_non_quadratic_var(*cur)||has_non_quadratic_var(*cur)){
                    selected=true;
                }else{
                    result.insert({*cur, *next});
                }

                cur++;
                next++;
                if(selected && next==eq_class_map[k.first].end()){
                    result.insert({*cur, *k.second.begin()});
                }
            };
        }
        m_eq_wes=result;
    }
    void theory_str::assert_axiom(expr *e) {
        if (e == nullptr || get_manager().is_true(e)) return;

        context& ctx = get_context();
//        SASSERT(!ctx.b_internalized(e));
        if(!ctx.b_internalized(e)){
            ctx.internalize(e, false);
        }
        ctx.internalize(e, false);
        literal l{ctx.get_literal(e)};
        ctx.mark_as_relevant(l);
        ctx.mk_th_axiom(get_id(), 1, &l);
        STRACE("str", ctx.display_literal_verbose(tout << "[Assert]\n", l) << '\n';);
    }


    void theory_str::set_conflict(const literal_vector& lv) {
        context& ctx = get_context();
        const auto& js = ext_theory_conflict_justification{
                get_id(), ctx.get_region(), lv.size(), lv.c_ptr(), 0, nullptr, 0, nullptr};
        ctx.set_conflict(ctx.mk_justification(js));
        STRACE("str", ctx.display_literals_verbose(tout << "[Conflict]\n", lv) << '\n';);
    }

    void theory_str::block_curr_assignment() {

        ast_manager& m = get_manager();
        expr *refinement = nullptr;
        STRACE("str", tout << "[Refinement]\nformulas:\n";);

        std::cout << "[Refinement]\nformulas:\n";

//        for (const auto& we : m_word_eq_todo) {
//            expr *const e = m.mk_not(mk_eq_atom(we.first, we.second));
//            refinement = refinement == nullptr ? e : m.mk_or(refinement, e);
//            STRACE("str", tout << we.first << " = " << we.second << '\n';);
//        }
//        for (const auto& wi : m_word_diseq_todo) {
//            expr *const e = mk_eq_atom(wi.first, wi.second);
//            refinement = refinement == nullptr ? e : m.mk_or(refinement, e);
//            STRACE("str", tout << wi.first << " != " << wi.second << '\n';);
//        }
//        for (const auto& mem : m_membership_todo) {
//            expr *const e = m.mk_not(m_util_s.re.mk_in_re(mem.first, mem.second));
//            refinement = refinement == nullptr ? e : m.mk_or(refinement, e);
//            STRACE("str", tout << mem.first << " in " << mem.second << '\n';);
//        }

        for(const auto& e:m_block_todo){
            refinement = refinement == nullptr ? e : m.mk_or(refinement, e);
            STRACE("str", tout << mk_pp(e,m) << '\n';);
            std::cout <<mk_pp(e,m)<<std::endl;
        }
        if (refinement != nullptr) {
            assert_axiom(refinement);
        }
    }
    theory_var theory_str::get_var(expr * n) const {
        if (!is_app(n)) {
            return null_theory_var;
        }
        context & ctx = get_context();
        if (ctx.e_internalized(to_app(n))) {
            enode * e = ctx.get_enode(to_app(n));

            ast_manager & m = get_manager();
            return e->get_th_var(get_id());
        }
        return null_theory_var;
    }

    expr * theory_str::mk_concat(expr * n1, expr * n2) {
        expr *concatAst = nullptr;
        concatAst = m_util_s.str.mk_concat(n1, n2);
        m_trail.push_back(concatAst);
        return concatAst;
    }
    void theory_str::get_nodes_in_concat(expr * node, ptr_vector<expr> & nodeList) {
        app * a_node = to_app(node);
        if (!m_util_s.str.is_concat(a_node)) {
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

    void theory_str::dump_assignments() const {
        STRACE("str", \
                ast_manager& m = get_manager();
                context& ctx = get_context();
                std::cout << "dump all assignments:\n";
                expr_ref_vector assignments{m};
                ctx.get_assignments(assignments);
                for (expr *const e : assignments) {
                   // ctx.mark_as_relevant(e);
                    std::cout <<"**"<< mk_pp(e, m) << (ctx.is_relevant(e) ? "\n" : " (not relevant)\n");
                }
        );
    }
}
