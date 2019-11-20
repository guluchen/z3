#include <algorithm>
#include <numeric>
#include <sstream>
#include "ast/ast_pp.h"
#include "ast/rewriter/bool_rewriter.h"
#include "smt/theory_str/theory_str2.h"
#include "smt/smt_context.h"
#include "smt/smt_model_generator.h"
#include "smt/theory_lra.h"
#include "smt/theory_arith.h"
#include "smt/smt_context.h"
#include "ast/seq_decl_plugin.h"
#include "ast/reg_decl_plugins.h"


namespace smt {

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

        const expr_ref element::length_expr(ast_manager& m) const{
            expr_ref ret{m};
            seq_util m_util_s(m);
            arith_util m_util_a(m);

            if(m_type==t::CONST){
                ret = {m_util_a.mk_int(1),m};
            }else{
                for(auto& expr:origin_expr()){
                    if(!ret) ret = {m_util_s.str.mk_length(expr), m};
                    else ret = {m_util_a.mk_add(ret, m_util_s.str.mk_length(expr)), m};
                }

            }
            return ret;
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

        element str::word_term::get(size_t index ) const {
            if (length() > index)
            {
                std::list<element>::const_iterator it = std::next(m_elements.begin(), index);
                return {*it};
            }
            else return element::null();
        };

        void str::word_term::update_next_and_previous_element_maps(const word_term& w,
                                                                   std::map<element,element> &next, std::map<element,element> &previous){
            if(w.length()==0) return;
            if(w.get(w.length()-1).type()==element::t::VAR) {
                if(next.count(w.get(w.length()-1))){
                    if(next.at(w.get(w.length()-1)) != str::element::null() ) {
                        next.at(w.get(w.length()-1)) = str::element::multiple();
                    }
                }else {
                    next.insert({w.get(w.length() - 1), str::element::null()});
                }
            };
            if(w.get(0).type()==element::t::VAR){
                if(previous.count(w.get(0))){
                    if(previous.at(w.get(0)) != str::element::null() ) {
                        previous.at(w.get(0)) = str::element::multiple();
                    }
                }else {
                    previous.insert({w.get(0),str::element::null()});
                }

            }

            for (size_t index = 0; index < w.length() - 1; index++) {
                if(w.get(index).type()!=element::t::VAR) continue;
                if (next.count(w.get(index))) {
                    if(next.at(w.get(index)) != w.get(index + 1) ) {
                        next.at(w.get(index)) = str::element::multiple();
                    }
                } else {
                    if(w.get(index + 1).type()==element::t::VAR)
                        next.insert({w.get(index),w.get(index + 1)});
                    else
                        next.insert({w.get(index),element::multiple()});
                    //std::cout<<"just added "<<index<<" to next: "<<w.get(index)<<","<<w.get(index + 1)<<std::endl;
                }
            }
            for (size_t index = 1; index < w.length(); index++) {
                if(w.get(index).type()!=element::t::VAR) continue;
                if (previous.count(w.get(index))) {
                    if(previous.at(w.get(index)) != w.get(index - 1) ) {
                        previous.at(w.get(index)) = str::element::multiple();
                    }
                } else {
                    if(w.get(index - 1).type()==element::t::VAR) {
                        previous.insert({w.get(index), w.get(index - 1)});
                    }else{
                        previous.insert({w.get(index), element::multiple()});
                    }
                }
            }

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


        bool word_term::unequalable(const word_term& w1, const word_term& w2, const std::map<element, size_t>& lb )  {
            return (!w1.has_variable() && w1.length() < w2.minimal_model_length(lb)) ||
                   (!w2.has_variable() && w2.length() < w1.minimal_model_length(lb)) ||
                   word_term::prefix_const_mismatched(w1, w2) || word_term::suffix_const_mismatched(w1, w2);
        }

        bool word_equation::unsolvable(const std::map<element, size_t>& lb ) const {
                return word_term::unequalable(lhs(),rhs(),lb);
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

        not_contains::not_contains(const word_term& superstring, const word_term& substring) {
            m_superstring=superstring;
            m_substring=substring;
        }

        not_contains not_contains::replace(const element& tgt, const word_term& subst) const {
            not_contains result{*this};
            result.m_superstring.replace(tgt, subst);
            result.m_substring.replace(tgt, subst);
            return result;
        }

        not_contains not_contains::remove(const element& tgt) const {
            return replace(tgt, {});
        }

        not_contains not_contains::remove_all(const std::set<element>& tgt) const {
            not_contains result{*this};
            for (const auto& e : tgt) {
                result.m_superstring.replace(e, {});
                result.m_substring.replace(e, {});
            }
            return result;
        }

        const bool not_contains::is_invalid_by_syntatic_check() const{

            std::list<element>::const_iterator pos = std::search(
                    m_superstring.content().begin(), m_superstring.content().end(),
                    m_substring.content().begin(), m_substring.content().end());

            if(pos == m_superstring.content().end()){
                return false;
            }else{
                return true;
            }

        }

        bool not_contains::operator==(const not_contains& other) const {
            return m_superstring == other.m_superstring && m_substring == other.m_substring;
        }

        bool not_contains::operator<(const not_contains& other) const {
            if (m_superstring < other.m_superstring) return true;
            if (other.m_superstring < m_superstring) return false;
            return m_substring < other.m_substring;
        }

        std::ostream& operator<<(std::ostream& os, const not_contains& we) {
            os << "not_contains(" <<we.m_superstring << "," << we.m_substring<<")";
            return os;
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

        expr_ref length_constraints::constraint::get_expr(ast_manager& m) const{//TODO: test if it fits the invariant of Z3
            STRACE("str", tout << __LINE__ << " enter " << __FUNCTION__ << std::endl;);
            bool on_screen =false;
            seq_util m_util_s(m);
            arith_util m_util_a(m);
            expr_ref ret(m);
            for(auto & conf:m_coeffs){
                if(on_screen) std::cout<<conf.second<<"*"<<conf.first<<std::endl;
                if(conf.first!=element::null()) {
                    expr_ref length(m);
                    for (auto &e:conf.first.origin_expr()) {
                        if (!length) length = {m_util_s.str.mk_length(e), m};
                        else length = {m_util_a.mk_add(length, m_util_s.str.mk_length(e)), m};
                    }
                    expr_ref const_mul_var_length{m};
                    if(conf.second==1){
                        const_mul_var_length=length;
                    }else {
                        const_mul_var_length={m_util_a.mk_mul(m_util_a.mk_int(conf.second), length), m};
                    }

                    if (!ret) ret = const_mul_var_length;
                    else ret = {m_util_a.mk_add(ret, const_mul_var_length), m};
                }else{
                    if (!ret) ret = {m_util_a.mk_int(conf.second),m};
                    else ret = {m_util_a.mk_add(ret, m_util_a.mk_int(conf.second)), m};
                }
            }

            if(type==t::GT){
                ret = {m_util_a.mk_gt(ret, m_util_a.mk_int(0)), m};
            }else if(type==t::EQ){
                ret = {m_util_a.mk_eq(ret, m_util_a.mk_int(0)), m};
            }
            STRACE("str", tout << __LINE__ << " leave " << __FUNCTION__ << std::endl;);
            return ret;
        }

        length_constraints::length_constraints(const std::set<element>& vars){
            for(auto& var:vars){
                m_len_cons.insert({var,{var}});
            }
            m_path_cond.insert({});
        }

        expr_ref length_constraints::get_path_cond(ast_manager& m) const{
            bool on_screen=false;
            STRACE("str", tout << __LINE__ << " enter " << __FUNCTION__ << std::endl;);

            expr_ref ret(m);
            for(auto& c:m_path_cond){
                if(on_screen) std::cout<<"[Path Condition]"<<mk_pp(c.get_expr(m),m)<<std::endl;

                if(!ret){ret=c.get_expr(m);}
                else {ret = {m.mk_and(ret,c.get_expr(m)),m};}
            }
            STRACE("str", tout << __LINE__ << " leave " << __FUNCTION__ << std::endl;);
            return ret;
        }
        expr_ref length_constraints::get_len_cons(const element& e, ast_manager& m) const{
            if(m_len_cons.count(e)>0){
                return m_len_cons.at(e).get_expr(m);
            }else{
                return {m.mk_true(),m};
            }

        }
        length_constraints length_constraints::assign_prefix(const element& x, const element& a) const{
            //x -> a.x

            length_constraints ret(*this);
            SASSERT(m_len_cons.count(x)>0);
            ret.m_len_cons.at(x).add(constraint::constant(), -1);
            constraint ex = ret.m_len_cons.at(x);

            ret.m_path_cond.insert(ex.set_type(constraint::t::GT));//set m_len_cons[x] -1 >0
            return ret;
        };
        length_constraints length_constraints::assign_as(const element& x, const element& y) const{
            // x -> y
            length_constraints ret(*this);
            SASSERT(m_len_cons.count(x)>0);
            SASSERT(m_len_cons.count(y)>0);
            constraint ex_minus_ey = ret.m_len_cons.at(x);
            ex_minus_ey.minus(ret.m_len_cons.at(y));

            ret.m_len_cons.at(x) = ret.m_len_cons.at(y);
            ret.m_path_cond.insert(ex_minus_ey.set_type(constraint::t::EQ));//set m_len_cons[x]=m_len_cons[y]

            return ret;
        };
        length_constraints length_constraints::assign_const(const element& x, const word_term& tgt) const{
            // x -> string(tgt)
            length_constraints ret(*this);
            SASSERT(m_len_cons.count(x)>0);
            constraint ex_minus_len_tgt = ret.m_len_cons.at(x);
            ex_minus_len_tgt.add(constraint::constant(), -tgt.length());

            ret.m_len_cons.at(x).minus(ret.m_len_cons.at(x));
            ret.m_len_cons.at(x).add(constraint::constant(), tgt.length());
            ret.m_path_cond.insert(ex_minus_len_tgt.set_type(constraint::t::EQ));//set m_len_cons[x] = |tgt|

            return ret;
        };
        length_constraints length_constraints::assign_empty(const element& x, const element& non_zero_var) const{
            // x -> epsilon

            length_constraints ret(*this);

            SASSERT(m_len_cons.count(x)>0);
            constraint ex = ret.m_len_cons.at(x);
            ret.m_len_cons.at(x).minus(ret.m_len_cons.at(x));
            ret.m_path_cond.insert(ex.set_type(constraint::t::EQ));//set m_len_cons[x] = 0
            return ret;
        }
        length_constraints length_constraints::assign_empty_all(const std::set<element>& vars) const{
            // no constraint on all variables
            length_constraints ret(*this);

            for(auto& v:vars){
                ret = ret.assign_empty(v,v);
            }
            return ret;
        };
        length_constraints length_constraints::assign_prefix_var(const element& x, const element& y) const{
            // x ->yx
            length_constraints ret(*this);
            SASSERT(m_len_cons.count(x)>0);
            SASSERT(m_len_cons.count(y)>0);
            constraint ex_miuns_ey = ret.m_len_cons.at(x);
            ex_miuns_ey.minus(ret.m_len_cons.at(y));
            constraint ey = ret.m_len_cons.at(y);

            ret.m_len_cons.at(x).minus(ret.m_len_cons.at(y));

            ret.m_path_cond.insert(ex_miuns_ey.set_type(constraint::t::GT));//set m_len_cons[x]-m_len_cons[y]>0
            ret.m_path_cond.insert(ey.set_type(constraint::t::GT));//set m_len_cons[y]>0
            return ret;
        };

        length_constraints length_constraints::add_equality(const element& lhs, const word_term& rhs) const{
            length_constraints ret(*this);
            constraint len_diff(lhs);
            len_diff.set_type(constraint::t::EQ);

            for(auto& e:rhs.content()){
                constraint len_e(e);
                len_diff.minus(len_e);
            }

            ret.m_path_cond.insert(len_diff);
            return ret;
        }



        void length_constraints::merge_list_of_elements(const std::list<element>& to_merge) {
            element merged(to_merge);
            constraint sum;
            sum.set_type(constraint::t::EXPR);
            for(auto& e:to_merge){
                SASSERT(m_len_cons.count(e)>0);
                sum.add(m_len_cons[e]);
                m_len_cons.erase(e);
            }
            m_len_cons.insert({merged,sum});


        };

        std::ostream& operator<<(std::ostream& os, const length_constraints& lc) {
            lc.print_len_cons(os);
            lc.print_path_cond(os);

            return os;
        }



        std::size_t state::hash::operator()(const state& s) const {
            static const auto word_equation_hash{word_equation::hash{}};
            std::size_t result{22447};
            result += (s.get_strategy()==state::transform_strategy::allow_empty_var)? 10093 : 0;
            for (const auto& we : s.m_eq_wes) {
                result += word_equation_hash(we);
            }
            for (const auto& we : s.m_diseq_wes) {
                result += word_equation_hash(we);
            }
            result += s.m_memberships->hash();
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
            bool on_screen=false;
            std::map<word_term, std::size_t> word_class_tbl;
            std::vector<std::vector<word_term>> classes;
            for (const auto& we : m_eq_wes) {
                const word_term& w1 = we.lhs();
                const word_term& w2 = we.rhs();
                if(on_screen) std::cout<<"From "<<w1<<" = "<<w2<<" we infer that ";
                const auto& fit1 = word_class_tbl.find(w1);
                const auto& fit2 = word_class_tbl.find(w2);


                if (fit1 != word_class_tbl.end() && fit2 != word_class_tbl.end()) {
                    const auto class_id1 = fit1->second;
                    const auto class_id2 = fit2->second;
                    if(on_screen) std::cout<<"both "<<w1<<" and "<<w2<<" should in the same class, ";
                    if(class_id1==class_id2) {
                        if(on_screen) std::cout<<"and both of them are alreday in the same class "<<class_id1<<std::endl;
                    }else{
                        if(on_screen) std::cout<<"move "<<w1<<" and its equivalent word terms from class "<<class_id1<<" to "<<class_id2<<std::endl;
                        for(const auto& w:classes.at(class_id1)){
                            classes.at(class_id2).push_back(w);
                            word_class_tbl[w] = class_id2;
                        }
                        classes.at(class_id1).clear();
                    }
                    continue;
                }
                if (fit1 == word_class_tbl.end() && fit2 == word_class_tbl.end()) {
                    classes.push_back({w1, w2});
                    const auto class_id = classes.size() - 1;
                    if(on_screen) std::cout<<"both "<<w1<<" and "<<w2<<" are in class "<<class_id<<std::endl;
                    word_class_tbl[w1] = class_id;
                    word_class_tbl[w2] = class_id;
                    continue;
                }
                if (fit1 != word_class_tbl.end()) {
                    const auto class_id = fit1->second;
                    classes.at(class_id).push_back(w2);
                    word_class_tbl[w2] = class_id;
                    if(on_screen) std::cout<<w2<<" is in class "<<class_id<<std::endl;
                } else {
                    const auto class_id = fit2->second;
                    classes.at(class_id).push_back(w1);
                    word_class_tbl[w1] = class_id;
                    if(on_screen) std::cout<<w1<<" is in class "<<class_id<<std::endl;
                }
            }
            for(auto& c: classes){
                if(on_screen)  std::cout<<"[class] ";
                for(auto& t: c){
                    if(on_screen)  std::cout<<"["<<t<<"]";
                }
                if(on_screen)  std::cout<<std::endl;
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
            bool on_screen=false;
            const auto& unequalable = word_term::unequalable;
            for (const auto& cls : eq_classes()) {
                if (cls.size() == 0) continue;
                if(on_screen) std::cout<<"[Eq class start]\n";
                if (cls.size() == 2) {
                    if(on_screen) std::cout<<cls.at(0)<<"\n"<<cls.at(1)<<"\n";
                    if (unequalable(cls.at(0), cls.at(1), m_lower_bound)) return true;
                    continue;
                }
                std::vector<bool> select(cls.size());
                std::fill(select.end() - 2, select.end(), true);
                do {
                    std::vector<word_term> selected;
                    selected.reserve(2);
                    for (std::size_t i = 0; i < cls.size(); i++) {
                        if (select.at(i)) {
                            if(on_screen) std::cout<<cls.at(i)<<"\n";
                            selected.push_back(cls.at(i));
                        }
                    }
                    if (unequalable(selected.at(0), selected.at(1), m_lower_bound)) return true;
                } while (std::next_permutation(select.begin(), select.end()));
                if(on_screen) std::cout<<"[Eq class end]\n";

            }
            return false;
        }

        bool state::diseq_inconsistent() const {
            return !m_diseq_wes.empty() && m_diseq_wes.begin()->empty();
        }

        bool state::unsolvable_by_check() const {
            const auto& unsolvable = std::bind(&word_equation::unsolvable, _1, m_lower_bound);
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
                    m_lower_bound[v]=1;
                }
            }
        }

        void state::add_word_diseq(const word_equation& we) {
            SASSERT(we);
            word_equation&& trimmed = we.trim_prefix();
            //update length bound

            if(we.in_definition_form() && we.definition_body().length()==0 && get_strategy()==state::transform_strategy::dynamic_empty_var_detection){
                m_lower_bound[we.definition_var()]=1;
            }
//            std::cout<<we<<" is in definition form "<<we.in_definition_form()<<" and its length of definition body is "<<we.definition_body().length()<<std::endl;
            if (trimmed.unsolvable(m_lower_bound)) return;

            m_diseq_wes.insert(std::move(trimmed));


        }

        void state::add_not_contains(const smt::str::not_contains &nc) {
            m_not_contains.insert(std::move(nc));
        }



        void str::state::remove_useless_diseq(){
            std::set<word_equation> to_remove;

//            for(auto& v: m_lower_bound){
//                std::cout<<v.first<<"->"<<v.second<<std::endl;
//            }
//

            for(auto & diseq:m_diseq_wes){
                if(diseq.unsolvable(m_lower_bound)) to_remove.insert(diseq);
            }
            for(auto & rm_diseq:to_remove){
                m_diseq_wes.erase(rm_diseq);
            }

        }

        void state::add_membership(const element& var, expr *re) {
            m_memberships->set(var, re);
        }

        void state::set_length(const length_constraints& lc){
            m_length=lc;
        }

        state state::assign_empty(const element& var, const element& non_zero_var) const {
            SASSERT(var.typed(element::t::VAR));

            state result{m_memberships->assign_empty(var)};
            result.set_strategy(m_strategy);
            result.m_lower_bound=m_lower_bound;
            result.m_lower_bound[non_zero_var]=1;

            result.m_model=m_model;
            for(auto& var_wt:m_model){
                element lhs=var_wt.first;
                word_term rhs = var_wt.second;
                rhs.replace(var,{});
                result.m_model[lhs]=rhs;
            }

            for (const auto& we : m_eq_wes) {
                result.add_word_eq(we.remove(var));
            }
            for (const auto& we : m_diseq_wes) {
                result.add_word_diseq(we.remove(var));
            }
            for (const auto& nc : m_not_contains) {
                result.add_not_contains(nc.remove(var));
            }
            result.set_length(m_length.assign_empty(var,non_zero_var));


            return result;
        }

        state state::assign_empty_all(const std::set<element>& vars) const {
            static const auto& is_var = std::bind(&element::typed, _1, element::t::VAR);
            SASSERT(std::all_of(vars.begin(), vars.end(), is_var));

            state result{m_memberships->assign_empty_all(vars)};
            result.set_strategy(m_strategy);
            result.m_lower_bound=m_lower_bound;

            auto temp_model=m_model;
            for (std::set<element>::iterator it(vars.begin()); it != vars.end(); ++it)
            {
                result.m_lower_bound.erase(*it);
                for(auto& var_wt:temp_model){
                    element lhs=var_wt.first;
                    word_term rhs = var_wt.second;
                    rhs.replace(*it,{});
                    result.m_model[lhs]=rhs;
                }

                temp_model=result.m_model;
            }

            for (const auto& we : m_eq_wes) {
                result.add_word_eq(we.remove_all(vars));
            }
            for (const auto& we : m_diseq_wes) {
                result.add_word_diseq(we.remove_all(vars));
            }
            for (const auto& nc : m_not_contains) {
                result.add_not_contains(nc.remove_all(vars));
            }
            result.set_length(m_length.assign_empty_all(vars));

            return result;
        }

        state state::assign_const(const element& var, const word_term& tgt) const {
            static const auto& is_const = std::bind(&element::typed, _1, element::t::CONST);
            SASSERT(var.typed(element::t::VAR));
            SASSERT(std::all_of(tgt.content().begin(), tgt.content().end(), is_const));

            state result{m_memberships->assign_const(var, tgt)};
            result.set_strategy(m_strategy);
            result.m_lower_bound=m_lower_bound;
            result.m_model=m_model;

            for(auto& var_wt:m_model){
                element lhs=var_wt.first;
                word_term rhs = var_wt.second;
                rhs.replace(var,tgt);
                result.m_model[lhs]=rhs;
            }

            for (const auto& we : m_eq_wes) {
                result.add_word_eq(we.replace(var, tgt));
            }
            for (const auto& we : m_diseq_wes) {
                result.add_word_diseq(we.replace(var, tgt));
            }
            for (const auto& nc : m_not_contains) {
                result.add_not_contains(nc.replace(var, tgt));
            }
            result.set_length(m_length.assign_const(var,tgt));

            return result;
        }

        state state::assign_as(const element& var, const element& as_var) const {
            SASSERT(var.typed(element::t::VAR) && as_var.typed(element::t::VAR));

            state result{m_memberships->assign_as(var, as_var)};
            result.set_strategy(m_strategy);
            result.m_lower_bound=m_lower_bound;
            result.m_lower_bound[as_var]=1;
            result.m_model=m_model;

            for(auto& var_wt:m_model){
                element lhs=var_wt.first;
                word_term rhs = var_wt.second;
                rhs.replace(var,{as_var});
                result.m_model[lhs]=rhs;
            }

            for (const auto& we : m_eq_wes) {
                result.add_word_eq(we.replace(var, {as_var}));
            }
            for (const auto& we : m_diseq_wes) {
                result.add_word_diseq(we.replace(var, {as_var}));
            }
            for (const auto& nc : m_not_contains) {
                result.add_not_contains(nc.replace(var, {as_var}));
            }

            result.set_length(m_length.assign_as(var,as_var));

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
            std::list<not_contains> ncontains;

            for (const auto& nc : m_not_contains) {
                ncontains.emplace_back(nc.replace(var, {ch, var}));
            }

            std::list<state> result;
            for (auto& m : m_memberships->assign_prefix(var, ch)) {
                state s{std::move(m)};

                s.set_strategy(m_strategy);
                s.m_lower_bound=m_lower_bound;

                for(auto& var_wt:m_model){
                    element lhs=var_wt.first;
                    word_term rhs = var_wt.second;
                    rhs.replace(var,{ch,var});
                    s.m_model[lhs]=rhs;
                }

                if(s.m_lower_bound.count(var)>0) s.m_lower_bound[var]=0;

                for (const auto& we : wes) {
                    s.add_word_eq(we);
                }
                for (const auto& wine : wines) {
                    s.add_word_diseq(wine);
                }
                for (const auto& nc : ncontains) {
                    s.add_not_contains(nc);
                }
                s.set_length(m_length.assign_prefix(var,ch));
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
            std::list<not_contains> ncontains;
            for (const auto& nc : m_not_contains) {
                ncontains.emplace_back(nc.replace(var, {prefix, var}));
            }

            std::list<state> result;
            for (auto& m : m_memberships->assign_prefix_var(var, prefix)) {
                state s{std::move(m)};
                s.set_strategy(m_strategy);
                s.m_lower_bound=m_lower_bound;

                for(auto& var_wt:m_model){
                    element lhs=var_wt.first;
                    word_term rhs = var_wt.second;
                    rhs.replace(var,{prefix,var});
                    s.m_model[lhs]=rhs;
                }

                for (const auto& we : wes) {
                    s.add_word_eq(we);
                }
                for (const auto& wine : wines) {
                    s.add_word_diseq(wine);
                }
                for (const auto& nc : ncontains) {
                    s.add_not_contains(nc);
                }
                s.set_length(m_length.assign_prefix_var(var,prefix));
                result.emplace_back(std::move(s));
            }
            return result;
        }
        bool state::is_reachable(ast_manager& m, int_expr_solver& m_int_solver, bool is_leaf) const {
            seq_util m_util_s(m);
            arith_util m_util_a(m);


            for(auto& nc:m_not_contains) {
                if(nc.is_invalid_by_syntatic_check())
                    return false;
            }

                STRACE("str", tout << __LINE__ << " enter " << __FUNCTION__ << std::endl;);
            bool on_screen=false;
            expr_ref to_check= m_length.get_path_cond(m);
//            if(on_screen) std::cout<< mk_pp(to_check,m)<<std::endl;
            if(is_leaf){
                for(auto& nc:m_not_contains){
                    expr_ref super_len{m}, sub_len{m};
                    for(auto& ele:nc.super().content()){
                        if(!super_len) super_len = ele.length_expr(m);
                        else super_len = {m_util_a.mk_add(super_len, ele.length_expr(m)), m};
                    }
                    for(auto& ele:nc.sub().content()){
                        if(!sub_len) sub_len = ele.length_expr(m);
                        else sub_len = {m_util_a.mk_add(sub_len, ele.length_expr(m)), m};
                    }
                    to_check = {m.mk_and(to_check, m_util_a.mk_gt(sub_len,super_len)),m};
                }
            }

            lbool chk_res = m_int_solver.check_sat(to_check);

            if(on_screen) std::cout<<"[is_reachable]"<<(chk_res==lbool::l_true)<<std::endl;
            STRACE("str", tout << __LINE__ << " leave " << __FUNCTION__ << std::endl;);
            return chk_res==lbool::l_true;
        };
        bool state::operator==(const state& other) const {
            return m_strategy == other.m_strategy &&
                   m_eq_wes == other.m_eq_wes &&
                   m_diseq_wes == other.m_diseq_wes &&
                   *m_memberships == *other.m_memberships;
                   //&& m_length == other.m_length;
        }




        bool length_constraints::operator==(const length_constraints& s) const{
            bool on_screen =false;
            if(on_screen) std::cout<<"PC1:"<<std::endl;
            for(auto& pc:s.m_path_cond){
                if(on_screen) pc.print(std::cout);
            }
            if(on_screen) std::cout<<"\nPC2:"<<std::endl;
            for(auto& pc:m_path_cond){
                if(on_screen) pc.print(std::cout);
            }
            if(on_screen) std::cout<<"\nThey are equal: ";
            if(on_screen) std::cout<<(s.m_path_cond==m_path_cond)<<std::endl;

            if(on_screen) std::cout<<"LC1:"<<std::endl;
            for(auto& lc:s.m_len_cons){
                if(on_screen) lc.second.print(std::cout<<lc.first<<"=");
                if(on_screen) std::cout<<" ";
            }
            if(on_screen) std::cout<<"\nLC2:"<<std::endl;
            for(auto& lc:m_len_cons){
                if(on_screen) lc.second.print(std::cout<<lc.first<<"=");
                if(on_screen) std::cout<<" ";
            }
            if(on_screen) std::cout<<"\nThey are equal: ";
            if(on_screen) std::cout<<(s.m_len_cons==m_len_cons)<<std::endl;


            return s.m_len_cons==m_len_cons && s.m_path_cond==m_path_cond;

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
            for (const auto& nc : s.m_not_contains) {
                os << nc << ")\n";
            }

            os << s.m_memberships<<std::endl;

            s.m_length.print_path_cond(os);
            s.m_length.print_len_cons(os);

            os <<"Non-empty variables: ";
            for(const auto& lb:s.m_lower_bound){
                if(lb.second>0){
                    os << lb.first<<"_cur ";
                }
            }

            os <<"\nCurrent model: "<<std::endl;
            for(const auto& model:s.m_model){
                os << model.first<<" at root = the current version of "<<model.second<<std::endl;
            }


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
                    s.m_lower_bound[x]=1;
                    s.m_lower_bound[y]=1;
                }
                result.emplace_back(std::make_pair(std::move(m), std::move(s)));
            }
            for (auto& s : m_state.assign_prefix_var(y, x)) {
                move m{m_state, move::t::TO_VAR_VAR, {y, x}};
                if(m_state.get_strategy()==state::transform_strategy::dynamic_empty_var_detection){
                    s.m_lower_bound[x]=1;
                    s.m_lower_bound[y]=1;
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
            return m_backward_def.find(s) != m_backward_def.end();
        }

        const std::list<solver::move>&
        solver::record_graph::incoming_moves(const state& s) const {
            SASSERT(contains(s));
            return m_backward_def.find(s)->second;
        }

        void solver::record_graph::add_move(move&& m, const state& s) {
            SASSERT(contains(m.m_from) && contains(s));
            m_backward_def[s].push_back(std::move(m));
        }

        const state& solver::record_graph::add_state(state&& s) {
            SASSERT(!contains(s));
            auto&& pair = std::make_pair(std::move(s), std::list<move>{});
            return m_backward_def.emplace(std::move(pair)).first->first;
        }

        solver::solver(state&& root, automaton_factory::sptr af)
                : m_rec_root{m_records.add_state(std::move(root))}, m_aut_maker{std::move(af)}{
            m_pending.push(m_rec_root);
        }

        bool solver::should_explore_all() const {
            return true;
        }

        void solver::resume(ast_manager& m, context& ctx, theory_str2& th, int_expr_solver& m_int_solver){
            m_unchecked_leaves.clear();
            if (m_pending.size() == 1 && !check_linear_membership(m_pending.top())) return;
            while (!m_pending.empty()&&m_unchecked_leaves.empty()) {
                const state& curr_s = m_pending.top();
                m_pending.pop();

                std::string action_type_string[5] = {"TO_EMPTY","TO_CONST","TO_VAR","TO_VAR_VAR","TO_CHAR_VAR"};

                STRACE("strg", tout << "from:\n" << curr_s << '\n';);
                for (auto& action : transform(curr_s)) {
                    STRACE("strg", tout <<action_type_string[static_cast<int>(action.first.m_type)]<<" ";);

                    if (m_records.contains(action.second)) {
                        m_records.add_move(std::move(action.first), action.second);
                        STRACE("strg", tout << "already visited:\n" << action.second << '\n';);
                        continue;
                    }

                    if (!action.second.is_reachable(m, m_int_solver)) {
                        STRACE("strg", tout << "not reachable:\n" << action.second << '\n';);
                        continue;
                    }

                    const state& s = m_records.add_state(std::move(action.second));
                    m_records.add_move(std::move(action.first), s);
                    if (s.unsolvable_by_inference()) {
                        STRACE("strg", tout << "failed:\n" << s << '\n';);
                        continue;
                    }

//                    if (s.in_definition_form()) {
//                        var_relation&& var_rel = s.var_rel_graph();
//                        if (var_rel.is_straight_line() &&
//                            check_straight_line_membership(var_rel, s.get_memberships())) {
//                            STRACE("str", tout << "[Success Leaf]\n" << s << '\n';);
//                            m_rec_success_leaves.emplace_back(s);
//                            m_unchecked_leaves.emplace_back(s);
//                            continue;
//                        }
//                    }


                    if (s.word_eq_num() == 0 ) {
                        STRACE("strg", tout << "[Success Leaf]\n" << s << '\n';);
                        m_rec_success_leaves.emplace_back(s);
                        m_unchecked_leaves.emplace_back(s);
                        continue;
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
                    STRACE("strg", tout << "to:\n" << s << '\n';);

                    if(s.word_eq_num() != 0)
                        m_pending.push(s);
                }

            }

        }

        bool solver::unfinished(){
            if(m_pending.empty()){
                m_status = m_rec_success_leaves.empty() ? result::UNSAT : result::SAT;
            }
            if (in_status(result::UNKNOWN)) return true;
            else return false;
        }

        std::list<state> solver::get_last_leaf_states(){
            return m_unchecked_leaves;
        }

        const void solver::print_counter_automaton(ast_manager& mgr){
            unsigned counter = 1;
            unsigned cs_curr, cs_tgt;

            std::queue<state::cref> process_queue;
            std::unordered_set<state::cref, state::hash, std::equal_to<state>> processed_states;
            std::unordered_map<state, unsigned, state::hash> mapped_states;


            for (const auto &s : get_success_leaves()) {  // assume all succ_states are different (set of states)
                mapped_states.insert({s, counter});
                process_queue.push(s);
                counter++;
            }

            std::list<solver::move> moves;
            while (!process_queue.empty()) {
                const state &curr = process_queue.front();
                cs_curr = mapped_states[curr];
                process_queue.pop();
                if (processed_states.count(curr) != 0) {
                    continue;  // already processed, skip
                } else {
                    processed_states.insert(curr);
                }
                for (auto const &m : get_graph().incoming_moves(curr)) {
                    const state &tgt = m.m_from;
                    if (mapped_states.count(tgt) == 0) {  // if tgt is new, add to mapping
                        mapped_states.insert({tgt, counter});
                        cs_tgt = counter;
                        counter++;
                    } else {
                        cs_tgt = mapped_states[tgt];
                    }

                    std::cout<<cs_curr<< " -->"<<cs_tgt<<"\t";
                    switch (m.m_type) {
                        case solver::move::t::TO_EMPTY:
                            std::cout << "[ label = TO_EMPTY\"";
                            for(auto& e:m.m_record){
                                for(auto& f:e.origin_expr()){
                                    std::cout<<mk_pp(f,mgr)<<" ";
                                }
                            }
                            std::cout<<"\n";
                            break;
                        case solver::move::t::TO_CONST:
                            std::cout << "[ label = TO_CONST\"";
                            for(auto& e:m.m_record){
                                for(auto& f:e.origin_expr()){
                                    std::cout<<mk_pp(f,mgr)<<" ";
                                }
                            }
                            std::cout<<"\n";
                            break;
                        case solver::move::t::TO_VAR:
                            std::cout << "[ label = TO_VAR\"";
                            for(auto& e:m.m_record){
                                for(auto& f:e.origin_expr()){
                                    std::cout<<mk_pp(f,mgr)<<" ";
                                }
                            }
                            std::cout<<"\n";
                            break;
                        case solver::move::t::TO_VAR_VAR:
                            std::cout << "[ label = TO_VAR_VAR\"";
                            for(auto& e:m.m_record){
                                for(auto& f:e.origin_expr()){
                                    std::cout<<mk_pp(f,mgr)<<" ";
                                }
                            }
                            std::cout<<"\n";
                            break;
                        case solver::move::t::TO_CHAR_VAR:
                            std::cout << "[ label = TO_CHAR_VAR\"";
                            for(auto& e:m.m_record){
                                for(auto& f:e.origin_expr()){
                                    std::cout<<mk_pp(f,mgr)<<" ";
                                }
                            }
                            std::cout<<"\n";
                            break;
                        default: SASSERT(false);
                    }
                    if (processed_states.count(tgt) == 0)  // if tgt is not processed yet, add to queue
                        process_queue.push(tgt);
                }
            }
        }

        result solver::check() {

            return m_status = m_rec_success_leaves.empty() ? result::UNSAT : result::SAT;
        }


        std::string element::abbreviation_to_fullname(){
            std::string ret;
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
                if(!lhs) continue;
                if (lhs->intersect_with(rhs)->is_empty()) return false;

//                if ((!lhs && rhs->is_empty()) ) return false;
//                if (lhs->intersect_with(rhs)->is_empty()) return false;
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





        const state& solver::add_sibling_ext_record(const state& s, state&& sib, const element& v) {
            const state& added = m_records.add_state(std::move(sib));
            for (const auto& m : m_records.incoming_moves(s)) {
                m_records.add_move(m.add_record(v), added);
            }
            return added;
        }

        const state& solver::add_child_var_removed(const state& s, state&& c, const element& v) {
            const state& added = m_records.add_state(std::move(c));
            m_records.add_move({s, move::t::TO_EMPTY, {v}}, added);
            return added;
        }

        void state::initialize_eq_class_map(){
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

        void str::state::merge_elements(){
            bool on_screen=false;

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
            for(auto& p:previous) {
                if (on_screen) std::cout << "prev: " << p.first << "," << p.second << std::endl;
            }

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

                    m_length.merge_list_of_elements(to_merge);

//               TODO: update membership constraints for merged elements
//                element merged(to_merge);
//                m_memberships
                }
            }
        };

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

        str::word_term str::word_term::merge_list_of_elements(const std::list<element>& to_merge) const{
            element merged(to_merge);
            std::list<element> ret;
            for(unsigned int index=0;index<length();index++){
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



        void state::remove_single_variable_word_term() {
            std::set<word_equation> updated_result;

            bool updated =true;
            bool on_screen = false;

            while (updated) {
                updated = false;
                if(on_screen){
                    std::cout << "Word equality:" << std::endl;
                    for(auto &eq:m_eq_wes) {
                        std::cout << eq << std::endl;
                    }
                    std::cout << "Word m_diseq_wes:" << std::endl;
                    for(auto &eq:m_diseq_wes) {
                        std::cout << eq << std::endl;
                    }
                }
                for(auto &eq:m_eq_wes){
                    word_equation cur=eq;
                    element source =element::null();
                    word_term target;

                    if (eq.lhs().length() == 1 && eq.lhs().has_variable() && m_memberships->get(eq.lhs().head())== nullptr ) {
                        source = eq.lhs().head();
                        target = eq.rhs();
                        updated =true;
                    } else if (eq.rhs().length() == 1 && eq.rhs().has_variable() && m_memberships->get(eq.rhs().head())== nullptr) {
                        source = eq.rhs().head();
                        target = eq.lhs();
                        updated =true;
                    }
                    if(updated){
                        m_length=m_length.add_equality(source,target);
                        if(on_screen) std::cout << "Replace " << source<< " to "<<target<<std::endl;


                        for (auto &eq2:m_eq_wes) {
                            if(eq2!=cur){
                                word_equation eq3 = eq2.replace(source, target);
                                eq3=eq3.trim_prefix();
                                if (!eq3.empty()){
                                    updated_result.insert(eq3);
                                }
                            }
                        }
                        m_eq_wes = updated_result;

                        updated_result.clear();

                        for (auto &eq2:m_diseq_wes) {
                            word_equation eq3 = eq2.replace(source, target);
                            eq3=eq3.trim_prefix();
                            updated_result.insert(eq3);
                        }
                        m_diseq_wes = updated_result;
                        updated_result.clear();

                        std::set<not_contains> updated_not_contains;
                        for (auto &nc:m_not_contains) {
                            updated_not_contains.insert(nc.replace(source, target));
                        }
                        m_not_contains = updated_not_contains;

                        break;
                    }
                }
            }
        }


        bool state::has_non_quadratic_var(const word_term& wt){
            for(const element& e:wt.content()){
                if(e.typed(element::t::VAR) && var_occurrence[e]>2){
                    return true;
                }
            }
            return false;
        }

        //best effort implementation to make the word equation quadratic
        void state::quadratify(){
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

//        result solver::split_var_empty_cases() {
//            STRACE("str", tout << "[Split Empty Variable Cases]\n";);
//            std::queue<state::cref> pending{split_first_level_var_empty()};
//            SASSERT(m_pending.empty());
//            if (in_status(result::SAT)) return m_status;
//            while (!pending.empty()) {
//                const state& curr_s = pending.front();
//                pending.pop();
//                m_pending.push(curr_s);
//                for (const auto& var : curr_s.variables()) {
//                    state&& next_s = curr_s.assign_empty(var);
//                    next_s.allow_empty_var(false);
//                    if (m_records.contains(next_s)) {
//                        for (const auto& m : m_records.incoming_moves(curr_s)) {
//                            m_records.add_move(m.add_record(var), next_s);
//                        }
//                        continue;
//                    }
//                    next_s.allow_empty_var(true);
//                    if (next_s.in_definition_form()) {
//                        var_relation&& var_rel = next_s.var_rel_graph();
//                        if (var_rel.is_straight_line() &&
//                            check_straight_line_membership(var_rel, next_s.get_memberships())) {
//                            const state& s = add_sibling_ext_record(curr_s, std::move(next_s), var);
//                            if (finish_after_found(s)) return m_status;
//                            continue;
//                        }
//                    }
//                    if (next_s.unsolvable_by_check()) {
//                        next_s.allow_empty_var(false);
//                        const state& s = add_sibling_ext_record(curr_s, std::move(next_s), var);
//                        STRACE("str", tout << "failed:\n" << s << '\n';);
//                        continue;
//                    }
//                    next_s.allow_empty_var(false);
//                    const state& s = add_sibling_ext_record(curr_s, std::move(next_s), var);
//                    pending.push(s);
//                    STRACE("str", tout << "add:\n" << s << '\n';);
//                }
//            }
//            return m_status = m_rec_success_leaves.empty() ? result::UNKNOWN : result::SAT;
//        }
//
//        std::queue<state::cref> solver::split_first_level_var_empty() {
//            std::queue<state::cref> result;
//            while (!m_pending.empty()) {
//                const state& curr_s = m_pending.top();
//                m_pending.pop();
//                for (const auto& var : curr_s.variables()) {
//                    state&& next_s = curr_s.assign_empty(var);
//                    next_s.allow_empty_var(false);
//                    if (m_records.contains(next_s)) {
//                        m_records.add_move({curr_s, move::t::TO_EMPTY, {var}}, next_s);
//                        continue;
//                    }
//                    next_s.allow_empty_var(true);
//                    if (next_s.in_definition_form()) {
//                        var_relation&& var_rel = next_s.var_rel_graph();
//                        if (var_rel.is_straight_line() &&
//                            check_straight_line_membership(var_rel, next_s.get_memberships())) {
//                            const state& s = add_child_var_removed(curr_s, std::move(next_s), var);
//                            std::queue<state::cref> empty_result;
//                            if (finish_after_found(s)) return empty_result;
//                            continue;
//                        }
//                    }
//                    if (next_s.unsolvable_by_check()) {
//                        next_s.allow_empty_var(false);
//                        const state& s = add_child_var_removed(curr_s, std::move(next_s), var);
//                        STRACE("str", tout << "failed:\n" << s << '\n';);
//                        continue;
//                    }
//                    next_s.allow_empty_var(false);
//                    const state& s = add_child_var_removed(curr_s, std::move(next_s), var);
//                    result.push(s);
//                    STRACE("str", tout << "add:\n" << s << '\n';);
//                }
//            }
//            return result;
//        }

        std::list<solver::action> solver::transform(const state& s) const {
            SASSERT(s.word_eq_num() != 0);
            SASSERT(!s.unsolvable_by_check());
            // no diseq-only handling for now
            return mk_move{s, s.smallest_eq()}();
        }

    }

}
