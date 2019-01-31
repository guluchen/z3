#include <algorithm>
#include <sstream>
#include "ast/ast_pp.h"
#include "ast/rewriter/bool_rewriter.h"
#include "smt/theory_str.h"
#include "smt/smt_context.h"
#include "smt/smt_model_generator.h"

#include "math/automata/symbolic_automata_def.h"

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

        automaton::~automaton() {
        }

        std::list<automaton::ptr> automaton::remove_prefix(const zstring& prefix) {
            std::set<state> act({get_init()});
            std::set<state> next, succ;
            std::list<automaton::ptr> ret;

            for(std::size_t i = 0; i < prefix.length(); i++) {
                next.clear();
                for(auto st : act) {
                    succ = successors(st, prefix[i]);
                    next.insert(succ.begin(), succ.end());
                }
                act = next;
            }

            for(auto st : act) {
                ptr cl = clone();
                cl->set_init(st);
                ret.emplace_back(std::move(cl));
            }
            return ret;
        }

        std::list<automaton::sptr_pair> automaton::split() {
            std::set<state> states = reachable_states();
            std::set<state> fin = get_finals();
            std::list<automaton::sptr_pair> ret;

            for (auto middle : states) {
                ptr cl1 = clone();
                ptr cl2 = clone();

                cl2->set_init(middle);
                for (auto f : fin) {
                    cl1->remove_final(f);
                }
                cl1->add_final(middle);
                ret.emplace_back(std::make_pair(std::move(cl1), std::move(cl2)));
            }
            return ret;
        }

        zaut::symbol_boolean_algebra::symbol_boolean_algebra(ast_manager& m, expr_solver& s)
                : m_ast_man{m}, m_solver{s} {}

        using zaut_sym_t = zaut::symbol_boolean_algebra::expr;

        zaut_sym_t zaut::symbol_boolean_algebra::mk_true() {
            expr_ref e{m_ast_man.mk_true(), m_ast_man};
            return sym_expr::mk_pred(e, m_ast_man.mk_bool_sort());
        }

        zaut_sym_t zaut::symbol_boolean_algebra::mk_false() {
            expr_ref e{m_ast_man.mk_false(), m_ast_man};
            return sym_expr::mk_pred(e, m_ast_man.mk_bool_sort());
        }

        zaut_sym_t zaut::symbol_boolean_algebra::mk_and(zaut_sym_t e1, zaut_sym_t e2) {
            if (e1->is_char() && e2->is_char()) {
                if (e1->get_char() == e2->get_char()) return e1;
                if (m_ast_man.are_distinct(e1->get_char(), e2->get_char())) {
                    expr_ref e{m_ast_man.mk_false(), m_ast_man};
                    return sym_expr::mk_pred(e, e1->get_sort());
                }
            }
            sort *s = e1->get_sort();
            if (m_ast_man.is_bool(s)) {
                s = e2->get_sort();
            }
            var_ref v{m_ast_man.mk_var(0, s), m_ast_man};
            expr_ref fml1 = e1->accept(v);
            expr_ref fml2 = e2->accept(v);
            if (m_ast_man.is_true(fml1)) return e2;
            if (m_ast_man.is_true(fml2)) return e1;
            if (fml1 == fml2) return e1;
            expr_ref e{m_ast_man};
            bool_rewriter{m_ast_man}.mk_and(fml1, fml2, e);
            return sym_expr::mk_pred(e, e1->get_sort());
        }

        zaut_sym_t zaut::symbol_boolean_algebra::mk_and(unsigned size, const zaut_sym_t *es) {
            switch (size) {
                case 0:
                    return mk_true();
                case 1:
                    return es[0];
                default: {
                    zaut_sym_t e = es[0];
                    for (unsigned i = 1; i < size; ++i) {
                        e = mk_and(e, es[i]);
                    }
                    return e;
                }
            }
        }

        zaut_sym_t zaut::symbol_boolean_algebra::mk_or(zaut_sym_t e1, zaut_sym_t e2) {
            if (e1->is_char() && e2->is_char() && e1->get_char() == e2->get_char()) return e1;
            if (e1 == e2) return e1;
            var_ref v(m_ast_man.mk_var(0, e1->get_sort()), m_ast_man);
            expr_ref fml1 = e1->accept(v);
            expr_ref fml2 = e2->accept(v);
            if (m_ast_man.is_false(fml1)) return e2;
            if (m_ast_man.is_false(fml2)) return e1;
            expr_ref e{m_ast_man};
            bool_rewriter{m_ast_man}.mk_or(fml1, fml2, e);
            return sym_expr::mk_pred(e, e1->get_sort());
        }

        zaut_sym_t zaut::symbol_boolean_algebra::mk_or(unsigned size, const zaut_sym_t *es) {
            switch (size) {
                case 0:
                    return mk_false();
                case 1:
                    return es[0];
                default: {
                    zaut_sym_t e = es[0];
                    for (unsigned i = 1; i < size; ++i) {
                        e = mk_or(e, es[i]);
                    }
                    return e;
                }
            }
        }

        zaut_sym_t zaut::symbol_boolean_algebra::mk_not(zaut_sym_t e) {
            var_ref v{m_ast_man.mk_var(0, e->get_sort()), m_ast_man};
            expr_ref fml{m_ast_man.mk_not(e->accept(v)), m_ast_man};
            return sym_expr::mk_pred(fml, e->get_sort());
        }

        lbool zaut::symbol_boolean_algebra::is_sat(zaut_sym_t e) {
            if (e->is_char()) return l_true;
            if (e->is_range()) {
                // TODO: check lower is below upper
            }
            expr_ref v{m_ast_man.mk_fresh_const("x", e->get_sort()), m_ast_man};
            expr_ref fml = e->accept(v);
            if (m_ast_man.is_true(fml)) return l_true;
            if (m_ast_man.is_false(fml)) return l_false;
            return m_solver.check_sat(fml);
        }

        lbool zaut::symbol_solver::check_sat(expr *const e) {
            m_kernel.push();
            m_kernel.assert_expr(e);
            lbool r = m_kernel.check();
            m_kernel.pop(1);
            return r;
        }

        zaut::zaut(internal *a, symbol_manager& s, symbol_boolean_algebra& ba, handler& h, ast_manager& m)
                : m_imp{a}, m_sym_man{s}, m_sym_ba{ba}, m_handler{h}, m_ast_man{m}, m_seq_util{m} {
        }

        bool zaut::is_deterministic() {
        }

        std::set<automaton::state> zaut::get_finals() {
            unsigned_vector fin =  m_imp->final_states();
            return std::set<state>(fin.begin(), fin.end());
        }

        automaton::ptr zaut::clone() {
            return mk_ptr(m_imp->clone());
        }

        automaton::ptr zaut::determinize() {
            return mk_ptr(m_handler.mk_deterministic(*m_imp));
        }

        automaton::ptr zaut::intersect_with(sptr other) {
            zaut *const o = static_cast<zaut *>(other.get()); // only one implementation at a time
            return mk_ptr(m_handler.mk_product(*m_imp, *o->m_imp));
        }

        automaton::ptr zaut::union_with(sptr other) {
        }

        std::list<automaton::ptr> zaut::remove_prefix(const zstring& prefix) {
        }

        std::list<automaton::sptr_pair> zaut::split() {
            return automaton::split();
        }

        void zaut::set_init(state s) {
            internal *tmp = m_imp;
            m_imp = alloc(internal, m_sym_man, s, m_imp->final_states(), transitions());
            dealloc(tmp);
        }

        void zaut::add_final(state s) {
          m_imp->add_to_final_states(s);
        }

        void zaut::remove_final(state s) {
          m_imp->remove_from_final_states(s);
        }

        zaut::moves zaut::transitions() {
          moves mvs;
          for (auto st : automaton::reachable_states()) {
              mvs.append(m_imp->get_moves_from(st));
          }
          return mvs;
        }

        std::set<automaton::state> zaut::reachable_states(state st) {
            std::vector<state> todo;
            std::set<state> ret({st});
            unsigned act;

            todo.push_back(st);
            while (!todo.empty()) {
                act = todo.back();
                todo.pop_back();
                moves const& mvs = m_imp->get_moves_from(act);
                for (unsigned i = 0; i < mvs.size(); i++) {
                    if (!mvs[i].is_epsilon()) {
                        symbol_ref con(mvs[i].t(), m_sym_man);
                        lbool is_sat = m_sym_ba.is_sat(con);
                        if (is_sat == l_undef || is_sat == l_false)
                            continue;
                    }
                    if (ret.find(mvs[i].dst()) == ret.end()) {
                        ret.emplace(mvs[i].dst());
                        todo.push_back(mvs[i].dst());
                    }
                }
            }
            return ret;
        }

        std::set<zaut::state> zaut::successors(state s) {
            moves mvs = m_imp->get_moves_from(s);
            std::set<state> succ;
            for (auto mv : mvs) {
                succ.insert(mv.dst());
            }

            return succ;
        }

        std::set<zaut::state> zaut::successors(state s, const zstring& str) {
            SASSERT(str.length() >= 1);
            moves mvs = m_imp->get_moves_from(s);

            std::set<state> succ;
            for (auto mv : mvs) {
                symbol_boolean_algebra::expr c = sym_expr::mk_char(m_ast_man, m_seq_util.str.mk_char(str, 0));
                symbol_boolean_algebra::expr tmp = m_sym_ba.mk_and(mv.t(), c);
                if(m_sym_ba.is_sat(tmp) == l_true)
                    succ.insert(mv.dst());
                dealloc(tmp);
                dealloc(c);
            }

            return succ;
        }

        std::set<automaton::len_constraint> zaut::length_constraints() {
            std::vector<state> lasso;
            std::vector<state> todo;
            unsigned act;
            std::set<std::pair<state, len_offset> > fin_offset;
            unsigned off_counter = 0;
            moves mvs;

            internal *clone = m_imp->clone();
            internal *det = m_handler.mk_deterministic(*clone);

            todo.push_back(det->init());
            while (!todo.empty()) {
                act = todo.back();
                todo.pop_back();

                if (det->is_final_state(act)) {
                    fin_offset.emplace(std::make_pair(act, off_counter));
                }

                mvs.reset();
                det->get_moves_from(act, mvs, false);
                SASSERT(mvs.size() <= 1);

                for (unsigned i = 0; i < mvs.size(); i++) {
                    symbol_ref con(mvs[i].t(), m_sym_man);
                    lbool is_sat = m_sym_ba.is_sat(con);
                    SASSERT(is_sat == l_true);

                    auto res = std::find(lasso.begin(), lasso.end(), mvs[i].dst());
                    if (res == lasso.end()) {
                        lasso.push_back(mvs[i].dst());
                        todo.push_back(mvs[i].dst());
                    } else { //lasso found
                        SASSERT(todo.empty());
                        lasso.erase(lasso.begin(), res);
                        break;
                    }
                }
                off_counter++;
            }

            unsigned period = lasso.size();
            std::set<automaton::len_constraint> ret;
            std::set<unsigned> lasso_set(lasso.begin(), lasso.end());
            for (auto pair : fin_offset) {
                if (lasso_set.find(pair.first) != lasso_set.end())
                    ret.emplace(std::make_pair(pair.second, period));
                else
                    ret.emplace(std::make_pair(pair.second, 0));
            }

            return ret;
        }

        std::ostream& zaut::display(std::ostream& out) {
            symbol_boolean_algebra::displayer d{};
            return m_imp->display(out, d);
        }

        bool zaut::operator==(automaton::sptr other) {
            zaut *const o = static_cast<zaut *>(other.get()); // only one implementation at a time
            return contains(*o) && o->contains(*this);
        }

        bool zaut::contains(const zaut& other) const {
            return m_handler.mk_difference(*other.m_imp, *m_imp)->is_empty();
        }

        automaton::ptr zaut::mk_ptr(internal *&& a) const {
            return ptr{new zaut{a, m_sym_man, m_sym_ba, m_handler, m_ast_man}};
        }

        automaton::sptr zaut::mk_sptr(internal * a) const {
            return sptr{new zaut{a, m_sym_man, m_sym_ba, m_handler, m_ast_man}};
        }

        zaut::moves zaut::transitions_skeleton() {
            std::set<state> states = reachable_states(m_imp->init());
            moves mvs;
            for (auto st : states) {
                for (auto tr : m_imp->get_moves_from(st)) {
                    if (tr.is_epsilon())
                        mvs.push_back(internal::move(m_sym_man, tr.src(), tr.dst()));
                    else
                        mvs.push_back(
                                internal::move(m_sym_man, tr.src(), tr.dst(), m_sym_ba.mk_true()));
                }
            }
            return mvs;
        }

        zaut_adaptor::zaut_adaptor(ast_manager& m, context& ctx) : m_aut_make{m}, m_ast_man{m} {
            m_sym_solver = alloc(zaut::symbol_solver, m, ctx.get_fparams());
            m_sym_ba = alloc(zaut::symbol_boolean_algebra, m, *m_sym_solver);
            m_aut_man = alloc(zaut::handler, m_sym_man, *m_sym_ba);
        }

        zaut_adaptor::~zaut_adaptor() {
            dealloc(m_aut_man);
            dealloc(m_sym_ba);
        }

        automaton::sptr zaut_adaptor::mk_from_re_expr(expr *const re) {
            if (m_re_aut_cache.find(re) != m_re_aut_cache.end()) {
                return m_re_aut_cache[re];
            }
            if (!m_aut_make.has_solver()) {
                m_aut_make.set_solver(m_sym_solver);
            }
            auto&& aut = std::make_shared<zaut>(m_aut_make(re), m_sym_man, *m_sym_ba, *m_aut_man, m_ast_man);
            auto&& pair = std::make_pair(re, std::move(aut));
            return m_re_aut_cache.emplace(std::move(pair)).first->second;
        }

        language::language(const language& other) : m_type{other.m_type} {
            if (typed(t::AUT)) m_value.aut = other.m_value.aut;
        }

        language::language(language&& other) noexcept : m_type{other.m_type} {
            if (typed(t::AUT)) m_value.aut = std::move(other.m_value.aut);
        }

        language::~language() {
            if (typed(t::AUT)) m_value.aut.~shared_ptr();
        }

        language language::intersect(const language& other) const {
            if (typed(t::AUT) && other.typed(t::AUT))
                return language{m_value.aut->intersect_with(other.value().aut)};
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
            return m_wes_to_satisfy.empty() ? word_equation::null() : *m_wes_to_satisfy.begin();
        }

        const word_equation& state::only_one_eq_left() const {
            return m_wes_to_satisfy.size() == 1 ? *m_wes_to_satisfy.begin() : word_equation::null();
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
            if (s.m_wes_to_satisfy.empty()) {
                return os << "(no word equation left)" << std::endl;
            }
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
            const element::pair& hh = m_src.heads();
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
            const element::pair& hh = m_src.heads();
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
            m_backward_def[s].push_back(std::move(m));
        }

        const state& neilsen_transforms::record_graph::add_state(state&& s) {
            SASSERT(!contains(s));
            auto&& pair = std::make_pair(std::move(s), std::list<move>{});
            return m_backward_def.emplace(std::move(pair)).first->first;
        }

        neilsen_transforms::neilsen_transforms(state&& root)
                : m_rec_root{m_records.add_state(std::move(root))} {
            m_pending.push(m_rec_root);
        }

        bool neilsen_transforms::should_explore_all() const {
            return true;
        }

        result neilsen_transforms::check(const bool split_var_empty_ahead) {
            if (in_status(result::SAT)) return m_status;
            if (split_var_empty_ahead && split_var_empty_cases() == result::SAT) return m_status;
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
                    if (s.in_solved_form()) {
                        if (finish_after_found(s)) return m_status;
                        continue;
                    }
                    const word_equation& only_one_left = s.only_one_eq_left();
                    if (only_one_left && only_one_left.in_definition_form()) {
                        // solved form check failed, the we in definition form must be recursive
                        const word_equation& last_we_recursive_def = only_one_left;
                        if (!last_we_recursive_def.definition_body().has_constant()) {
                            if (finish_after_found(s)) return m_status;
                            continue;
                        }
                        STRACE("str", tout << "failed:\n" << s << '\n';);
                        continue;
                    }
                    STRACE("str", tout << "to:\n" << s << '\n';);
                    m_pending.push(s);
                }
            }
            m_status = m_rec_success_leaves.empty() ? result::UNSAT : result::SAT;
            return m_status;
        }

        bool neilsen_transforms::finish_after_found(const state& s) {
            STRACE("str", tout << "[Success Leaf]\n" << s << '\n';);
            m_rec_success_leaves.emplace_back(s);
            if (!should_explore_all()) {
                m_status = result::SAT;
                return true;
            }
            return false;
        }

        result neilsen_transforms::split_var_empty_cases() {
            STRACE("str", tout << "[Split Empty Variable Cases]\n";);
            std::queue<state::cref> pending{split_first_level_var_empty()};
            SASSERT(m_pending.empty());
            if (in_status(result::SAT)) return m_status;
            while (!pending.empty()) {
                const state& curr_s = pending.front();
                pending.pop();
                m_pending.push(curr_s);
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
                    if (next_s.in_solved_form()) {
                        const state& s = m_records.add_state(std::move(next_s));
                        for (const auto& m : m_records.incoming_moves(curr_s)) {
                            m_records.add_move(m.add_record(var), s);
                        }
                        if (finish_after_found(s)) return m_status;
                        continue;
                    }
                    if (next_s.unsolvable_by_check()) {
                        next_s.allow_empty_var(false);
                        const state& s = m_records.add_state(std::move(next_s));
                        for (const auto& m : m_records.incoming_moves(curr_s)) {
                            m_records.add_move(m.add_record(var), s);
                        }
                        STRACE("str", tout << "failed:\n" << curr_s << '\n';);
                        continue;
                    }
                    next_s.allow_empty_var(false);
                    const state& s = m_records.add_state(std::move(next_s));
                    for (const auto& m : m_records.incoming_moves(curr_s)) {
                        m_records.add_move(m.add_record(var), s);
                    }
                    pending.push(s);
                    STRACE("str", tout << "add:\n" << s << '\n';);
                }
            }
            m_status = m_rec_success_leaves.empty() ? result::UNKNOWN : result::SAT;
            return m_status;
        }

        std::queue<state::cref> neilsen_transforms::split_first_level_var_empty() {
            std::queue<state::cref> result;
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
                    if (next_s.in_solved_form()) {
                        const state& s = m_records.add_state(std::move(next_s));
                        m_records.add_move({curr_s, move::t::TO_EMPTY, {var}}, s);
                        if (finish_after_found(s)) return {};
                        continue;
                    }
                    if (next_s.unsolvable_by_check()) {
                        next_s.allow_empty_var(false);
                        const state& s = m_records.add_state(std::move(next_s));
                        m_records.add_move({curr_s, move::t::TO_EMPTY, {var}}, s);
                        STRACE("str", tout << "failed:\n" << curr_s << '\n';);
                        continue;
                    }
                    next_s.allow_empty_var(false);
                    const state& s = m_records.add_state(std::move(next_s));
                    m_records.add_move({curr_s, move::t::TO_EMPTY, {var}}, s);
                    result.push(s);
                    STRACE("str", tout << "add:\n" << s << '\n';);
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

    std::ostream& operator<<(std::ostream& os, str::automaton::sptr a) {
        return a->display(os);
    }

    theory_str::theory_str(ast_manager& m, const theory_str_params& params)
            : theory{m.mk_family_id("seq")}, m_params{params}, m_rewrite{m}, m_util_a{m},
              m_util_s{m} {}

    void theory_str::display(std::ostream& os) const {
        os << "theory_str display" << std::endl;
    }

    void theory_str::init(context *ctx) {
        theory::init(ctx);
        STRACE("str", tout << "init\n";);
    }

    void theory_str::add_theory_assumptions(expr_ref_vector& assumptions) {
        STRACE("str", tout << "add_theory_assumptions\n";);
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
        STRACE("str", tout << "internalize_term: " << mk_pp(term, m) << '\n';);
        if (ctx.e_internalized(term)) {
            STRACE("str", tout << "done before\n";);
            return true;
        }

        const unsigned num_args = term->get_num_args();
        for (unsigned i = 0; i < num_args; i++) {
            ctx.internalize(term->get_arg(i), false);
        }

        enode *const n = ctx.mk_enode(term, false, m.is_bool(term), true);
        for (unsigned i = 0; i < num_args; i++) {
            enode *arg = n->get_arg(i);
            const theory_var& v_arg = mk_var(arg);
            (void) v_arg;
            STRACE("str", tout << "arg has theory_var #" << v_arg << '\n';);
        }
        if (m.is_bool(term)) {
            const bool_var& bv = mk_bool_var(term);
            (void) bv;
            STRACE("str", tout << "term has bool_var #" << bv << '\n';);
        } else {
            const theory_var& v = mk_var(n);
            (void) v;
            STRACE("str", tout << "term has theory_var #" << v << '\n';);
        }
        return true;
    }

    void theory_str::init_search_eh() {
        STRACE("str", tout << "init_search\n";);
    }

    void theory_str::relevant_eh(app *const n) {
        STRACE("str", tout << "relevant: " << mk_pp(n, get_manager()) << '\n';);
        if (m_util_s.str.is_extract(n)) {
            handle_substr(n);
        } else if (m_util_s.str.is_itos(n)) {
            //handle_itos(n);
        } else if (m_util_s.str.is_stoi(n)) {
            //handle_stoi(n);
        } else if (m_util_s.str.is_at(n)) {
            handle_char_at(n);
        } else if (m_util_s.str.is_replace(n)) {
            //handle_replace(n);
        } else if (m_util_s.str.is_index(n)) {
            handle_index_of(n);
        }
    }


    void theory_str::assign_eh(bool_var v, const bool is_true) {
        ast_manager& m = get_manager();
        STRACE("str", tout << "assign: bool_var #" << v << " is " << is_true << ", "
                           << mk_pp(get_context().bool_var2expr(v), m) << '\n';);
        context& ctx = get_context();
        expr *e = ctx.bool_var2expr(v);
        expr *e1 = nullptr, *e2 = nullptr;

        if (m_util_s.str.is_prefix(e, e1, e2)) {
            if (is_true) {
                handle_prefix(e);
            } else {
                TRACE("str", tout << "TODO: not prefix\n";);
            }
        } else if (m_util_s.str.is_suffix(e, e1, e2)) {
            if (is_true) {
                handle_suffix(e);
            } else {
                TRACE("str", tout << "TODO: not suffix\n";);
            }
        } else if (m_util_s.str.is_contains(e, e1, e2)) {
            if (is_true) {
                handle_contains(e);
            } else {
                TRACE("str", tout << "TODO: not contains\n";);
            }
        } else if (m_util_s.str.is_in_re(e)) {
            handle_in_re(e, is_true);
        } else {
            TRACE("str", tout << "unhandled literal " << mk_pp(e, m) << "\n";);
            UNREACHABLE();
        }
    }

    void theory_str::new_eq_eh(theory_var x, theory_var y) {
        ast_manager& m = get_manager();
        const expr_ref l{get_enode(x)->get_owner(), m};
        const expr_ref r{get_enode(y)->get_owner(), m};
        m_word_eq_todo.push_back({l, r});
        STRACE("str", tout << "new_eq: " << l << " = " << r << '\n';);
    }

    void theory_str::new_diseq_eh(theory_var x, theory_var y) {
        ast_manager& m = get_manager();
        const expr_ref l{get_enode(x)->get_owner(), m};
        const expr_ref r{get_enode(y)->get_owner(), m};
        m_word_diseq_todo.push_back({l, r});
        STRACE("str", tout << "new_diseq: " << l << " != " << r << '\n';);
    }

    bool theory_str::can_propagate() {
        return false;
    }

    void theory_str::propagate() {
        STRACE("str", tout << "propagate" << '\n';);
    }

    void theory_str::push_scope_eh() {
        m_scope_level += 1;
        m_word_eq_todo.push_scope();
        m_word_diseq_todo.push_scope();
        m_membership_todo.push_scope();
        STRACE("str", tout << "push_scope: " << m_scope_level << '\n';);
    }

    void theory_str::pop_scope_eh(const unsigned num_scopes) {
        m_scope_level -= num_scopes;
        m_word_eq_todo.pop_scope(num_scopes);
        m_word_diseq_todo.pop_scope(num_scopes);
        m_membership_todo.pop_scope(num_scopes);
        m_rewrite.reset();
        STRACE("str", tout << "pop_scope: " << num_scopes << " (back to level "
                           << m_scope_level << ")\n";);
    }

    void theory_str::reset_eh() {
        STRACE("str", tout << "reset" << '\n';);
    }

    final_check_status theory_str::final_check_eh() {
        using namespace str;
        if (m_word_eq_todo.empty()) return FC_DONE;
        TRACE("str", tout << "final_check: level " << get_context().get_scope_level() << '\n';);

        state&& root = mk_state_from_todo();
        STRACE("str", tout << "root built:\n" << root << '\n';);
        if (root.unsolvable_by_inference()) {
            block_curr_assignment();
            return FC_CONTINUE;
        }
        neilsen_transforms solver{std::move(root)};
        if (solver.check() == result::SAT) {
            TRACE("str", tout << "final_check ends\n";);
            return FC_DONE;
        }
        block_curr_assignment();
        TRACE("str", tout << "final_check ends\n";);
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
        STRACE("str", tout << "init_model\n";);
    }

    void theory_str::finalize_model(model_generator& mg) {
        STRACE("str", tout << "finalize_model\n";);
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

    expr_ref
    theory_str::mk_skolem(symbol const& name, expr *e1, expr *e2, expr *e3, expr *e4, sort *range) {
        ast_manager& m = get_manager();
        expr *es[4] = {e1, e2, e3, e4};
        unsigned len = e4 ? 4 : (e3 ? 3 : (e2 ? 2 : 1));

        if (!range) {
            range = m.get_sort(e1);
        }
        return expr_ref(m_util_s.mk_skolem(name, len, es, range), m);
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

    str::language theory_str::mk_language(expr *const e) {
        using namespace str;
        if (!m_aut_imp) {
            m_aut_imp = std::unique_ptr<zaut_adaptor>(
                    new zaut_adaptor{get_manager(), get_context()});
        }
        return language{m_aut_imp->mk_from_re_expr(e)->determinize()};
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
        return word_term::from_variable({ss.str().data()});
    }

    str::state theory_str::mk_state_from_todo() {
        str::state result;
        STRACE("str", tout << "[Build State]\nword equation todo:\n";);
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
        STRACE("str", tout << "membership todo:\n";);
        STRACE("str", if (m_membership_todo.empty()) tout << "--\n";);
        for (const auto& m : m_membership_todo) {
            auto aut = mk_language(m.second); // TODO: for temporary testing
            STRACE("str", tout << m.first << " is in " << m.second << '\n';);
        }
        return result;
    }

    void theory_str::add_axiom(expr *const e) {
        if (e == nullptr || get_manager().is_true(e)) return;

        context& ctx = get_context();
        SASSERT(!ctx.b_internalized(e));
        ctx.internalize(e, false);
        literal l{ctx.get_literal(e)};
        ctx.mark_as_relevant(l);
        ctx.mk_th_axiom(get_id(), 1, &l);
        STRACE("str", ctx.display_literal_verbose(tout << "[Assert]\n", l) << '\n';);
    }

    void theory_str::add_clause(std::initializer_list<literal> ls) {
        context& ctx = get_context();
        literal_vector lv;
        for (const auto& l : ls) {
            if (l != null_literal && l != false_literal) {
                ctx.mark_as_relevant(l);
                lv.push_back(l);
            }
        }
        ctx.mk_th_axiom(get_id(), lv.size(), lv.c_ptr());
        STRACE("str", ctx.display_literals_verbose(tout << "[Assert]\n", lv) << '\n';);
    }

    /*
      Note: this is copied and modified from theory_seq.cpp
      Let e = at(s, i)
        0 <= i < len(s)  ->  s = xey /\ len(x) = i /\ len(e) = 1
        i < 0 \/ i >= len(s)  ->  e = empty
    */
    void theory_str::handle_char_at(expr *e) {
        ast_manager& m = get_manager();
        expr *s = nullptr, *i = nullptr;
        VERIFY(m_util_s.str.is_at(e, s, i));
        expr_ref len_e(m_util_s.str.mk_length(e), m);
        expr_ref len_s(m_util_s.str.mk_length(s), m);
        expr_ref zero(m_util_a.mk_int(0), m);
        expr_ref one(m_util_a.mk_int(1), m);
        expr_ref x = mk_skolem(symbol("m_char_at_left"), s, i);
        expr_ref y = mk_skolem(symbol("m_char_at_right"), s, mk_sub(mk_sub(len_s, i), one));
        expr_ref xey(m_util_s.str.mk_concat(x, m_util_s.str.mk_concat(e, y)), m);
        expr_ref len_x(m_util_s.str.mk_length(x), m);
        expr_ref emp(m_util_s.str.mk_empty(m.get_sort(e)), m);

        literal i_ge_0 = mk_literal(m_util_a.mk_ge(i, zero));
        literal i_ge_len_s = mk_literal(m_util_a.mk_ge(mk_sub(i, m_util_s.str.mk_length(s)), zero));

        add_clause({~i_ge_0, i_ge_len_s, mk_eq(s, xey, false)});
        add_clause({~i_ge_0, i_ge_len_s, mk_eq(one, len_e, false)});
        add_clause({~i_ge_0, i_ge_len_s, mk_eq(i, len_x, false)});

        add_clause({i_ge_0, mk_eq(e, emp, false)});
        add_clause({~i_ge_len_s, mk_eq(e, emp, false)});
    }

    /*
      Note: this is copied and modified from theory_seq.cpp
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
    void theory_str::handle_substr(expr *e) {
        ast_manager& m = get_manager();
        expr *s = nullptr, *i = nullptr, *l = nullptr;
        VERIFY(m_util_s.str.is_extract(e, s, i, l));

        expr_ref x(mk_skolem(symbol("m_substr_left"), s, i), m);
        expr_ref ls(m_util_s.str.mk_length(s), m);
        expr_ref lx(m_util_s.str.mk_length(x), m);
        expr_ref le(m_util_s.str.mk_length(e), m);
        expr_ref ls_minus_i_l(mk_sub(mk_sub(ls, i), l), m);
        expr_ref y(mk_skolem(symbol("m_substr_right"), s, ls_minus_i_l), m);
        expr_ref xe(m_util_s.str.mk_concat(x, e), m);
        expr_ref xey(m_util_s.str.mk_concat(x, e, y), m);
        expr_ref zero(m_util_a.mk_int(0), m);

        literal i_ge_0 = mk_literal(m_util_a.mk_ge(i, zero));
        literal ls_le_i = mk_literal(m_util_a.mk_le(mk_sub(i, ls), zero));
        literal li_ge_ls = mk_literal(m_util_a.mk_ge(ls_minus_i_l, zero));
        literal l_ge_zero = mk_literal(m_util_a.mk_ge(l, zero));
        literal ls_le_0 = mk_literal(m_util_a.mk_le(ls, zero));

        add_clause({~i_ge_0, ~ls_le_i, mk_eq(xey, s, false)});
        add_clause({~i_ge_0, ~ls_le_i, mk_eq(lx, i, false)});
        add_clause({~i_ge_0, ~ls_le_i, ~l_ge_zero, ~li_ge_ls, mk_eq(le, l, false)});
        add_clause({~i_ge_0, ~ls_le_i, li_ge_ls, mk_eq(le, mk_sub(ls, i), false)});
        add_clause({~i_ge_0, ~ls_le_i, l_ge_zero, mk_eq(le, zero, false)});
        add_clause({i_ge_0, mk_eq(le, zero, false)});
        add_clause({ls_le_i, mk_eq(le, zero, false)});
        add_clause({~ls_le_0, mk_eq(le, zero, false)});
    }

    void theory_str::handle_index_of(expr *e) {
        ast_manager& m = get_manager();
        expr *s = nullptr, *t = nullptr, *offset = nullptr;
        rational r;
        VERIFY(m_util_s.str.is_index(e, t, s) || m_util_s.str.is_index(e, t, s, offset));

        expr_ref minus_one(m_util_a.mk_int(-1), m);
        expr_ref zero(m_util_a.mk_int(0), m);

        expr_ref emp(m_util_s.str.mk_empty(m.get_sort(t)), m);

        literal cnt = mk_literal(m_util_s.str.mk_contains(t, s));
        literal i_eq_m1 = mk_eq(e, minus_one, false);
        literal i_eq_0 = mk_eq(e, zero, false);
        literal s_eq_empty = mk_eq(s, emp, false);
        literal t_eq_empty = mk_eq(t, emp, false);

        add_clause({cnt, i_eq_m1});
        add_clause({~t_eq_empty, s_eq_empty, i_eq_m1});

        if (!offset || (m_util_a.is_numeral(offset, r) && r.is_zero())) {
            expr_ref x = mk_skolem(symbol("m_indexof_left"), t, s);
            expr_ref y = mk_skolem(symbol("m_indexof_right"), t, s);
            expr_ref xsy(m_util_s.str.mk_concat(x, s, y), m);
            expr_ref lenx(m_util_s.str.mk_length(x), m);
            add_clause({~s_eq_empty, i_eq_0});
            add_clause({~cnt, s_eq_empty, mk_eq(t, xsy, false)});
            add_clause({~cnt, s_eq_empty, mk_eq(e, lenx, false)});
            add_clause({~cnt, mk_literal(m_util_a.mk_ge(e, zero))});
            // tightest_prefix(s, x);
        } else {
            expr_ref len_t(m_util_s.str.mk_length(t), m);
            literal offset_ge_len = mk_literal(m_util_a.mk_ge(mk_sub(offset, len_t), zero));
            literal offset_le_len = mk_literal(m_util_a.mk_le(mk_sub(offset, len_t), zero));
            literal i_eq_offset = mk_eq(e, offset, false);
            add_clause({~offset_ge_len, s_eq_empty, i_eq_m1});
            add_clause({offset_le_len, i_eq_m1});
            add_clause({~offset_ge_len, ~offset_le_len, ~s_eq_empty, i_eq_offset});

            expr_ref x = mk_skolem(symbol("m_indexof_left"), t, s, offset);
            expr_ref y = mk_skolem(symbol("m_indexof_right"), t, s, offset);
            expr_ref indexof0(m_util_s.str.mk_index(y, s, zero), m);
            expr_ref offset_p_indexof0(m_util_a.mk_add(offset, indexof0), m);
            literal offset_ge_0 = mk_literal(m_util_a.mk_ge(offset, zero));

            add_clause(
                    {~offset_ge_0, offset_ge_len, mk_eq(t, m_util_s.str.mk_concat(x, y), false)});
            add_clause(
                    {~offset_ge_0, offset_ge_len, mk_eq(m_util_s.str.mk_length(x), offset, false)});
            add_clause({~offset_ge_0, offset_ge_len, ~mk_eq(indexof0, minus_one, false), i_eq_m1});
            add_clause({~offset_ge_0, offset_ge_len, ~mk_literal(m_util_a.mk_ge(indexof0, zero)),
                        mk_eq(offset_p_indexof0, e, false)});

            // offset < 0 => -1 = i
            add_clause({offset_ge_0, i_eq_m1});
        }
    }

    // e = prefix(x, y), check if x is a prefix of y
    void theory_str::handle_prefix(expr *e) {
        ast_manager& m = get_manager();
        expr *x = nullptr, *y = nullptr;
        VERIFY(m_util_s.str.is_prefix(e, x, y));

        expr_ref s = mk_skolem(symbol("m_prefix_right"), x, y);
        expr_ref xs(m_util_s.str.mk_concat(x, s), m);

        add_clause({mk_eq(y, xs, false)});
    }

    // e = suffix(x, y), check if x is a suffix of y
    void theory_str::handle_suffix(expr *e) {
        ast_manager& m = get_manager();
        expr *x = nullptr, *y = nullptr;
        VERIFY(m_util_s.str.is_suffix(e, x, y));

        expr_ref p = mk_skolem(symbol("m_suffix_left"), x, y);
        expr_ref px(m_util_s.str.mk_concat(p, x), m);

        add_clause({mk_eq(y, px, false)});
    }

    // e = contains(x, y)
    void theory_str::handle_contains(expr *e) {
        ast_manager& m = get_manager();
        expr *x = nullptr, *y = nullptr;
        VERIFY(m_util_s.str.is_contains(e, x, y));

        expr_ref p = mk_skolem(symbol("m_contains_left"), x, y);
        expr_ref s = mk_skolem(symbol("m_contains_right"), x, y);
        expr_ref pys(m_util_s.str.mk_concat(m_util_s.str.mk_concat(p, y), s), m);

        add_clause({mk_eq(x, pys, false)});
    }

    void theory_str::handle_in_re(expr *const e, const bool is_true) {
        expr *s = nullptr, *re = nullptr;
        VERIFY(m_util_s.str.is_in_re(e, s, re));
        ast_manager& m = get_manager();

        expr_ref tmp{e, m};
        m_rewrite(tmp);
        if ((m.is_false(tmp) && is_true) || (m.is_true(tmp) && !is_true)) {
            literal_vector lv;
            lv.push_back(is_true ? mk_literal(e) : ~mk_literal(e));
            set_conflict(lv);
            return;
        }
        expr_ref r{re, m};
        context& ctx = get_context();
        literal l = ctx.get_literal(e);
        if (!is_true) {
            r = m_util_s.re.mk_complement(re);
            l.neg();
        }
        m_membership_todo.push_back({{s, m}, r});
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
            add_axiom(refinement);
        }
    }

    void theory_str::dump_assignments() const {
        STRACE("str", \
                ast_manager& m = get_manager();
                context& ctx = get_context();
                tout << "dump all assignments:\n";
                expr_ref_vector assignments{m};
                ctx.get_assignments(assignments);
                for (expr *const e : assignments) {
                    tout << mk_pp(e, m) << (ctx.is_relevant(e) ? "\n" : " (not relevant)\n");
                }
        );
    }

}
