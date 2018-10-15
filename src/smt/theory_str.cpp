#include <algorithm>
#include <queue>
#include <map>
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

#define RESET   "\033[0m"
#define BLACK   "\033[30m"      /* Black */
#define RED     "\033[31m"      /* Red */
#define GREEN   "\033[32m"      /* Green */
#define YELLOW  "\033[33m"      /* Yellow */
#define BLUE    "\033[34m"      /* Blue */
#define MAGENTA "\033[35m"      /* Magenta */
#define CYAN    "\033[36m"      /* Cyan */
#define WHITE   "\033[37m"      /* White */
#define BOLDBLACK   "\033[1m\033[30m"      /* Bold Black */
#define BOLDRED     "\033[1m\033[31m"      /* Bold Red */
#define BOLDGREEN   "\033[1m\033[32m"      /* Bold Green */
#define BOLDYELLOW  "\033[1m\033[33m"      /* Bold Yellow */
#define BOLDBLUE    "\033[1m\033[34m"      /* Bold Blue */
#define BOLDMAGENTA "\033[1m\033[35m"      /* Bold Magenta */
#define BOLDCYAN    "\033[1m\033[36m"      /* Bold Cyan */
#define BOLDWHITE   "\033[1m\033[37m"      /* Bold White */

namespace smt {

    const element& element::null() {
        static const element e{element_t::NONE, ""};
        return e;
    }

    const bool element::operator==(const element& other) const {
        if (other.m_type != m_type) return false;
        return other.m_value == m_value;
    }

    const bool element::operator<(const element& other) const {
        if (m_type < other.m_type) return true;
        if (m_type > other.m_type) return false;
        return m_value < other.m_value;
    }

    std::ostream& operator<<(std::ostream& os, const element& s) {
        if (s.m_type == element_t::VAR) {
            os << BOLDGREEN << s.value() << " " << RESET;
        } else {
            os << BLUE << s.value() << " " << RESET;
        }
        return os;
    }

    const word_term& word_term::null() {
        static const word_term w;
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

    word_term::word_term(const smt::word_term& other) {
        m_elements.insert(m_elements.begin(), other.m_elements.begin(), other.m_elements.end());
    }

    const std::set<element> word_term::variables() const {
        std::set<element> result;
        for (const auto& e : m_elements) {
            if (e.type() == element_t::VAR) {
                result.insert(e);
            }
        }
        return result;
    }

    const bool word_term::has_constant() const {
        for (const auto& e : m_elements) {
            if (e.type() == element_t::CONST) {
                return true;
            }
        }
        return false;
    }

    const bool word_term::check_front(const element_t& t) const {
        return peek_front().type() == t;
    }

    const element& word_term::peek_front() const {
        // TODO: review the empty case
        return *m_elements.begin();
    }

    void word_term::remove_front() {
        // TODO: review the empty case
        m_elements.pop_front();
    }

    void word_term::concat(const word_term& other) {
        m_elements.insert(m_elements.end(), other.m_elements.begin(), other.m_elements.end());
    }

    void word_term::replace(const element& tgt, const word_term& subst) {
        auto find_it = std::find(m_elements.begin(), m_elements.end(), tgt);
        while (find_it != m_elements.end()) {
            m_elements.insert(find_it, subst.m_elements.begin(), subst.m_elements.end());
            m_elements.erase(find_it++);
            find_it = std::find(find_it, m_elements.end(), tgt);
        }
    }

    const bool word_term::operator<(const word_term& other) const {
        if (m_elements.size() < other.m_elements.size()) return true;
        if (m_elements.size() > other.m_elements.size()) return false;
        auto e_it_other = other.m_elements.begin();
        for (const auto& e : m_elements) {
            if (e < *e_it_other) return true;
            if (*e_it_other < e) return false;
            e_it_other++;
        }
        return false;
    }

    std::ostream& operator<<(std::ostream& os, const word_term& w) {
        for (const auto& e : w.m_elements) {
            os << e;
        }
        return os;
    }

    word_equation::word_equation(const smt::word_term& lhs, const smt::word_term& rhs) {
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

    const element& word_equation::def_var() const {
        if (m_lhs.length() == 1 && m_lhs.check_front(element_t::VAR)) {
            return m_lhs.peek_front();
        }
        if (m_rhs.length() == 1 && m_rhs.check_front(element_t::VAR)) {
            return m_rhs.peek_front();
        }
        return element::null();
    }

    const word_term& word_equation::def_body() const {
        if (m_lhs.length() == 1 && m_lhs.check_front(element_t::VAR)) {
            return m_rhs;
        }
        if (m_rhs.length() == 1 && m_rhs.check_front(element_t::VAR)) {
            return m_lhs;
        }
        return word_term::null();
    }

    const bool word_equation::is_simply_unsat(const bool allow_empty_assign) const {
        if (allow_empty_assign) {
            if ((m_lhs.length() == 0 && m_rhs.has_constant()) ||
                (m_rhs.length() == 0 && m_lhs.has_constant())) {
                return true;
            }
        } else {
            if ((m_lhs.length() == 0 && m_rhs.length() != 0) ||
                (m_lhs.length() != 0 && m_rhs.length() == 0)) {
                return true;
            }
            // check inconsistent heads when having same length
            const auto& lh = m_lhs.peek_front();
            const auto& rh = m_rhs.peek_front();
            if (check_heads(element_t::CONST, element_t::CONST) && lh.value() != rh.value())
                return true;
        }
        return false;
    }

    const bool word_equation::is_in_definition_form() const {
        return !(def_var() == element::null());
    }

    const bool word_equation::check_heads(const element_t& lht, const element_t& rht) const {
        return m_lhs.check_front(lht) && m_rhs.check_front(rht);
    }

    void word_equation::trim_prefix() {
        while (m_lhs.peek_front() == m_rhs.peek_front()) {
            m_lhs.remove_front();
            m_rhs.remove_front();
        }
    }

    void word_equation::replace(const element& tgt, const word_term& subst) {
        m_lhs.replace(tgt, subst);
        m_rhs.replace(tgt, subst);
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

    const std::set<element> state::variables() const {
        std::set<element> result;
        for (const auto& we : m_word_equations) {
            for (const auto& v : we.variables()) {
                result.insert(v);
            }
        }
        return result;
    }

    const bool state::is_inconsistent() const {
        for (const auto& we : m_word_equations) {
            if (we.is_simply_unsat()) return true;
        }
        return false;
    }

    const bool state::is_in_definition_form() const {
        for (const auto& we : m_word_equations) {
            if (!we.is_in_definition_form()) return false;
        }
        return true;
    }

    const bool state::is_in_solved_form() const {
        if (is_in_definition_form() && definition_form_acyclic()) return true;
        for (const auto& we : m_word_equations) {
            if (!(we.lhs().length() == 0 && we.rhs().length() == 0)) {
                return false;
            }
        }
        return true;
    }

    void state::add_word_equation(word_equation we) {
        we.trim_prefix();
        m_word_equations.insert(we);
    }

    state state::replace(const element& tgt, const word_term& subst) const {
        state result;
        for (auto we : m_word_equations) {
            we.replace(tgt, subst);
            result.add_word_equation(we);
        }
        return result;
    }

    const std::list<state> state::transform() const {
        std::list<state> result;
        if (is_inconsistent()) return result;

        const word_equation& curr_we = *m_word_equations.begin();
        const element& x = curr_we.lhs().peek_front();
        const element& y = curr_we.rhs().peek_front();
        if (curr_we.check_heads(element_t::VAR, element_t::VAR)) {
            const word_term yx{std::list<element>{y, x}};
            result.push_back(replace(x, yx));
            const word_term xy{std::list<element>{x, y}};
            result.push_back(replace(y, xy));
            const word_term single_y{std::list<element>{y}};
            result.push_back(replace(x, single_y));
        } else {
            const bool var_cons_headed = curr_we.lhs().check_front(element_t::VAR);
            const element& v = var_cons_headed ? x : y;
            const element& c = var_cons_headed ? y : x;
            const word_term cv{std::list<element>{c, v}};
            result.push_back(replace(v, cv));
            const word_term single_c{std::list<element>{c}};
            result.push_back(replace(v, single_c));
        }
        return result;
    }

    const bool state::operator<(const state& other) const {
        if (m_word_equations.size() < other.m_word_equations.size()) return true;
        if (m_word_equations.size() > other.m_word_equations.size()) return false;
        auto we_it_other = other.m_word_equations.begin();
        for (const auto& we : m_word_equations) {
            if (we < *we_it_other) return true;
            if (*we_it_other < we) return false;
            we_it_other++;
        }
        return false;
    }

    std::ostream& operator<<(std::ostream& os, const state& s) {
        for (const auto& we : s.m_word_equations) {
            os << we << std::endl;
        }
        return os;
    }

    const bool state::dag_def_check_node(const def_graph& graph, const def_node& node,
                                         def_nodes& marked, def_nodes& checked) {
        if (checked.find(node) != checked.end()) {
            return true;
        }
        if (marked.find(node) != marked.end()) {
            return false;
        }
        marked.insert(node);
        auto next_it = graph.find(node);
        if (next_it != graph.end()) {
            for (const auto& next : next_it->second) {
                if (!dag_def_check_node(graph, next, marked, checked)) return false;
            }
        }
        checked.insert(node);
        return true;
    }

    const bool state::definition_form_acyclic() const {
        def_graph graph;
        def_nodes marked;
        def_nodes checked;
        for (const auto& we : m_word_equations) {
            const def_node& node = we.def_var();
            if (graph.find(node) != graph.end()) {
                return false; // definition not unique
            }
            graph[node] = we.def_body().variables();
        }
        for (const auto& kv : graph) {
            if (!dag_def_check_node(graph, kv.first, marked, checked)) return false;
        }
        return true;
    }

    neilson_based_solver::neilson_based_solver(const state& root) : m_solution_found{false} {
        m_pending.push(root);
    }

    void neilson_based_solver::consider_var_empty_cases() {
        while (!m_pending.empty()) {
            state curr_s = m_pending.top();
            m_pending.pop();
            if (curr_s.is_in_solved_form()) {
                m_solution_found = true;
                return;
            }
            if (!curr_s.is_inconsistent() && m_processed.find(curr_s) == m_processed.end()) {
                std::cout << curr_s << std::endl;
                m_processed.insert(curr_s);
                for (const auto& var : curr_s.variables()) {
                    word_term empty;
                    m_pending.push(curr_s.replace(var, empty));
                }
            }
        }
        for (const auto& s : m_processed) {
            m_pending.push(s);
        }
    }

    void neilson_based_solver::check_sat() {
        std::cout << "start the check SAT procedure" << std::endl;
        while (!m_pending.empty()) {
            state curr_s = m_pending.top();
            m_pending.pop();
            std::cout << "from " << curr_s << std::endl;
            for (const auto& next : curr_s.transform()) {
                if (m_processed.find(next) == m_processed.end() && !next.is_inconsistent()) {
                    if (next.is_in_solved_form()) {
                        std::cout << "to " << next << RED << "(solved form)" << RESET << std::endl;
                        m_solution_found = true;
                        return;
                    }
                    std::cout << "to " << next << std::endl;
                    m_processed.insert(next);
                    m_pending.push(next);
                }
            }
        }
    }

    theory_str::theory_str(ast_manager& m, theory_str_params const& params) :
            theory{m.mk_family_id("seq")}, m_scope_level{0}, m_params{params} {
    }

    void theory_str::display(std::ostream& os) const {
        os << "TODO: theory_str display" << std::endl;
    }

    void theory_str::init(context *ctx) {
        theory::init(ctx);
    }

    bool theory_str::internalize_atom(app *atom, bool gate_ctx) {
        return internalize_term(atom);
    }

    bool theory_str::internalize_term(app *term) {
        ast_manager& m = get_manager();
        context& ctx = get_context();
        SASSERT(term->get_family_id() == get_family_id());
        TRACE("str", tout << "internalizing term: " << mk_ismt2_pp(term, m) << std::endl;);

        unsigned num_args = term->get_num_args();
        for (unsigned i = 0; i < num_args; ++i) {
            ctx.internalize(term->get_arg(i), false);
        }
        if (ctx.e_internalized(term)) {
            enode *e = ctx.get_enode(term);
            mk_var(e);
            return true;
        }
        // std::cout << "the term: " << mk_ismt2_pp(term, m) << " is bool? " << m.is_bool(term)
        // << std::endl;
        enode *e = ctx.mk_enode(term, false, m.is_bool(term), true);
        if (m.is_bool(term)) {
            bool_var bv = ctx.mk_bool_var(term);
            ctx.set_var_theory(bv, get_id());
            ctx.set_enode_flag(bv, true);
        }
        // make sure every argument is attached to a theory variable
        for (unsigned i = 0; i < num_args; ++i) {
            enode *arg = e->get_arg(i);
            theory_var v_arg = mk_var(arg);
            TRACE("str", tout << "arg has theory var #" << v_arg << std::endl;);
            (void) v_arg;
        }

        theory_var v = mk_var(e);
        TRACE("str", tout << "term has theory var #" << v << std::endl;);
        return true;
    }

    theory_var theory_str::mk_var(enode *n) {
        TRACE("str", tout << "mk_var for " << mk_pp(n->get_owner(), get_manager()) << std::endl;);
        if (!(is_theory_str_term(n->get_owner()))) {
            return null_theory_var;
        }
        if (is_attached_to_var(n)) {
            TRACE("str", tout << "already attached to theory var v#" << n->get_th_var(get_id())
                              << std::endl;);
            return n->get_th_var(get_id());
        } else {
            theory_var v = theory::mk_var(n);
            TRACE("str", tout << "new theory var v#" << v << " find " << get_enode(v)
                              << std::endl;);
            get_context().attach_th_var(n, this, v);
            get_context().mark_as_relevant(n);
            return v;
        }
    }

    model_value_proc *theory_str::mk_value(enode *n, model_generator& mg) {
        ast_manager& m = get_manager();
        TRACE("str", tout << "mk_value for: " << mk_ismt2_pp(n->get_owner(), m) << " (sort "
                          << mk_ismt2_pp(m.get_sort(n->get_owner()), m) << ")" << std::endl;);
        app_ref owner{m};
        owner = n->get_owner();

        // if the owner is not internalized, it doesn't have an enode associated.
        SASSERT(get_context().e_internalized(owner));
        return alloc(expr_wrapper_proc, owner);
    }

    void theory_str::add_theory_assumptions(expr_ref_vector& assumptions) {
        TRACE("str", tout << "add theory assumption for theory_str" << std::endl;);
    }

    lbool theory_str::validate_unsat_core(expr_ref_vector& unsat_core) {
        return l_undef;
    }

    void theory_str::new_eq_eh(theory_var x, theory_var y) {
        ast_manager& m = get_manager();
        enode *n1 = get_enode(x);
        enode *n2 = get_enode(y);
        expr_ref e1{n1->get_owner(), m};
        expr_ref e2{n2->get_owner(), m};
        expr_pair we{e1, e2};
        // std::cout << "new equality " << get_context().get_scope_level() << ": "
        // << mk_ismt2_pp(n1->get_owner(), m) << " = " << mk_ismt2_pp(n2->get_owner(), m)
        // << std::endl;

        m_we_expr_memo.push_back(we);
        TRACE("str", tout << "new eq: " << mk_ismt2_pp(n1->get_owner(), m) << " = "
                          << mk_ismt2_pp(n2->get_owner(), m) << std::endl;);
    }

    void theory_str::new_diseq_eh(theory_var x, theory_var y) {
        ast_manager& m = get_manager();
        enode *n1 = get_enode(x);
        enode *n2 = get_enode(y);
        expr_ref e1{n1->get_owner(), m};
        expr_ref e2{n2->get_owner(), m};
        expr_pair wine{e1, e2};
        // std::cout << "new disequality " << get_context().get_scope_level() << ": "
        // << mk_ismt2_pp(n1->get_owner(), m) << " = " << mk_ismt2_pp(n2->get_owner(), m)
        // << std::endl;

        m_wine_expr_memo.push_back(wine);
        TRACE("str", tout << "new diseq: " << mk_ismt2_pp(n1->get_owner(), m) << " = "
                          << mk_ismt2_pp(n2->get_owner(), m) << std::endl;);
    }

    void theory_str::init_search_eh() {
    }

    void theory_str::relevant_eh(app *n) {
        TRACE("str", tout << "relevant: " << mk_ismt2_pp(n, get_manager()) << std::endl;);
    }

    void theory_str::assign_eh(bool_var v, bool is_true) {
        // YFC: membership constraint goes here
        std::cout << "assign: v" << v << " #" << get_context().bool_var2expr(v)->get_id()
                  << " is_true: " << is_true << std::endl;

        TRACE("str", tout << "assign: v" << v << "--> "
                          << mk_ismt2_pp(get_context().bool_var2expr(v), get_manager())
                          << " is_true: " << is_true << std::endl;);
    }

    void theory_str::push_scope_eh() {
        m_scope_level += 1;
        m_we_expr_memo.push_scope();
        m_wine_expr_memo.push_scope();
        // std::cout << "push to " << m_scope_level << std::endl;
        TRACE("str", tout << "push to " << m_scope_level << std::endl;);
    }

    void theory_str::pop_scope_eh(unsigned num_scopes) {
        m_scope_level -= num_scopes;
        m_we_expr_memo.pop_scope(num_scopes);
        m_wine_expr_memo.pop_scope(num_scopes);

        // std::cout << "pop " << num_scopes << " to " << m_scope_level << std::endl;
        TRACE("str", tout << "pop " << num_scopes << " to " << m_scope_level << std::endl;);
    }

    void theory_str::reset_eh() {
        TRACE("str", tout << "resetting" << std::endl;);
    }

    final_check_status theory_str::final_check_eh() {
        context& ctx = get_context();
        std::cout << "final_check at level: " << ctx.get_scope_level() << "\n" << std::endl;
        std::cout << "identified root states (color: " << BOLDGREEN << "GREEN" << RESET
                  << " for variables and " << BLUE << "BLUE" << RESET << " for constants"
                  << std::endl;

        const state& search_root = build_state_from_memo();
        neilson_based_solver solver{search_root};
        solver.consider_var_empty_cases();
        if (solver.solution_found()) return FC_DONE;
        solver.check_sat();
        if (solver.solution_found()) return FC_DONE;

        if (block_dpllt_assignment_from_memo()) {
            TRACE("str", tout << "final check" << std::endl;);
            return FC_CONTINUE;
        } else {
            TRACE_CODE(dump_assignments(););
            return FC_DONE;
        }
    }

    bool theory_str::can_propagate() {
        return false;
    }

    void theory_str::propagate() {
        TRACE("str", tout << "propagating..." << std::endl;);
    }

    void theory_str::init_model(model_generator& mg) {
        TRACE("str", tout << "initializing model" << std::endl;);
    }

    void theory_str::finalize_model(model_generator& mg) {
    }

    void theory_str::assert_axiom(expr *const e) {
        if (e == nullptr) return;
        if (get_manager().is_true(e)) return;

        ast_manager& m = get_manager();
        context& ctx = get_context();
        TRACE("str", tout << "asserting " << mk_ismt2_pp(e, m) << std::endl;);

        expr_ref ex{e, m};
        if (!ctx.b_internalized(ex)) {
            ctx.internalize(ex, false);
        }
        literal lit(ctx.get_literal(ex));
        ctx.mark_as_relevant(lit);
        ctx.mk_th_axiom(get_id(), 1, &lit);
    }

    void theory_str::dump_assignments() {
        TRACE_CODE(
                ast_manager& m = get_manager();
                context& ctx = get_context();
                tout << "dumping all assignments:" << std::endl;
                expr_ref_vector assignments{m};
                ctx.get_assignments(assignments);
                for (expr *const e : assignments) {
                    tout << mk_ismt2_pp(e, m) << (ctx.is_relevant(e) ? "" : " (NOT REL)")
                         << std::endl;
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

    word_term theory_str::get_word_term(expr *const e) const {
        if (get_decl_kind(e) == OP_STRING_CONST) {
            std::stringstream ss;
            ss << mk_ismt2_pp(e, get_manager());
            return word_term::of_string(ss.str());
        }
        if (get_decl_kind(e) == OP_SEQ_CONCAT) {
            word_term result;
            unsigned num_args = to_app(e)->get_num_args();
            for (unsigned i = 0; i < num_args; i++) {
                const word_term& sub_term = get_word_term(to_app(e)->get_arg(i));
                result.concat(sub_term);
            }
            return result;
        }
        std::stringstream ss;
        ss << mk_ismt2_pp(e, get_manager());
        return word_term::of_variable(ss.str());
    }

    state theory_str::build_state_from_memo() const {
        ast_manager& m = get_manager();
        state result;
        for (const auto& memo : m_we_expr_memo) {
            std::cout << "formula:" << mk_ismt2_pp(memo.first, m) << "="
                      << mk_ismt2_pp(memo.second, m) << std::endl;
            const word_term& lhs = get_word_term(memo.first);
            const word_term& rhs = get_word_term(memo.second);
            result.add_word_equation(word_equation(rhs, lhs));
        }
        return result;
    }

    const bool theory_str::block_dpllt_assignment_from_memo() {
        ast_manager& m = get_manager();
        expr *refinement_expr = nullptr;
        for (const auto& memo : m_we_expr_memo) {
            expr *const e = m.mk_not(mk_eq_atom(memo.first, memo.second));
            if (refinement_expr == nullptr) {
                refinement_expr = e;
            } else {
                refinement_expr = m.mk_or(refinement_expr, e);
            }
            std::cout << memo.first << " = " << memo.second << " \n";
        }
        if (refinement_expr != nullptr) {
            std::cout << "asserting " << mk_pp(refinement_expr, m) << std::endl;
            assert_axiom(refinement_expr);
            return true;
        }
        return false;
    }

};
