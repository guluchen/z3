#include <algorithm>
#include <sstream>
#include "ast/ast_pp.h"
#include "ast/rewriter/bool_rewriter.h"
#include "smt/theory_str/automata.h"
#include "smt/smt_context.h"
#include "smt/smt_model_generator.h"

#include "math/automata/symbolic_automata_def.h"

template<typename TO, typename FROM>
std::unique_ptr<TO> static_unique_pointer_cast(std::unique_ptr<FROM>&& old) {
    return std::unique_ptr<TO>{static_cast<TO*>(old.release())};
}
template<typename TO, typename FROM>
std::shared_ptr<TO> static_shared_pointer_cast(std::unique_ptr<FROM>&& old) {
    return std::shared_ptr<TO>{static_cast<TO*>(old.release())};
}

void show_fst(fst::StdVectorFst m_imp, const string& description="") {//YFC:I will remove this function later
    const float Zero = std::numeric_limits<float>::infinity();

    std::cout<<description<<std::endl;
    std::cout<<"Init: "<<m_imp.Start()<<std::endl;
    fst::StateIterator<fst::StdVectorFst> st_itr(m_imp);
    std::set<int> final_states;
    while (!st_itr.Done()) {
        int from = st_itr.Value();
        fst::ArcIterator<fst::StdVectorFst> arc_it(m_imp,from);
        while (!arc_it.Done()) {
            int symbol = arc_it.Value().ilabel;
            int symbol2 = arc_it.Value().olabel;
            int to = arc_it.Value().nextstate;
            std::cout<<from<<"("<<m_imp.Final(from)<<")"<<"--"<<(symbol-1)<<"/"<<(symbol2-1)<<"("<<arc_it.Value().weight<<")"<<"-->"<<to<<"("<<m_imp.Final(to)<<")"<<std::endl;
            arc_it.Next();
        }
        if (m_imp.Final(from)!=Zero)//is "from" a final state
            final_states.insert(from);
        st_itr.Next();
    }
    std::cout<<"Finals: ";
    for (auto& s:final_states) {
        std::cout<<s<<" ";
    }

    const auto props = m_imp.Properties(
            fst::kAcceptor | fst::kIDeterministic | fst::kNoIEpsilons | fst::kWeighted | fst::kUnweighted, true);

    std::cout<<std::endl;
    std::cout<<"(kAcceptor,kIDeterministic,kNoIEpsilons, kWeighted, kUnweighted): ("
             <<((props & fst::kAcceptor)!=0) << ","
             <<((props & fst::kIDeterministic) !=0) << ","
             <<((props & fst::kNoIEpsilons)!=0) << ","
             <<((props & fst::kWeighted)!=0) << ","
             <<((props & fst::kUnweighted)!=0 ) << ")"<<std::endl;
}

namespace smt {

    namespace str {

        automaton::~automaton() = default;

        std::list<automaton::ptr> automaton::remove_prefix(const zstring& prefix) {
            std::set<state> curr_heads{get_init()};
            std::set<state> next_heads;
            std::list<ptr> result;
            for (std::size_t i = 0; i < prefix.length(); i++) {
                next_heads.clear();
                for (auto s : curr_heads) {
                    const std::set<state>& avail = successors(s, prefix[i]);
                    next_heads.insert(avail.begin(), avail.end());
                }
                curr_heads = next_heads;
            }
            for (auto st : curr_heads) {
                ptr a{clone()};
                a->set_init(st);
                result.emplace_back(std::move(a));
            }
            return result;
        }

        std::list<automaton::ptr_pair> automaton::split() {
            const std::set<state>& finals = get_finals();
            std::list<ptr_pair> result;
            for (const auto middle : reachable_states()) {
                ptr a1{clone()};
                ptr a2{clone()};
                a2->set_init(middle);
                for (const auto f : finals) {
                    a1->remove_final(f);
                }
                a1->add_final(middle);
                result.emplace_back(std::make_pair(std::move(a1), std::move(a2)));
            }
            return result;
        }

        std::ostream& operator<<(std::ostream& os, automaton::sptr a) {
            return a->display(os);
        }

        automaton_factory::~automaton_factory() = default;

        zaut::symbol_boolean_algebra::symbol_boolean_algebra(ast_manager& m, expr_solver& s)
                : m_ast_man{m}, m_solver{s} {}

        using zaut_sym_t = zaut::symbol_boolean_algebra::expr;

        zaut_sym_t zaut::symbol_boolean_algebra::mk_true() {
            expr_ref e{m_ast_man.mk_true(), m_ast_man};
            return symbol::mk_pred(e, m_ast_man.mk_bool_sort());
        }

        zaut_sym_t zaut::symbol_boolean_algebra::mk_false() {
            expr_ref e{m_ast_man.mk_false(), m_ast_man};
            return symbol::mk_pred(e, m_ast_man.mk_bool_sort());
        }

        zaut_sym_t zaut::symbol_boolean_algebra::mk_and(zaut_sym_t e1, zaut_sym_t e2) {
            if (e1->is_char() && e2->is_char()) {
                if (e1->get_char() == e2->get_char()) return e1;
                if (m_ast_man.are_distinct(e1->get_char(), e2->get_char())) {
                    expr_ref e{m_ast_man.mk_false(), m_ast_man};
                    return symbol::mk_pred(e, e1->get_sort());
                }
            }
            sort *s = e1->get_sort();
            if (m_ast_man.is_bool(s)) {
                s = e2->get_sort();
            }
            const var_ref v{m_ast_man.mk_var(0, s), m_ast_man};
            const expr_ref fml1 = e1->accept(v);
            const expr_ref fml2 = e2->accept(v);
            if (m_ast_man.is_true(fml1)) return e2;
            if (m_ast_man.is_true(fml2)) return e1;
            if (fml1 == fml2) return e1;
            expr_ref e{m_ast_man};
            bool_rewriter{m_ast_man}.mk_and(fml1, fml2, e);
            return symbol::mk_pred(e, e1->get_sort());
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
            const var_ref v{m_ast_man.mk_var(0, e1->get_sort()), m_ast_man};
            const expr_ref fml1 = e1->accept(v);
            const expr_ref fml2 = e2->accept(v);
            if (m_ast_man.is_false(fml1)) return e2;
            if (m_ast_man.is_false(fml2)) return e1;
            expr_ref e{m_ast_man};
            bool_rewriter{m_ast_man}.mk_or(fml1, fml2, e);
            return symbol::mk_pred(e, e1->get_sort());
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
            const var_ref v{m_ast_man.mk_var(0, e->get_sort()), m_ast_man};
            expr_ref fml{m_ast_man.mk_not(e->accept(v)), m_ast_man};
            return symbol::mk_pred(fml, e->get_sort());
        }

        lbool zaut::symbol_boolean_algebra::is_sat(zaut_sym_t e) {
            if (e->is_char()) return l_true;
            if (e->is_range()) {
                // TODO: check lower is below upper
            }
            const expr_ref v{m_ast_man.mk_fresh_const("x", e->get_sort()), m_ast_man};
            const expr_ref fml = e->accept(v);
            if (m_ast_man.is_true(fml)) return l_true;
            if (m_ast_man.is_false(fml)) return l_false;
            return m_solver.check_sat(fml);
        }

        lbool zaut::symbol_solver::check_sat(expr *const e) {
            m_kernel.push();
            m_kernel.assert_expr(e);
            const lbool r = m_kernel.check();
            m_kernel.pop(1);
            return r;
        }

        zaut::dependency_ref::dependency_ref(am& m, seq_util& su, sm& sm, sba& sba, h& h)
                : ast_man{m}, util_s{su}, sym_man{sm}, sym_ba{sba}, han{h} {}

        bool zaut::is_deterministic() {
            for (const auto s : automaton::reachable_states()) {
                const moves& m = m_imp->get_moves_from(s);
                for (std::size_t i = 0; i < m.size(); i++) {
                    for (std::size_t j = 0; j < m.size(); j++) {
                        if (i == j) continue;
                        const symbol_ref e{m_dep.sym_ba.mk_and(m[i].t(), m[j].t()), m_dep.sym_man};
                        if (symbol_check_sat(e) == l_true) return false;
                    }
                }
            }
            return true;
        }

        std::set<automaton::state> zaut::get_finals() {
            const unsigned_vector& finals = m_imp->final_states();
            return std::set<state>(finals.begin(), finals.end());
        }

        automaton::ptr zaut::clone() {
            return mk_ptr(m_imp->clone());
        }

        automaton::ptr zaut::determinize() {
            return mk_ptr(m_dep.han.mk_deterministic(*m_imp));
        }

        automaton::ptr zaut::complement() {
            return mk_ptr(m_dep.han.mk_complement(*m_imp));
        }

        automaton::ptr zaut::intersect_with(sptr other) {
            zaut *const o = static_cast<zaut *>(other.get()); // one imp at a time
            return mk_ptr(m_dep.han.mk_product(*m_imp, *o->m_imp));
        }

        automaton::ptr zaut::union_with(sptr other) {
            zaut *const o = static_cast<zaut *>(other.get()); // one imp at a time
            return mk_ptr(internal::mk_union(*m_imp, *o->m_imp));
        }

        automaton::ptr zaut::append(sptr other) {
            zaut *const o = static_cast<zaut *>(other.get()); // one imp at a time
            return mk_ptr(internal::mk_concat(*m_imp, *o->m_imp));
        }

        void zaut::set_init(state s) {
            const scoped_ptr<internal> old{m_imp};
            m_imp = alloc(internal, m_dep.sym_man, s, m_imp->final_states(), transitions());
        }

        void zaut::add_final(state s) {
            m_imp->add_to_final_states(s);
        }

        void zaut::remove_final(state s) {
            m_imp->remove_from_final_states(s);
        }

        std::set<automaton::state> zaut::reachable_states(state s) {
            std::queue<state> pending;
            std::set<state> result{s};
            pending.push(s);
            while (!pending.empty()) {
                const state curr_s = pending.front();
                pending.pop();
                for (const auto& move : m_imp->get_moves_from(curr_s)) {
                    if (!move.is_epsilon()) {
                        const lbool is_sat = symbol_check_sat(symbol_ref{move.t(), m_dep.sym_man});
                        if (is_sat == l_undef || is_sat == l_false)
                            continue;
                    }
                    if (result.find(move.dst()) == result.end()) {
                        result.emplace(move.dst());
                        pending.push(move.dst());
                    }
                }
            }
            return result;
        }

        std::set<zaut::state> zaut::successors(state s) {
            std::set<state> result;
            for (const auto& mv : m_imp->get_moves_from(s)) {
                result.insert(mv.dst());
            }
            return result;
        }

        std::set<zaut::state> zaut::epsilon_closure(state s) {
            std::set<state> result;
            result.insert(s);
            for (const auto& move : m_imp->get_moves_from(s)) {
                if (move.t()== nullptr) {
                    result.insert(move.dst());
                }
            }
            return result;
        }

        std::set<zaut::state> zaut::successors(state s, const zstring& ch) {
            SASSERT(ch.length() == 1);
            std::set<state> result;

            for( const auto& eps_reach_state: epsilon_closure(s)){
                for (const auto& move : m_imp->get_moves_from(eps_reach_state)) {
                    const symbol_ref c{mk_char(ch), m_dep.sym_man};
                    if(move.t() != nullptr) {
                        const symbol_ref avail{m_dep.sym_ba.mk_and(move.t(), c), m_dep.sym_man};
                        if (symbol_check_sat(avail) == l_true) {
                            std::set<zaut::state> destinations= epsilon_closure(move.dst());
                            result.insert(destinations.begin(),destinations.end());
                        }
                    }
                }
            }

            return result;
        }

        std::set<automaton::len_constraint> zaut::length_constraints() {
            std::vector<state> lasso;
            std::queue<state> pending;
            std::set<std::pair<state, len_offset>> fin_offset;
            unsigned curr_offset = 0;

            const auto to_true = [&](const move& m) {
                if (m.is_epsilon()) {
                    return move{m};
                } else {
                    return move{m_dep.sym_man, m.src(), m.dst(), m_dep.sym_ba.mk_true()};
                }
            };
            scoped_ptr<internal> tmp{alloc(internal, m_dep.sym_man, m_imp->init(),
                                           m_imp->final_states(), transform_transitions(to_true))};
            const scoped_ptr<internal> tgt{m_dep.han.mk_deterministic(*tmp)};

            pending.push(tgt->init());
            while (!pending.empty()) {
                const state curr_s = pending.front();
                pending.pop();
                if (tgt->is_final_state(curr_s)) {
                    fin_offset.emplace(std::make_pair(curr_s, curr_offset));
                }
                for (const auto& move : tgt->get_moves_from(curr_s)) {
                    SASSERT(symbol_check_sat(symbol_ref{move.t(), m_dep.sym_man}) == l_true);
                    auto fit = std::find(lasso.begin(), lasso.end(), move.dst());
                    if (fit == lasso.end()) {
                        lasso.push_back(move.dst());
                        pending.push(move.dst());
                    } else { // lasso found
                        SASSERT(pending.empty());
                        lasso.erase(lasso.begin(), fit);
                        break;
                    }
                }
                curr_offset++;
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

        std::ostream& zaut::display_timbuk(std::ostream& out) {
            out << "Ops ";
            for(unsigned alp = 0; alp <= maximal_char; alp++) {
                out << "a" << alp << ":1 ";
            }
            out << "start:0" << std::endl << std::endl;
            out << "Automaton A" << std::endl;
            out << "States ";
            for(state st : automaton::reachable_states()) {
                out << st << " ";
            }
            out << std::endl <<"Final States ";
            for(state st : get_finals()) {
                out << st << " ";
            }
            out << std::endl << "Transitions" << std::endl;
            out << "start() -> " << get_init() << std::endl;

            for(state from : automaton::reachable_states()) {
                for(unsigned alp = 0; alp <= maximal_char; alp++) {
                    zstring symbol(alp);
                    for(state to : successors(from, symbol)) {
                        out << "a" << alp << "(" << from << ") -> " << to << std::endl;
                    }
                }
            }
            return out;
        }

        bool zaut::operator==(const automaton& other) {
            const zaut *const o = static_cast<const zaut *>(&other); // one imp at a time
            return contains(*o) && o->contains(*this);
        }

        zaut::moves zaut::transitions() {
            moves result;
            for (const auto s : automaton::reachable_states()) {
                result.append(m_imp->get_moves_from(s));
            }
            return result;
        }

        zaut::moves zaut::transform_transitions(std::function<move(move)> transformer) {
            moves result;
            for (const auto s : automaton::reachable_states()) {
                for (const auto& m : m_imp->get_moves_from(s)) {
                    result.push_back(transformer(m));
                }
            }
            return result;
        }

        zaut::symbol *zaut::mk_char(const zstring& ch) {
            SASSERT(ch.length() == 1);
            return symbol::mk_char(m_dep.ast_man, m_dep.util_s.str.mk_char(ch, 0));
        }

        lbool zaut::symbol_check_sat(const symbol_ref& s) {
            return m_dep.sym_ba.is_sat(s);
        }

        bool zaut::contains(const zaut& other) const {
            const scoped_ptr<internal> difference{m_dep.han.mk_difference(*other.m_imp, *m_imp)};
            return difference->is_empty();
        }

        automaton::ptr zaut::mk_ptr(internal *&& a) const {
            return ptr{new zaut{a, {m_dep}}};
        }

        zaut_adaptor::zaut_adaptor(ast_manager& m, context& ctx)
                : m_ast_man{m}, m_util_s{m}, m_aut_make{m}, m_sym_man{m_aut_make.get_manager()} {
            m_sym_solver = alloc(zaut::symbol_solver, m, ctx.get_fparams());
            m_sym_ba = alloc(zaut::symbol_boolean_algebra, m, *m_sym_solver);
            m_aut_man = alloc(zaut::handler, *m_sym_man, *m_sym_ba);
        }

        zaut_adaptor::~zaut_adaptor() {
            dealloc(m_aut_man);
            dealloc(m_sym_ba);
            if (!m_aut_make.has_solver()) {
                // if the solver has been attached, when m_aut_make is destroyed,
                // the solver will be destroyed as well; if not, we have to destroy it here
                dealloc(m_sym_solver);
            }
        }

        automaton::sptr zaut_adaptor::mk_empty() {
            expr_ref a{m_util_s.re.mk_to_re(m_util_s.str.mk_string(symbol{"a"})), m_ast_man};
            expr_ref b{m_util_s.re.mk_to_re(m_util_s.str.mk_string(symbol{"b"})), m_ast_man};
            expr_ref empty{m_util_s.re.mk_inter(a, b), m_ast_man};
            return mk_from_re_expr(empty, true);
        }

        automaton::sptr zaut_adaptor::mk_from_word(const zstring& str) {
            expr_ref str_re{m_util_s.re.mk_to_re(m_util_s.str.mk_string(str)), m_ast_man};
            return mk_from_re_expr(str_re, false);
        }

        automaton::sptr zaut_adaptor::mk_from_re_expr(expr *const re, bool minimize_result) {
            std::stringstream ss;
            ss << mk_pp(re, m_ast_man);
            const std::string& re_str = ss.str();
            auto fit = m_re_aut_cache.find(re_str);
            if (fit != m_re_aut_cache.end()) {
                return fit->second;
            }
            if (!m_aut_make.has_solver()) {
                m_aut_make.set_solver(m_sym_solver);
            }
            zaut::dependency_ref dep{m_ast_man, m_util_s, *m_sym_man, *m_sym_ba, *m_aut_man};
            automaton::sptr result = std::make_shared<zaut>(m_aut_make(re), dep);
            if (!minimize_result) {
                return result;
            }
            result = result->determinize()->simplify();
            m_re_aut_cache[re_str] = result;
            return result;
        }

        oaut::oaut(internal a): m_imp{a} {
            m_imp = a;
        }

        bool oaut::is_empty() {
            if (m_imp.NumStates()==0)
                return true;

            std::set<state> processed;
            std::set<state> waitlist;

            waitlist.insert(m_imp.Start());
            while (!waitlist.empty()) {
                state cur = *waitlist.begin();
                waitlist.erase(waitlist.begin());
                processed.insert(cur);

                for (fst::ArcIterator<fst::StdVectorFst> arc_it(m_imp,cur);!arc_it.Done();arc_it.Next()) {
                    StateId to = arc_it.Value().nextstate;
                    if (m_imp.Final(to)!=Zero) { // is "to" a final state
                        return false;
                    }
                    if (processed.find(to) == processed.end()) {
                        processed.insert(cur);
                    }
                }
            }
            return true;
        }

        bool oaut::is_deterministic() {
            return 1 - !m_imp.Properties(fst::kIDeterministic, true);
        }

        std::set<automaton::state> oaut::get_finals() {
            std::set<state> result;
            for (fst::StateIterator<fst::StdVectorFst> st_itr(m_imp);!st_itr.Done();st_itr.Next()) {
                StateId state = st_itr.Value();
                if (m_imp.Final(st_itr.Value())!=Zero)//is "from" a final state
                    result.insert(state);
            }
            return result;
        }

        automaton::ptr oaut::determinize() {
            using namespace fst;
            StdVectorFst r_imp;
            cloneInternalStructure(r_imp);
            Determinize(r_imp, &r_imp);
            return std::unique_ptr<oaut>(new oaut(r_imp));
        };

        automaton::ptr oaut::complement() {
            using namespace fst;
            automaton::ptr result = clone();
            auto cur = static_unique_pointer_cast<oaut>(std::move(result));
            RmEpsilon(&cur->m_imp);
            Determinize(cur->m_imp, &cur->m_imp);
            Minimize(&cur->m_imp);
            cur->totalize();
            for (fst::StateIterator<fst::StdVectorFst> st_itr(cur->m_imp);!st_itr.Done();st_itr.Next()) {
                StateId state = st_itr.Value();
                cur->m_imp.SetFinal(state, (cur->m_imp.Final(state)==Zero)?One:Zero);
            }
            Minimize(&cur->m_imp);
            return std::unique_ptr<oaut>(new oaut(cur->m_imp));
            //return cur;
        }

        automaton::ptr oaut::clone() {
            using namespace fst;
            const float Zero = std::numeric_limits<float>::infinity();
            const float One = 0;
            StdVectorFst r_imp;
            std::map<StateId,StateId> st_map;
            for (StateIterator<fst::StdVectorFst> st_itr(m_imp);!st_itr.Done();st_itr.Next()) {
                StateId s=r_imp.AddState();
                st_map[st_itr.Value()] = s;
                if (m_imp.Final(st_itr.Value())!=Zero)//is "from" a final state
                    r_imp.SetFinal(s,One);
            }
            r_imp.SetStart(st_map[m_imp.Start()]);
            for (StateIterator<fst::StdVectorFst> st_itr(m_imp);!st_itr.Done();st_itr.Next()) {
                StateId from = st_itr.Value();
                for (ArcIterator<fst::StdVectorFst> arc_it(m_imp,st_itr.Value());!arc_it.Done();arc_it.Next()) {
                    Label symbol = arc_it.Value().ilabel;
                    StateId to = arc_it.Value().nextstate;
                    r_imp.AddArc(st_map[from], makeArc(symbol, st_map[to]));
                }
            }
            std::unique_ptr<automaton> result = std::unique_ptr<automaton>(new oaut(r_imp));
            return result;
        }

        automaton::ptr oaut::intersect_with(sptr other) {
            using namespace fst;
            oaut item = dynamic_cast<const oaut&>(*other);
            StdVectorFst r_imp;
            cloneInternalStructure(r_imp);
            ArcSort(&r_imp, OLabelCompare<StdArc>());
            ArcSort(&item.m_imp, ILabelCompare<StdArc>());

            Intersect(r_imp,item.m_imp,&r_imp);
            return std::unique_ptr<oaut>(new oaut(r_imp));
        };

        automaton::ptr oaut::union_with(sptr other) {
            using namespace fst;
            oaut item = dynamic_cast<const oaut&>(*other);
            StdVectorFst r_imp;
            cloneInternalStructure(r_imp);
            Union(&r_imp,item.m_imp);
            return std::unique_ptr<oaut>(new oaut(r_imp));
        };

        std::set<automaton::state> oaut::reachable_states(state s) {
            std::set<state> states;
            std::set<state> waitlist;

            waitlist.insert(m_imp.Start());
            while (!waitlist.empty()) {
                state cur = *waitlist.begin();
                waitlist.erase(waitlist.begin());
                states.insert(cur);

                for (fst::ArcIterator<fst::StdVectorFst> arc_it(m_imp,cur);!arc_it.Done();arc_it.Next()) {
                    StateId to = arc_it.Value().nextstate;
                    if (states.find(to) == states.end()) {
                        waitlist.insert(to);
                    }
                }
            }
            return states;
        }

        std::set<automaton::state> oaut::successors(state s) {
            std::set<state> states;
            for (fst::ArcIterator<fst::StdVectorFst> arc_it(m_imp,s);!arc_it.Done();arc_it.Next()) {
                state to = arc_it.Value().nextstate;
                states.insert(to);
            }
            return states;
        }

        std::set<automaton::state> oaut::successors(state s, const zstring& ch) {
            SASSERT(ch.length() == 1);
            std::set<state> states;

            for (fst::ArcIterator<fst::StdVectorFst> arc_it(m_imp,s);!arc_it.Done();arc_it.Next()) {
                state to = arc_it.Value().nextstate;
                Label symbol = arc_it.Value().ilabel;
                if (symbol == ch[0])
                    states.insert(to);
            }
            return states;

        };

        std::set<automaton::len_constraint> oaut::length_constraints() {
        }

        std::ostream& oaut::display(std::ostream& os) {
            os<<"Init: "<<m_imp.Start()<<std::endl;
            std::set<int> final_states;
            for (fst::StateIterator<fst::StdVectorFst> st_itr(m_imp);!st_itr.Done();st_itr.Next()) {
                StateId from = st_itr.Value();
                for (fst::ArcIterator<fst::StdVectorFst> arc_it(m_imp,st_itr.Value());!arc_it.Done();arc_it.Next()) {
                    Label symbol = arc_it.Value().ilabel;
                    StateId to = arc_it.Value().nextstate;
                    if ((symbol>=(int)'a' && symbol <= (int)'z')||
                        (symbol>=(int)'A' && symbol <= (int)'Z'))
                        os<<from<<"--"<<(char)(symbol-1)<<"-->"<<to<<std::endl;
                    else
                        os<<from<<"--"<<(symbol-1)<<"-->"<<to<<std::endl;
                }
                if (m_imp.Final(from)!=Zero)//is "from" a final state
                    final_states.insert(from);
            }
            os<<"Finals: ";
            for (auto& s:final_states) {
                os<<s<<" ";
            }
            os<<std::endl;
            const auto props = m_imp.Properties(
                    fst::kAcceptor | fst::kIDeterministic | fst::kNoIEpsilons | fst::kWeighted | fst::kUnweighted, true);

            os<<std::endl;
            os<<"(kAcceptor,kIDeterministic,kNoIEpsilons, kWeighted, kUnweighted): ("
              <<((props & fst::kAcceptor)!=0) << ","
              <<((props & fst::kIDeterministic) !=0) << ","
              <<((props & fst::kNoIEpsilons)!=0) << ","
              <<((props & fst::kWeighted)!=0) << ","
              <<((props & fst::kUnweighted)!=0 ) << ")"<<std::endl;
            return os;
        }

        std::ostream& oaut::display_timbuk(std::ostream& os) {
            os<<"Ops  start:0 ";
            for(int i=0;i<=automaton::maximal_char;i++){
                os<<"a"<<i<<":1 ";

            }
            os<<std::endl;

            os<<"Automaton OFST"<<std::endl;

            os<<"States ";
            std::set<int> final_states;
            for (fst::StateIterator<fst::StdVectorFst> st_itr(m_imp);!st_itr.Done();st_itr.Next()) {
                StateId cur = st_itr.Value();
                os<<"q"<<cur<<" ";
                if (m_imp.Final(cur)!=Zero)//is "cur" a final state
                    final_states.insert(cur);
            }
            os<<std::endl;

            os<<"Final States ";
            for (std::set<int>::iterator st_itr = final_states.begin();
                 st_itr!=final_states.end();++st_itr) {
                StateId cur = *st_itr;
                os<<"q"<<cur<<" ";
            }
            os<<std::endl;

            os<<"Transitions "<<std::endl;
            os<<"start() -> q"<<m_imp.Start()<<std::endl;

            for (fst::StateIterator<fst::StdVectorFst> st_itr(m_imp);!st_itr.Done();st_itr.Next()) {
                StateId from = st_itr.Value();
                for (fst::ArcIterator<fst::StdVectorFst> arc_it(m_imp,st_itr.Value());!arc_it.Done();arc_it.Next()) {
                    Label symbol = arc_it.Value().ilabel;
                    StateId to = arc_it.Value().nextstate;
                    os<<"a"<<(symbol-1)<<"(q"<<from<<") -> q"<<to<<std::endl;
                }

            }
            os<<std::endl;
            return os;
        }

        std::ostream& oaut::display(std::ostream& os, const string& description) {
            os << description << std::endl;
            return display(os);
        }

        bool oaut::operator==(const automaton& other) {
            try {
                oaut item = dynamic_cast<const oaut&>(other);
                RmEpsilon(&m_imp);
                RmEpsilon(&item.m_imp);
                Determinize(m_imp,&m_imp);
                Determinize(item.m_imp,&item.m_imp);
                return fst::Equivalent(m_imp, item.m_imp);
            }
            catch(const std::bad_cast& e) {
                return false;
            }
        }

        automaton::ptr oaut::append(sptr o){
            using namespace fst;


            oaut *result = static_cast<oaut *>(clone().release());
            oaut *const other = static_cast<oaut *>(o.get());

            std::map<state,state> state_map;
            set<state> my_finals=get_finals();

            for(StateIterator<StdVectorFst> st_itr(other->m_imp);!st_itr.Done(); st_itr.Next()){
                StateId s=result->add_state();
                StateId from = st_itr.Value();
                state_map[from]=s;
                if(other->m_imp.Final(from)!=Zero) {//is "from" a final state
                    result->add_final(state_map[from]);
                }
            }
            for(StateIterator<StdVectorFst> st_itr(other->m_imp);!st_itr.Done(); st_itr.Next()){
                StateId from = st_itr.Value();
                for(ArcIterator<fst::StdVectorFst> arc_it(other->m_imp,st_itr.Value());!arc_it.Done();arc_it.Next()){
                    Label symbol = arc_it.Value().ilabel;
                    StateId to = arc_it.Value().nextstate;
                    result->m_imp.AddArc(state_map[from], makeArc(symbol, state_map[to]));
                }
            }

            for(auto& s:my_finals){
                state other_init = other->m_imp.Start();
                result->m_imp.AddArc(s, makeArc(0, state_map[other_init]));
                result->remove_final(s);
            }
            RmEpsilon(&result->m_imp);

            return std::unique_ptr<automaton>(result);
        }



        void oaut::cloneInternalStructure(internal& r_imp) {
            using namespace fst;
            const float Zero = std::numeric_limits<float>::infinity();
            const float One = 0;
            std::map<StateId,StateId> st_map;
            for (StateIterator<fst::StdVectorFst> st_itr(m_imp);!st_itr.Done();st_itr.Next()) {
                StateId s=r_imp.AddState();
                st_map[st_itr.Value()] = s;
                if (m_imp.Final(st_itr.Value())!=Zero)//is "from" a final state
                    r_imp.SetFinal(s,One);
            }
            r_imp.SetStart(st_map[m_imp.Start()]);
            for (StateIterator<fst::StdVectorFst> st_itr(m_imp);!st_itr.Done();st_itr.Next()) {
                StateId from = st_itr.Value();
                for (ArcIterator<fst::StdVectorFst> arc_it(m_imp,st_itr.Value());!arc_it.Done();arc_it.Next()) {
                    Label symbol = arc_it.Value().ilabel;
                    StateId to = arc_it.Value().nextstate;
                    r_imp.AddArc(st_map[from], makeArc(symbol, st_map[to]));
                }
            }
        }

        void oaut::totalize() {
            StateId sink = m_imp.AddState();
            for (fst::StateIterator<fst::StdVectorFst> st_itr(m_imp);!st_itr.Done();st_itr.Next()) {
                StateId from = st_itr.Value();
                std::set<Label> usedSymbols;
                for (fst::ArcIterator<fst::StdVectorFst> arc_it(m_imp,st_itr.Value());!arc_it.Done();arc_it.Next()) {
                    Label symbol = arc_it.Value().ilabel;
                    usedSymbols.insert(symbol);
                }
                for (Label i=1;i<=MAX_CHAR_NUM;i++) {
                    if (usedSymbols.find(i)==usedSymbols.end()) {
                        m_imp.AddArc(from, makeArc(i, sink));
                    }
                }

            }
        }


        // Convert a regular expression to an e-NFA using Thompson's construction
        std::shared_ptr<oaut> oaut_adaptor::mk_oaut_from_re_expr(expr *const e) {
            using namespace fst;
            const float Zero = std::numeric_limits<float>::infinity();
            const float One = 0;
//            std::cout<<mk_pp(e,m)<<std::endl;

            std::shared_ptr<oaut> result;
            StdVectorFst result_fst;
            if (m_util_s.re.is_to_re(e)) {
                app *term_is_to_re = to_app(e);
                expr *term_str = term_is_to_re->get_arg(0);
                zstring str;
                if (m_util_s.str.is_string(term_str, str)) {
                    if (str.length() == 0) {
                        StateId init = result_fst.AddState();
                        result_fst.SetStart(init);
                        result_fst.SetFinal(init, One);
                    } else {
                        TRACE("str", tout << "build NFA for '" << str << "'" << "\n";);
                        /*
                         * For an n-character string, we make (n+1) states,
                         */
                        StateId last = result_fst.AddState();
                        result_fst.SetStart(last);
                        for (unsigned i = 0; i < str.length(); i++) {
                            StateId cur = result_fst.AddState();
                            result_fst.AddArc(last, makeArc(str[i]+1, cur));
                            TRACE("str", tout << "string transition " << last << "--" << str[i] << "--> " << cur
                                              << "\n";);
                            last = cur;
                        }
                        result_fst.SetFinal(last, One);
                    }
                    result=std::make_shared<smt::str::oaut>(result_fst);
                } else { // ! u.str.is_string(arg_str, str)
                    TRACE("str", tout << "WARNING: invalid string constant in str.to.re." << std::endl;);
                    m.raise_exception(
                            "invalid term in str.to.re, argument must be a string constant");
                }
            } else if (m_util_s.re.is_concat(e)) {
                app *term_concat = to_app(e);
                expr *re1 = term_concat->get_arg(0);
                expr *re2 = term_concat->get_arg(1);
                std::shared_ptr<oaut> prefix=mk_oaut_from_re_expr(re1);
                std::shared_ptr<oaut> suffix=mk_oaut_from_re_expr(re2);
                result = static_shared_pointer_cast<oaut>(prefix->append(suffix));

                TRACE("str", tout << "concat NFAs " <<mk_pp(re1,m)<<" and " <<mk_pp(re2,m)<<std::endl;);
            } else if (m_util_s.re.is_union(e)) {
                app *term_union = to_app(e);
                expr *re1 = term_union->get_arg(0);
                expr *re2 = term_union->get_arg(1);
                result = mk_oaut_from_re_expr(re1);
                std::shared_ptr<oaut> other = mk_oaut_from_re_expr(re2);
                fst::Union(&result->m_imp, other->m_imp);
                fst::RmEpsilon(&result->m_imp);

                TRACE("str", tout << "union NFAs " <<mk_pp(re1,m)<<" and " <<mk_pp(re2,m)<<std::endl;);
            } else if (m_util_s.re.is_star(e)) {
                app *term_star = to_app(e);
                expr *inner_re = term_star->get_arg(0);
                result=mk_oaut_from_re_expr(inner_re);
                StateId init =result->get_init();

                for (StateIterator<fst::StdVectorFst> st_itr(result->m_imp);!st_itr.Done();st_itr.Next()) {
                    StateId cur = st_itr.Value();
                    if (result->m_imp.Final(cur) != Zero ) {
                        result->m_imp.AddArc(cur, makeArc(0, init));// 0 is epsilon in OpenFst
                    }
                }
                result->add_final(result->get_init());
                fst::RmEpsilon(&result->m_imp);
                fst::Determinize(result->m_imp, &result->m_imp);
                fst::Minimize(&result->m_imp);
                TRACE("str", tout << "star NFA " <<mk_pp(inner_re,m)<<std::endl;);
            } else if (m_util_s.re.is_range(e)) {
                // range('a', 'z')
                // start --'a'--> end
                // start --'b'--> end
                // ...
                // start --'z'--> end
                app *term_range = to_app(e);
                expr *bound_expr1 = term_range->get_arg(0);
                expr *bound_expr2 = term_range->get_arg(1);
                StateId init = result_fst.AddState();
                result_fst.SetStart(init);
                StateId final = result_fst.AddState();
                result_fst.SetFinal(final, One);

                unsigned lower = exprToUnsigned(bound_expr1);
                unsigned upper = exprToUnsigned(bound_expr2);
                if (lower>upper) std::swap(lower,upper);
                for (unsigned label = lower; label <= upper; label++) {
                    result_fst.AddArc(init, makeArc(label, final));
                }
                result=std::make_shared<smt::str::oaut>(result_fst);
                TRACE("str", tout << "range NFA: " <<mk_pp(e,m)<<std::endl;);
            } else if (m_util_s.re.is_full_seq(e)) {
                // effectively the same as .* where . can be any single character
                // start --e--> tmp
                // tmp --e--> end
                // tmp --C--> tmp for every character C

                StateId init = result_fst.AddState();
                result_fst.SetStart(init);
                result_fst.SetFinal(init, One);

                for (unsigned label = 1; label <= (automaton::maximal_char+1); label++) {
                    result_fst.AddArc(init, makeArc(label, init));
                }
                result=std::make_shared<smt::str::oaut>(result_fst);
                TRACE("str", tout << "re.all NFA: " <<mk_pp(e,m)<<std::endl;);
            } else if (m_util_s.re.is_full_char(e)) {
                // effectively . (match any one character)
                StateId init = result_fst.AddState();
                result_fst.SetStart(init);
                StateId final = result_fst.AddState();
                result_fst.SetFinal(final, One);

                for (unsigned label = 1; label <= (automaton::maximal_char+1); label++) {
                    result_fst.AddArc(init, makeArc(label, final));
                }
                result=std::make_shared<smt::str::oaut>(result_fst);
                TRACE("str", tout << "re.allchar NFA: " <<mk_pp(e,m)<<std::endl;);
            } else if (m_util_s.re.is_complement(e)) {
                app *term_comp = to_app(e);
                expr *inner_expr = term_comp->get_arg(0);
                result = mk_oaut_from_re_expr(inner_expr);
                result = static_unique_pointer_cast<oaut>(result->complement());

                TRACE("str", tout << "re.complement NFA: " <<mk_pp(e,m)<<std::endl;);
            } else {
                TRACE("str", tout << "WARNING: invalid regular expression terms" << std::endl;);
                m.raise_exception(
                        "invalid regular expression terms");
            }
            return result;
        }

        unsigned oaut_adaptor::exprToUnsigned(expr * e) {
            zstring str_form;
            m_util_s.str.is_string(e, str_form);
            return str_form[0];
        }

        automaton::sptr oaut_adaptor::mk_from_re_expr(expr *const re, bool minimize_result) {
            return mk_oaut_from_re_expr(re);
        }

    }

}
