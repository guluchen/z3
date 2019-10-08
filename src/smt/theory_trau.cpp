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
#include "smt/theory_trau.h"
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
    }

    theory_trau::theory_trau(ast_manager& m, const theory_str_params& params)
            : theory(m.mk_family_id("seq")),
              m(m),
              m_scope_level(0),
              m_params(params),
              search_started(false),
            /* Options */
              m_rewrite(m),
              m_seq_rewrite(m),
              m_autil(m),
              m_arrayUtil(m),
              u(m),
              m_trail(m),
              m_find(*this),
              m_trail_stack(*this),
              m_delayed_axiom_setup_terms(m),
              m_delayed_assertions_todo(m),
              string_int_conversion_terms(m),
              m_persisted_axiom_todo(m),
              contains_map(m),
              m_fresh_id(0),
              totalCacheAccessCount(0),
              m_mk_aut(m),
              m_res(m),
              opt_DisableIntegerTheoryIntegration(false),
              opt_ConcatOverlapAvoid(true),
              uState(m),
              implied_facts(m){
        str_int_bound = rational(0);
    }

    theory_trau::~theory_trau() {
        m_trail.reset();
    }

    void theory_trau::display(std::ostream& os) const {
        os << "theory_trau display" << std::endl;
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

    void theory_trau::init(context *ctx) {
        theory::init(ctx);
    }

    bool theory_trau::internalize_atom(app *const atom, const bool gate_ctx) {
        (void) gate_ctx;
        return internalize_term(atom);
    }

    bool theory_trau::internalize_term(app *const term) {
        
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

    theory_var theory_trau::mk_var(enode *const n) {
        if (!u.is_seq(n->get_owner()) &&
            !u.is_re(n->get_owner())) {
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
    app * theory_trau::mk_value_helper(app * n, model_generator& mg) {
        expr* a0 = nullptr, *a1 = nullptr;
        if (u.str.is_string(n)) {
            return n;
        } else if (u.str.is_concat(n, a0, a1)) {
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

    model_value_proc *theory_trau::mk_value(enode *const n, model_generator& mg) {
        
        context & ctx = get_context();
        app_ref owner{m};
        owner = n->get_owner();
        // if the owner is not internalized, it doesn't have an e-node associated.
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << mk_ismt2_pp(owner, m) << std::endl;);
        rational vLen(-1);
        if (u.is_seq(owner) && get_len_value(n->get_owner(), vLen)) {
            STRACE("str", tout << __LINE__ << "mk_value for: " << mk_ismt2_pp(owner, m) << "  " << vLen << std::endl;);
        }
        else if (u.is_seq(owner)){
            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << mk_ismt2_pp(owner, m) << std::endl;);
            vLen.reset();
            ptr_vector<expr> leafNodes;
            if (u.str.is_concat(owner)) {
                get_nodes_in_concat(n->get_owner(), leafNodes);
            }
            else
                leafNodes.push_back(n->get_owner());

            for (unsigned i = 0; i < leafNodes.size(); ++i) {
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
                        vLen = rational(-1);
                        break;
                    }
                }
            }

            STRACE("str", tout << __LINE__ << "mk_value for: " << mk_ismt2_pp(owner, m) << "  " << vLen << std::endl;);
        }
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << mk_ismt2_pp(owner, m) << std::endl;);
        if (vLen.get_int64() == 0)
            return alloc(expr_wrapper_proc, u.str.mk_string(zstring("")));
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << mk_ismt2_pp(owner, m) << std::endl;);
        app * val = mk_value_helper(owner, mg);
        if (val != nullptr) {
            return alloc(expr_wrapper_proc, val);
        } else if (u.is_seq(owner)){
            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << mk_ismt2_pp(owner, m) << std::endl;);
//            return alloc(expr_wrapper_proc, owner);
            sort * s           = m.get_sort(n->get_owner());
            string_value_proc * result = nullptr;

            expr* non_fresh_var = nullptr;
            expr* regex = nullptr;
            is_regex_var(owner.get(), regex);
            expr* arr_var = get_var_flat_array(owner.get());
            if (is_non_fresh(owner.get()) && arr_var != nullptr) {
                STRACE("str", tout << __LINE__ << "mk_value for: " << mk_ismt2_pp(owner, m) << " (sort " << mk_ismt2_pp(m.get_sort(owner), m) << ")" << std::endl;);
                expr* arr_expr = get_var_flat_array(owner.get());
                if (arr_expr != nullptr) {
                    if (ctx.e_internalized(arr_expr)) {
                        enode *arrNode = ctx.get_enode(arr_expr);
                        result = alloc(string_value_proc, *this, s, n->get_owner(), true, arrNode, regex, vLen.get_int64());
                    }
                    else
                        return alloc(expr_wrapper_proc, owner);
                    non_fresh_var = owner.get();
                }
                else
                    return alloc(expr_wrapper_proc, owner);
            }
            else {
                STRACE("str", tout << __LINE__ << "mk_value for: " << mk_ismt2_pp(owner, m) << " (sort " << mk_ismt2_pp(m.get_sort(owner), m) << ")" << std::endl;);
                bool found = false;
                expr_ref_vector eqSet(m);
                collect_eq_nodes(owner.get(), eqSet);
                expr* reg = nullptr;
                for (unsigned i = 0; i < eqSet.size(); ++i) {
                    if ((is_non_fresh(eqSet[i].get()) && !u.str.is_concat(eqSet[i].get())) || is_internal_regex_var(eqSet[i].get(), reg)) {
                        expr* arr_expr = get_var_flat_array(owner.get());
                        if (arr_expr != nullptr && ctx.e_internalized(arr_expr)) {
                            enode* arrNode = ctx.get_enode(arr_expr);
                            result = alloc(string_value_proc, *this, s, n->get_owner(), true, arrNode, regex, vLen.get_int64());
                            found = true;
                            non_fresh_var = eqSet[i].get();
                            break;
                        }
                        else
                            return alloc(expr_wrapper_proc, owner);
                    }
                }

                if (!found) {
                    result = alloc(string_value_proc, *this, s, n->get_owner(), false, regex, vLen.get_int64());
                }
            }

            SASSERT(result != 0);
            STRACE("str", tout << __LINE__ << "mk_value for: " << mk_ismt2_pp(owner, m) << " (sort " << mk_ismt2_pp(m.get_sort(owner), m) << ")" << std::endl;);
            expr_ref_vector dep = get_dependencies(owner);
            expr* reg = nullptr;
            if (non_fresh_var != nullptr) {
                // add array
                expr* tmp_arr = get_var_flat_array(non_fresh_var);
                if (tmp_arr && ctx.e_internalized(tmp_arr))
                    result->add_entry(ctx.get_enode(get_var_flat_array(non_fresh_var)));
                STRACE("str", tout << __LINE__ << "mk_value for: " << mk_ismt2_pp(owner, m) << " (sort " << mk_ismt2_pp(m.get_sort(owner), m) << ")" << std::endl;);
                expr_ref_vector depImp = get_dependencies(non_fresh_var);
                STRACE("str", tout << __LINE__ << "mk_value for: " << mk_ismt2_pp(owner, m) << " (sort " << mk_ismt2_pp(m.get_sort(owner), m) << ")" << std::endl;);
                dep.append(depImp);

                // add its ancestors
                if (dependency_graph.contains(owner))
                    for (const auto& nn : dependency_graph[owner]) {
                        result->add_entry(ctx.get_enode(nn));
                    }
            }
            else if (is_internal_regex_var(owner.get(), reg)){
                // add array
                expr* tmp_arr = get_var_flat_array(owner.get());
                if (tmp_arr && ctx.e_internalized(tmp_arr))
                    result->add_entry(ctx.get_enode(get_var_flat_array(tmp_arr)));

                // add its ancestors
                if (dependency_graph.contains(owner))
                    for (const auto& nn : dependency_graph[owner]) {
                        result->add_entry(ctx.get_enode(nn));
                    }
            }
            else {
                // normal node
                STRACE("str", tout << __LINE__ << "mk_value for: " << mk_ismt2_pp(owner, m) << " (sort "
                                   << mk_ismt2_pp(m.get_sort(owner), m) << ")" << std::endl;);
                // all lens
                expr_ref_vector added_nodes(m);
                for (const auto& nn : dep)
                    if (ctx.e_internalized(nn)){
                        STRACE("str", tout << __LINE__ << " " << mk_pp(nn, m) << std::endl;);
                        if (is_non_fresh(nn) || is_regex_var(nn)) {
                            result->add_entry(ctx.get_enode(nn));
                            added_nodes.push_back(nn);
                        }
                    }

                // add its ancestors
                if (dependency_graph.contains(owner))
                    for (const auto& nn : dependency_graph[owner])
                        if (ctx.e_internalized(nn) && !added_nodes.contains(nn)){
                            result->add_entry(ctx.get_enode(nn));
                        }

                if (expr_array_linkers.contains(owner))
                    result->set_linker(expr_array_linkers[owner]);
            }
            STRACE("str", tout << __LINE__ << "mk_value for: " << mk_ismt2_pp(owner, m) << " (sort " << mk_ismt2_pp(m.get_sort(owner), m) << ")" << std::endl;);
            if (!u.str.is_concat(owner)) {
                if (ctx.e_internalized(mk_strlen(owner)))
                    result->add_entry(ctx.get_enode(mk_strlen(owner)));
            }
            STRACE("str", tout << __LINE__ << "mk_value for: " << mk_ismt2_pp(owner, m) << " (sort " << mk_ismt2_pp(m.get_sort(owner), m) << ")" << std::endl;);
            return result;
        }
        return alloc(expr_wrapper_proc, owner);
    }

    bool theory_trau::is_non_fresh(expr *n){
        expr_ref_vector eq(m);
        collect_eq_nodes(n, eq);
        for (const auto& nn : uState.non_fresh_vars)
            if (eq.contains(nn.m_key))
                return true;
        return false;
    }

    bool theory_trau::is_non_fresh(expr *n, int &val){
        for (const auto& nn : uState.non_fresh_vars)
            if (nn.m_key == n) {
                val = nn.m_value;
                if (val < 0)
                    val = connectingSize;
                return true;
            }
        return false;
    }

    bool theory_trau::is_regex_var(expr* n, expr* &regexExpr){
        for (const auto& we: membership_memo) {
            if (we.first == n){
                regexExpr = we.second;
                return true;
            }
        }
        return false;
    }

    bool theory_trau::is_regex_var(expr* n){
        for (const auto& we: membership_memo) {
            if (we.first == n){
                return true;
            }
        }
        return false;
    }

    bool theory_trau::is_regex_concat(expr* n){
        ptr_vector<expr> nodes;
        get_nodes_in_concat(n, nodes);
        for (unsigned i = 0; i < nodes.size(); ++i)
            if (!u.str.is_string(nodes[i]) && !is_regex_var(nodes[i])) {
                return false;
            }

        return true;
    }

    expr_ref_vector theory_trau::get_dependencies(expr *n){
        expr_ref_vector ret(m);
        expr_ref_vector eq(m);
        collect_eq_nodes(n, eq);
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(n, m) << std::endl;);
        if (u.str.is_concat(n)){
            ptr_vector<expr> nodes;
            get_all_nodes_in_concat(n, nodes);

            for (unsigned i = 0; i < nodes.size(); ++i) {
                if (!eq.contains(nodes[i]) && !ret.contains(nodes[i]))
                    ret.push_back(nodes[i]);
                else {
                }
            }
        }
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(n, m) << std::endl;);
        for (unsigned j = 0; j < eq.size(); ++j) {
            if (uState.eq_combination.contains(eq[j].get())) {
                for (const auto &nn : uState.eq_combination[eq[j].get()]) {
                    if (u.str.is_concat(nn)) {
                        ptr_vector<expr> nodes;
                        get_all_nodes_in_concat(nn, nodes);

                        for (unsigned i = 0; i < nodes.size(); ++i) {
                            if (!eq.contains(nodes[i]) && !ret.contains(nodes[i]))
                                ret.push_back(nodes[i]);
                        }
                    } else {
                        if (!eq.contains(nn) && !ret.contains(nn))
                            ret.push_back(nn);
                    }
                }
            }
        }
        return ret;
    }

    void theory_trau::add_theory_assumptions(expr_ref_vector& assumptions) {
        STRACE("str", tout << "add theory assumption for theory_trau" << std::endl;);
    }

    lbool theory_trau::validate_unsat_core(expr_ref_vector& unsat_core) {
        return l_undef;
    }

    void theory_trau::new_eq_eh(theory_var x, theory_var y) {
        clock_t t = clock();
        
        enode *const n1 = get_enode(x);
        enode *const n2 = get_enode(y);

        TRACE("str", tout << __FUNCTION__ << ":" << mk_ismt2_pp(n1->get_owner(), m) << " = "
                           << mk_ismt2_pp(n2->get_owner(), m) << "@lvl " << m_scope_level << std::endl;);

        handle_equality(get_enode(x)->get_owner(), get_enode(y)->get_owner());

        // merge eqc **AFTER** handle_equality
        m_find.merge(x, y);

        if (!is_trivial_eq_concat(n1->get_owner(), n2->get_owner())) {
            newConstraintTriggered = true;
            expr_ref tmp(createEqualOP(n1->get_owner(), n2->get_owner()), m);
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
    bool theory_trau::is_trivial_eq_concat(expr* x, expr* y){
        expr* x0 = nullptr, *x1 = nullptr, *y0 = nullptr, *y1 = nullptr;
        if (u.str.is_concat(x, x0, x1) && u.str.is_concat(y, y0, y1)) {
            if (are_equal_exprs(x0, y0) && are_equal_exprs(x1, y1)) {
                 return true;
            }
        }
        return false;
    }

    void theory_trau::assert_cached_eq_state(){
        if (implied_facts.size() > 0 && m_scope_level == 0){
            for (const auto& e : implied_facts) {
                assert_axiom(e);
            }
            implied_facts.reset();
        }


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

        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " implied_facts size: " << implied_facts.size() << std::endl;);
        if (implied_facts.size() > 0){
            newConstraintTriggered = true;
            uState.reassertEQ = true;
            uState.eqLevel = get_actual_trau_lvl();
            for (const auto& e : implied_facts) {
                assert_axiom(e);
            }
            if (uState.eqLevel == 0)
                implied_facts.reset();
        }

    }

    void theory_trau::handle_equality(expr * lhs, expr * rhs) {
        
        context & ctx = get_context();
        // both terms must be of sort String
        sort * lhs_sort = m.get_sort(lhs);
        sort * rhs_sort = m.get_sort(rhs);
        sort * str_sort = u.str.mk_string_sort();

        if (lhs_sort != str_sort || rhs_sort != str_sort) {
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
        expr *nn1_arg0 = nullptr, *nn1_arg1 = nullptr, *nn2_arg0 = nullptr, *nn2_arg1 = nullptr;
        if (u.str.is_concat(lhs, nn1_arg0, nn1_arg1) && u.str.is_concat(rhs, nn2_arg0, nn2_arg1)) {
            bool nn1HasEqcValue = false;
            bool nn2HasEqcValue = false;
            get_eqc_value(lhs, nn1HasEqcValue);
            get_eqc_value(rhs, nn2HasEqcValue);
            if (nn1_arg0 == nn2_arg0 && in_same_eqc(nn1_arg1, nn2_arg1)) {
                STRACE("str", tout << "skip: lhs arg0 == rhs arg0" << std::endl;);
                return;
            }

            if (nn1_arg1 == nn2_arg1 && in_same_eqc(nn1_arg0, nn2_arg0)) {
                STRACE("str", tout << "skip: lhs arg1 == rhs arg1" << std::endl;);
                return;
            }

            if (are_equal_concat(lhs, rhs))
                return;
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
            expr_ref conclusion(mk_not(m, createEqualOP(lhs, rhs)), m);
            if (u.str.is_string(containKey, keyStr)) {
                obj_hashtable<expr> checked_nodes;
                checked_nodes.insert(lhs);
                if (new_eq_check_wrt_disequalities(rhs, keyStr, conclusion, checked_nodes)) {
                    return;
                }
            }
        }
        else if (is_contain_equality(simplifiedRhs, containKey)){
            zstring keyStr;
            expr_ref conclusion(mk_not(m, createEqualOP(lhs, rhs)), m);
            if (u.str.is_string(containKey, keyStr)) {
                obj_hashtable<expr> checked_nodes;
                checked_nodes.insert(lhs);
                if (new_eq_check_wrt_disequalities(lhs, keyStr, conclusion, checked_nodes)) {
                    return;
                }
            }
        }

        // BEGIN new_eq_handler() in strTheory

        // Check that a string's length can be 0 iff it is the empty string.
        check_eqc_empty_string(lhs, rhs);

        // (lhs == rhs) -> ( Length(lhs) == Length(rhs) )
        instantiate_str_eq_length_axiom(ctx.get_enode(lhs), ctx.get_enode(rhs));

        // group terms by equivalence class (groupNodeInEqc())

        obj_hashtable<expr> eqc_concat_lhs;
        obj_hashtable<expr> eqc_var_lhs;
        obj_hashtable<expr> eqc_const_lhs;
        group_terms_by_eqc(lhs, eqc_concat_lhs, eqc_var_lhs, eqc_const_lhs);

        obj_hashtable<expr> eqc_concat_rhs;
        obj_hashtable<expr> eqc_var_rhs;
        obj_hashtable<expr> eqc_const_rhs;
        group_terms_by_eqc(rhs, eqc_concat_rhs, eqc_var_rhs, eqc_const_rhs);

        TRACE("str",
              tout << "lhs eqc:" << std::endl;
                      tout << "Constants:" << std::endl;
                      for (const auto& ex : eqc_const_lhs) {
                          tout << mk_ismt2_pp(ex, m) << std::endl;
                      }

                      tout << "rhs eqc:" << std::endl;
                      tout << "Constants:" << std::endl;
                      for (const auto& ex : eqc_const_rhs) {
                          tout << mk_ismt2_pp(ex, m) << std::endl;
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

            for (const auto& e : eqc_concat_rhs) {
                solve_concat_eq_str(e, conStr);
            }
        } else if (eqc_const_rhs.size() != 0) {
            expr* conStr = *(eqc_const_rhs.begin());

            for (const auto& e : eqc_concat_lhs) {
                solve_concat_eq_str(e, conStr);
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

        special_assertion_for_contain_vs_substr(lhs, rhs);
        special_assertion_for_contain_vs_substr(rhs, lhs);
    }

    bool theory_trau::new_eq_check_wrt_disequalities(expr* n, zstring containKey, expr_ref conclusion, obj_hashtable<expr> &checked_nodes){
        
        TRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": "<< mk_pp(n, m) << std::endl;);
        expr_ref_vector eqs(m);
        collect_eq_nodes(n, eqs);
        for (const auto& eq : eqs) {
            for (const auto& nn : m_wi_expr_memo) {
                expr* key;
                if (eq == nn.second.get() && is_contain_equality(nn.first.get(), key)){ // itor not contain key
                    zstring keyStr;
                    if (u.str.is_string(key, keyStr) && containKey.contains(keyStr)){ // containKey contains key
                        assert_axiom(conclusion.get());
                        return false;
                    }
                }
                else if (eq == nn.first.get() && is_contain_equality(nn.second.get(), key)){
                    zstring keyStr;
                    if (u.str.is_string(key, keyStr) && containKey.contains(keyStr)){
                        assert_axiom(conclusion.get());
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
                    if (ts0 == eq || ts1 == eq) {
                        // check if it is feasible or not
                        if (!checked_nodes.contains(it.get_value())) {
                            checked_nodes.insert(it.get_value());
                            if (!new_eq_check_wrt_disequalities(it.get_value(), containKey, conclusion, checked_nodes))
                                return false;
                        }
                    }
                }
        }
        return true;
    }

    void theory_trau::special_assertion_for_contain_vs_substr(expr* lhs, expr* rhs){
        
        // (str.++ replace1!tmp0 (str.++ "A" replace2!tmp1)) == (str.substr url 0 (+ 1 (str.indexof url "A" 0)))
        expr* contain = nullptr;
        if (is_contain_equality(lhs, contain)) {
            expr* arg0 = nullptr, *arg1 = nullptr, *arg2 = nullptr;
            if (u.str.is_extract(rhs, arg0, arg1, arg2)) {
                rational value;
                if (m_autil.is_numeral(arg1, value) && value.get_int64() == 0) {
                    // check 3rd arg
                    expr* arg0_index = nullptr, *arg1_index = nullptr, *arg2_index = nullptr;
                    if (u.str.is_index(arg2, arg0_index, arg1_index, arg2_index)) {
                        if (arg1_index == contain && arg2_index == arg1){
                            assert_axiom(mk_not(m, createEqualOP(lhs, rhs)));
                        }
                    }
                    else {
                        for (unsigned i = 0; i < to_app(arg2)->get_num_args(); ++i)
                            if (u.str.is_index(to_app(arg2)->get_arg(i), arg0_index, arg1_index, arg2_index)){
                                if (arg1_index == contain && arg2_index == arg1) {
                                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " end of " << mk_pp(lhs, m) << " = " << mk_pp(rhs, m) << std::endl;);
                                    // same containKey, same pos
                                    // get all str in lhs, take the last one
                                    ptr_vector<expr> exprVector;
                                    get_nodes_in_concat(lhs, exprVector);
                                    SASSERT(exprVector.size() == 3);

                                    // len3rd = arg2 - index - 1
                                    expr* len3rd = createMinusOP(arg2, createAddOP(to_app(arg2)->get_arg(i), mk_int(1)));
                                    expr* cause = createEqualOP(lhs, rhs);
                                    assert_implication(cause, createEqualOP(mk_strlen(exprVector[2]), len3rd));
                                    return;
                                }
                            }
                    }
                }
            }
        }
    }

    expr_ref_vector theory_trau::collect_all_empty_start(expr* lhs, expr* rhs){
        
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
            for (unsigned i = 0; i < v.size(); ++i){
                rational len;
                if (get_len_value(v[i], len)){
                    if (len.get_int64() == 0){
                        ret.push_back(createEqualOP(mk_strlen(v[i]), mk_int(0)));
                    }
                    else if (u.str.is_string(v[i]) && lhs != e){
                        ret.push_back(createEqualOP(lhs, e));
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
        return ret;
    }

    expr_ref_vector theory_trau::collect_all_empty_end(expr* lhs, expr* rhs){
        
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
                        ret.push_back(createEqualOP(mk_strlen(v[i]), mk_int(0)));
                    }
                    else if (u.str.is_string(v[i]) && lhs != e){
                        ret.push_back(createEqualOP(lhs, e));
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

        return ret;
    }

    expr_ref_vector theory_trau::negate_equality(expr* lhs, expr* rhs){
        
        expr_ref_vector ret(m);
        expr_ref_vector eqLhs(m);
        collect_eq_nodes(lhs, eqLhs);

        expr_ref_vector eqRhs(m);
        collect_eq_nodes(rhs, eqRhs);

        for (unsigned i = 0; i < eqLhs.size(); ++i)
            if (lhs != eqLhs[i].get())
                ret.push_back(createEqualOP(lhs, eqLhs[i].get()));

        for (unsigned i = 0; i < eqRhs.size(); ++i)
            if (rhs != eqRhs[i].get())
                ret.push_back(createEqualOP(rhs, eqRhs[i].get()));

        ret.push_back(createEqualOP(lhs, rhs));
        return ret;
    }

    bool theory_trau::is_inconsisten(obj_hashtable<expr> concat_lhs, obj_hashtable<expr> const& concat_rhs, obj_hashtable<expr> const_lhs, obj_hashtable<expr> const& const_rhs, bool &wrongStart, bool &wrongEnd){
        wrongStart = false;
        wrongEnd = false;
        for (const auto& e : concat_rhs)
            concat_lhs.insert(e);

        for (const auto& e : const_rhs)
            const_lhs.insert(e);

        // copy from const vectors
        vector<zstring> starts, ends;
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

        // check all starts
        for (unsigned i = 0; i < starts.size(); ++i)
            for (unsigned j = i + 1; j < starts.size(); ++j)
                if (starts[j].prefixof(starts[i]) || starts[i].prefixof(starts[j])) {

                }
                else {
                    wrongStart = true;
                    break;
                }

        // check all starts
        for (unsigned i = 0; i < ends.size(); ++i)
            for (unsigned j = i + 1; j < ends.size(); ++j)
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
    void theory_trau::solve_concat_eq_str(expr * concat, expr * str) {
        
        context &ctx = get_context();

        TRACE("str", tout << mk_ismt2_pp(concat, m) << " == " << mk_ismt2_pp(str, m) << std::endl;);

        zstring const_str;
        expr *a1 = nullptr, *a2 = nullptr;
        if (u.str.is_concat(to_app(concat), a1, a2) && u.str.is_string(to_app(str), const_str)) {
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
                    rational concatStrLen(const_str.length());
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
    expr * theory_trau::eval_concat(expr * n1, expr * n2) {
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

    void theory_trau::group_terms_by_eqc(expr * n, obj_hashtable<expr> & concats, obj_hashtable<expr> & vars, obj_hashtable<expr> & consts) {
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
    expr * theory_trau::simplify_concat(expr * node) {
        
        context & ctx = get_context();
        obj_map<expr, expr*> resolved_map;
        ptr_vector<expr> nodes;
        get_nodes_in_concat(node, nodes);

        for (unsigned i = 0; i < nodes.size(); ++i) {
            bool has_eq_val = false;
            expr * const_val = get_eqc_value(nodes[i], has_eq_val);
            if (const_val != nodes[i]) {
                resolved_map.insert(nodes[i], const_val);
            }
        }

        if (resolved_map.size() == 0) {
            // no simplification possible
            return node;
        } else {
            expr * resultAst = mk_string("");
            for (int i = nodes.size() - 1; i >= 0; --i) {
                bool has_eq_val = false;
                expr * const_val = get_eqc_value(nodes[i], has_eq_val);
                resultAst = mk_concat(const_val, resultAst);
            }

            if (in_same_eqc(node, resultAst)) {
            } else if (u.str.is_string(resultAst)){
                expr_ref_vector items(m);
                int pos = 0;
                for (auto itor : resolved_map) {
                    items.push_back(ctx.mk_eq_atom(itor.m_key, itor.m_value));
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
    void theory_trau::instantiate_str_eq_length_axiom(enode * lhs, enode * rhs) {
        context & ctx = get_context();
        

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
            assert_axiom(createEqualOP(premise.get(), conclusion.get()));
        else
            assert_implication(premise, conclusion);
    };

    /*
     * Check that a string's length can be 0 iff it is the empty string.
     */
    void theory_trau::check_eqc_empty_string(expr * lhs, expr * rhs) {
        context & ctx = get_context();
        

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
    bool theory_trau:: can_two_nodes_eq(expr * n1, expr * n2) {
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
    bool theory_trau::can_concat_eq_str(expr * concat, zstring& str) {
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
    bool theory_trau::can_concat_eq_concat(expr * concat1, expr * concat2) {
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

    inline expr * theory_trau::getMostLeftNodeInConcat(expr * node) {
        app * aNode = to_app(node);
        if (!u.str.is_concat(aNode)) {
            return node;
        } else {
            expr * concatArgL = aNode->get_arg(0);
            return getMostLeftNodeInConcat(concatArgL);
        }
    }

    inline expr * theory_trau::getMostRightNodeInConcat(expr * node) {
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
    bool theory_trau::new_eq_check(expr * lhs, expr * rhs) {
        context & ctx = get_context();
        
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
            if (are_equal_exprs(lhs, mk_string("")) && are_equal_exprs(rhs, mk_string("")))
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
        return true;
    }

    expr* theory_trau::collect_empty_node_in_concat(expr* n){
        ptr_vector <expr> nodes;
        get_nodes_in_concat(n, nodes);
        rational ra;
        expr_ref_vector ands(m);
        for (const auto& nn : nodes) {
            if (get_len_value(nn, ra) && ra.get_int64() == 0){
                ands.push_back(createEqualOP(mk_strlen(nn), mk_int(0)));
            }
        }

        return createAndOP(ands);
    }

    void theory_trau::propagate_const_str(expr * lhs, expr * rhs, zstring value){
        context & ctx = get_context();
        

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
                        expr * new_concat = mk_concat(lhs, ts1);
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
                        expr * new_concat = mk_concat(ts0, lhs);
                        m_trail.push_back(new_concat);

                        // check if it is feasible or not
                        propagate_non_const(litems, concat, new_concat);
                    }
                }
            }
        }
    }

    void theory_trau::propagate_non_const(expr_ref_vector litems, expr * concat, expr* new_concat){
        context & ctx = get_context();
        
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
                    expr* conclusion = mk_not(m, createEqualOP(concat, value));
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
                    expr* conclusion = mk_not(m, createEqualOP(concat, value));
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
                bool matchRes = match_regex(rhs, lhs);
                STRACE("str", tout << __LINE__ << " " << mk_ismt2_pp(new_concat, m) << " = " << mk_ismt2_pp(rhs, m) << " : "
                                   << (matchRes ? "yes: " : "no: ") << std::endl;);
                if (!matchRes) {
                    if (*itor != concat)
                        litems_lhs.push_back(ctx.mk_eq_atom(concat, *itor));

                    for (unsigned i = 0; i < litems_lhs.size(); ++i)
                        litems_rhs.push_back(litems_lhs[i].get());

                    for (unsigned i = 0; i < litems.size(); ++i)
                        litems_rhs.push_back(litems[i].get());
                    expr_ref implyL(mk_and(litems_rhs), m);
                    assert_implication(implyL, mk_not(m, ctx.mk_eq_atom(concat, new_concat)));
                }
            }
        }
    }

    void theory_trau::check_regex_in(expr * nn1, expr * nn2) {
        context & ctx = get_context();
        
        TRACE("str", tout << __FUNCTION__ << ": " << mk_ismt2_pp(nn1, m) << " == " << mk_ismt2_pp(nn2, m) << std::endl;);

        // how to get regex_sort?
        sort * regex_sort = nullptr;
        if (regex_in_bool_map.size() > 0){
            expr *tmp = regex_in_bool_map.begin()->m_value;
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
                    bool matchRes = match_regex(rhs, lhs);
                    expr_ref implyL(ctx.mk_eq_atom(*itor, constStr), m);
                    if (!matchRes) {
                        assert_implication(mk_and(litems), mk_not(implyL));
                    }
                }
            }
        }
    }

    void theory_trau::check_regex_in_lhs_rhs(expr * nn1, expr * nn2) {
        context &ctx = get_context();
        
        TRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": " << mk_ismt2_pp(nn1, m) << " == " << mk_ismt2_pp(nn2, m) << std::endl;);

        // how to get regex_sort?
        sort *regex_sort = nullptr;
        if (regex_in_bool_map.size() > 0) {
            expr *tmp = regex_in_bool_map.begin()->m_value;
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
                    bool matchRes = match_regex(rhs_over, lhs);
                    if (!matchRes) {
                        if (*itor01 != nn1)
                            litems_rhs.push_back(ctx.mk_eq_atom(nn1, *itor01));

                        for (unsigned i = 0; i < litems.size(); ++i)
                            litems_rhs.push_back(litems[i].get());

                        expr_ref implyL(mk_and(litems_rhs), m);
                        assert_implication(implyL, mk_not(m, ctx.mk_eq_atom(nn1, nn2)));
                    }
                }
        }
    }

    expr* theory_trau::construct_overapprox(expr* nn, expr_ref_vector & litems){
        context &ctx = get_context();
        

        // how to get regex_sort?
        sort *regex_sort = nullptr;
        if (regex_in_bool_map.size() > 0) {
            expr *tmp = regex_in_bool_map.begin()->m_value;
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
        expr* emptyReg = u.re.mk_to_re(u.str.mk_string(emptyConst));
        app *lhs = to_app(emptyReg);
        m_trail.push_back(lhs);

        // list of constraints
        bool lastIsSigmaStar = false;
        for (auto el : childrenVector) {
            zstring constStrValue;
            if (u.str.is_string(el, constStrValue)) {
                if (constStrValue.length() > 0) {
                    if (lhs != emptyReg)
                        lhs = u.re.mk_concat(lhs, u.re.mk_to_re(el));
                    else
                        lhs = u.re.mk_to_re(el);
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
                            for (unsigned i = 0; i < tmpList.size(); ++i)
                                litems.push_back(tmpList[i].get());
                            lhs = u.re.mk_concat(lhs, tmp);
                            STRACE("str", tout << __FUNCTION__ << ": " << mk_ismt2_pp(lhs, m) << std::endl;);
                            m_trail.push_back(lhs);
                            lastIsSigmaStar = false;
                        }
                    } else {
                        if (!lastIsSigmaStar) {
                            if (lhs != emptyReg)
                                lhs = u.re.mk_concat(lhs, u.re.mk_full_seq(regex_sort));
                            else
                                lhs = u.re.mk_full_seq(regex_sort);
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

    void theory_trau::propagate_contain_in_new_eq(expr * n1, expr * n2) {
        if (contains_map.empty()) {
            return;
        }

        
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
    void theory_trau::check_contain_by_eqc_val(expr * varNode, expr * constNode) {
        context & ctx = get_context();
        

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
                        obj_hashtable<expr> eqcConcats;
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

    void theory_trau::check_contain_by_substr(expr * varNode, expr_ref_vector & willEqClass) {
        context & ctx = get_context();
        
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

    bool theory_trau::in_contain_idx_map(expr * n) {
        return contain_pair_idx_map.contains(n);
    }

    void theory_trau::check_contain_by_eq_nodes(expr * n1, expr * n2) {
        context & ctx = get_context();
        

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
    bool theory_trau::in_same_eqc(expr * n1, expr * n2) {
        if (n1 == n2) return true;
        context & ctx = get_context();

        // similar to get_eqc_value(), make absolutely sure
        // that we've set this up properly for the context

        if (!ctx.e_internalized(n1)) {
            TRACE("str", tout << "WARNING: expression " << mk_ismt2_pp(n1, m) << " was not internalized" << std::endl;);
            ctx.internalize(n1, false);
        }
        if (!ctx.e_internalized(n2)) {
            TRACE("str", tout << "WARNING: expression " << mk_ismt2_pp(n2, m) << " was not internalized" << std::endl;);
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

    expr * theory_trau::collect_eq_nodes(expr * n, expr_ref_vector & eqcSet) {
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


    void theory_trau::new_diseq_eh(theory_var x, theory_var y) {
        clock_t t = clock();

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
                else {
                    STRACE("str", tout << __FUNCTION__ << ": not to m_wi_expr_memo: " << value << " " << mk_pp(n1, m)<< std::endl;);
                    skip = true;
                }
            }
            else if (u.str.is_string(n2, value)) {
                if (value.length() != 0 || m_scope_level == 0) {
                }
                else {
                    STRACE("str", tout << __FUNCTION__ << ": not to m_wi_expr_memo: " << value << " " << mk_pp(n2, m)<< std::endl;);
                    skip = true;
                }
            }

            expr *a0 = nullptr, *a1 = nullptr;
            if (u.str.is_concat(n1, a0, a1)){
                if (n2 == a0 || n2 == a1)
                    skip = true;
            }

            if (u.str.is_concat(n2, a0, a1)){
                if (n1 == a0 || n1 == a1)
                    skip = true;
            }
        }

        instantiate_str_diseq_length_axiom(n1, n2, skip);

        if (!skip && is_not_added_diseq(expr_ref{n1, m}, expr_ref{n2, m})) {
            STRACE("str", tout << __FUNCTION__ << ": add to m_wi_expr_memo: " << mk_ismt2_pp(n1, m) << " != " << mk_ismt2_pp(n2, m) << std::endl;);
            // skip all trivial diseq
            newConstraintTriggered = true;
            expr_ref tmp(mk_not(m, createEqualOP(n1, n2)), m);
            ensure_enode(tmp);
            mful_scope_levels.push_back(tmp);

            const str::expr_pair wi{expr_ref{n1, m}, expr_ref{n2, m}};
            m_wi_expr_memo.push_back(wi);
        }
        else {
            newConstraintTriggered = true;
            STRACE("str", tout << __FUNCTION__ << ": not to m_wi_expr_memo: " << mk_ismt2_pp(n1, m) << " != " << mk_ismt2_pp(n2, m) << std::endl;);
            STRACE("str", tout << __FUNCTION__ << ": not to m_wi_expr_memo: " << skip << "; " << is_not_added_diseq(expr_ref{n1, m}, expr_ref{n2, m}) << std::endl;);
        }
        STRACE("str", tout << __LINE__ <<  " time: " << __FUNCTION__ << ":  " << ((float)(clock() - t))/CLOCKS_PER_SEC << std::endl;);
    }

    /*
     * replace vs contain
     */
    bool theory_trau::is_inconsistent_inequality(expr* lhs, expr* rhs){
        expr* str;
        expr* simplifiedLhs = simplify_concat(lhs);
        expr* simplifiedRhs = simplify_concat(rhs);
        if (is_contain_equality(simplifiedLhs, str)){
            zstring key;
            if (u.str.is_string(str, key)) {
                expr_ref_vector eqs(m);
                collect_eq_nodes(rhs, eqs);
                for (const auto& eq : eqs) {
                    ptr_vector<expr> v;
                    get_all_nodes_in_concat(eq, v);
                    for (const auto &n : v) {

//                        expr * boolVar;
//                        if (contain_pair_bool_map.find(n, str, boolVar) && n != rhs){
//                            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " reach it "  << mk_pp(n, m)<< std::endl;);
//                            expr_ref_vector premises(m);
//                            premises.push_back(mk_not(m, createEqualOP(lhs, rhs)));
//                            premises.push_back(createEqualOP(rhs, eq));
//                            assert_implication(createAndOP(premises), mk_not(m, boolVar));
//                        }

                        zstring tmp;
                        if (u.str.is_string(n, tmp)) {
                            if (tmp.contains(key)) {
                                expr *conclusion = createEqualOP(lhs, rhs);
                                if (eq != rhs) {
                                    expr *premise = createEqualOP(rhs, eq);
                                    assert_implication(premise, conclusion);
                                } else
                                    assert_axiom(conclusion);
                                return true;
                            }
                        }
                    }
                }
            }
        }

        if (is_contain_equality(simplifiedRhs, str)){
            zstring key;
            if (u.str.is_string(str, key)) {
                expr_ref_vector eqs(m);
                collect_eq_nodes(lhs, eqs);
                for (const auto& eq : eqs) {
                    ptr_vector<expr> v;
                    get_all_nodes_in_concat(eq, v);
                    for (const auto &n : v) {
//                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " reach it "  << mk_pp(n, m)<< std::endl;);
//                        if (contain_pair_bool_map.find(n, str, boolVar) && n != lhs){
//                            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " reach it "  << mk_pp(n, m)<< std::endl;);
//                            expr_ref_vector premises(m);
//                            premises.push_back(mk_not(m, createEqualOP(lhs, rhs)));
//                            premises.push_back(createEqualOP(lhs, eq));
//                            assert_implication(createAndOP(premises), mk_not(m, boolVar));
//                        }

                        zstring tmp;
                        if (u.str.is_string(n, tmp)) {
                            if (tmp.contains(key)) {
                                expr *conclusion = createEqualOP(lhs, rhs);
                                if (eq != rhs) {
                                    expr *premise = createEqualOP(lhs, eq);
                                    assert_implication(premise, conclusion);
                                } else
                                    assert_axiom(conclusion);
                                return true;
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    bool theory_trau::is_not_added_diseq(expr_ref n1, expr_ref n2){
        const str::expr_pair w01 = std::make_pair(n1, n2);
        const str::expr_pair w02 = std::make_pair(n2, n1);
        for (unsigned i = 0; i < m_wi_expr_memo.size(); ++i)
            if (m_wi_expr_memo[i] == w01 || m_wi_expr_memo[i] == w02){
                return false;
            }
        return true;
    }

    void theory_trau::assert_cached_diseq_state(){

        if (uState.reassertDisEQ) {
            return;
        }
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << std::endl;);
        handle_diseq_notcontain(true);
        uState.reassertDisEQ = true;
        uState.diseqLevel = get_actual_trau_lvl();

    }

    /*
     * Add an axiom of the form:
     * len lhs != len rhs -> lhs != rhs
     * len lhs == 0 == len rhs --> lhs == rhs
     */
    void theory_trau::instantiate_str_diseq_length_axiom(expr * lhs, expr * rhs, bool &skip) {
        context & ctx = get_context();
        

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
            assert_axiom(createEqualOP(premise01, conclusion01));
        else
            assert_implication(premise01, conclusion01);

        // check all combinations
        zstring value;
        if (u.str.is_string(lhs, value)) {
            expr* extraAssert = handle_trivial_diseq(rhs, value);
            if (extraAssert != nullptr) {
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(extraAssert, m) << std::endl;);
                assert_axiom(createEqualOP(conclusion01, extraAssert));
            }
        }
        else if (u.str.is_string(rhs, value)) {
            expr* extraAssert = handle_trivial_diseq(lhs, value);
            if (extraAssert != nullptr) {
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(extraAssert, m) << std::endl;);
                assert_axiom(createEqualOP(conclusion01, extraAssert));
            }
        }


    }

    expr* theory_trau::handle_trivial_diseq(expr * e, zstring value){
        
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(e, m) << std::endl;);
        string_set constPart = extract_const(e);

        for (const auto& s : constPart)
            if (s.length() > value.length() || (s.length() == value.length() && s != value)) {
                return createGreaterEqOP(mk_strlen(e), mk_int(s.length()));
            }
            else if (s == value) {
                return createGreaterEqOP(mk_strlen(e), mk_int(value.length() + 1));
            }
        return nullptr;
    }

    theory_trau::string_set theory_trau::extract_const(expr* e, int lvl){
        if (lvl >= 5)
            return {};

        expr_ref_vector eq(m);
        expr* const_expr = collect_eq_nodes(e, eq);
        if (const_expr != nullptr){
            zstring const_val;
            u.str.is_string(const_expr, const_val);
            string_set ret;
            ret.insert(const_val);
            return ret;
        }
        else {
            string_set ret;
            expr *a0 = nullptr, *a1 = nullptr;
            for (unsigned i = 0; i < eq.size(); ++i)
                if (u.str.is_concat(eq[i].get(), a0, a1)) {
                    string_set const00 = extract_const(a0, lvl + 1);
                    string_set const01 = extract_const(a1, lvl + 1);
                    if (const00.size() == 0)
                        if (const01.size() > 0) {
                            for (const auto& c : const01)
                                ret.insert(c);
                        }
                    if (const01.size() == 0)
                        if (const00.size() > 0){
                            for (const auto& c : const00)
                                ret.insert(c);
                        }

                    if (const00.size() > 0 && const01.size() > 0){
                        for (const auto& s0 : const00)
                            for (const auto& s1 : const01)
                                ret.insert(s0 + s1);
                    }
                }
            return ret;
        }
    }

    enode* theory_trau::ensure_enode(expr* e) {
        context& ctx = get_context();
        if (!ctx.e_internalized(e)) {
            ctx.internalize(e, false);
        }
        enode* n = ctx.get_enode(e);
        ctx.mark_as_relevant(n);
        return n;
    }

    void theory_trau::set_up_axioms(expr * ex) {
        
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
            if (!m_basicstr_axiom_todo.contains(n))
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
                    m_library_aware_axiom_todo.insert(n);
                } else if (u.str.is_itos(ap)) {
                    TRACE("str", tout << __LINE__ << " found string-integer conversion term: " << mk_pp(ex, m) << std::endl;);
                    string_int_conversion_terms.push_back(ap);
                    m_library_aware_axiom_todo.insert(n);
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
                        m_library_aware_axiom_todo.insert(n);
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
                    m_library_aware_axiom_todo.insert(n);
                } else if (u.str.is_stoi(ap)) {
                    string_int_conversion_terms.push_back(ap);
                    m_library_aware_axiom_todo.insert(n);
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

    void theory_trau::create_pq(){
        if (p_bound_expr == nullptr)
            p_bound_expr = mk_int_var("PBound");
        if (q_bound_expr == nullptr)
            q_bound_expr = mk_int_var("QBound");
    }

    void theory_trau::init_search_eh() {
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

    void theory_trau::relevant_eh(app *const n) {
        (void) n;
    }

    void theory_trau::assign_eh(bool_var v, const bool is_true) {
        // YFC: membership constraint goes here
        (void) v;
        (void) is_true;
        expr *n1 = nullptr, *n2 = nullptr;
        context& ctx = get_context();
        expr* var =  ctx.bool_var2expr(v);
        if (u.str.is_prefix(var)){
        }
        else if (u.str.is_suffix(var)){
        }
        else if (u.str.is_in_re(var, n1, n2)){
            newConstraintTriggered = true;
            const str::expr_pair wi{expr_ref{n1, m}, expr_ref{n2, m}};
            if (is_true)
                membership_memo.push_back(wi);
            else
                non_membership_memo.push_back(wi);
        }
    }

    void theory_trau::push_scope_eh() {
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

    void theory_trau::pop_scope_eh(const unsigned num_scopes) {
        STRACE("str", tout << __FUNCTION__ << ": at level " << m_scope_level << "/ eqLevel = " << uState.eqLevel << "; diseqLevel = " << uState.diseqLevel << std::endl;);
        m_scope_level -= num_scopes;

        if (m_scope_level < uState.eqLevel) {
            uState.reset_eq();
        }

        if (m_scope_level < uState.diseqLevel) {
            uState.reset_diseq();
        }
        mful_scope_levels.pop_scope(num_scopes);
        m_we_expr_memo.pop_scope(num_scopes);
        m_wi_expr_memo.pop_scope(num_scopes);
        membership_memo.pop_scope(num_scopes);
        non_membership_memo.pop_scope(num_scopes);

        ptr_vector<enode> new_m_basicstr;
        for (ptr_vector<enode>::iterator it = m_basicstr_axiom_todo.begin(); it != m_basicstr_axiom_todo.end(); ++it) {
            enode * e = *it;
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

    void theory_trau::reset_eh() {
        TRACE("str", tout << __FUNCTION__ << std::endl;);
        m_trail_stack.reset();
        m_basicstr_axiom_todo.reset();
        m_str_eq_todo.reset();
        m_concat_axiom_todo.reset();
        completed_branches.reset();
        pop_scope_eh(get_context().get_scope_level());
    }

    final_check_status theory_trau::final_check_eh() {
        TRACE("str", tout << __FUNCTION__ << ": at level " << m_scope_level << "/ eqLevel = " << uState.eqLevel << "; bound = " << uState.str_int_bound << std::endl;);
        if (m_we_expr_memo.empty() && m_wi_expr_memo.empty() && membership_memo.size() == 0) {
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

        if (eval_str_int() || eval_disequal_str_int()) {
            TRACE("str", tout << "Resuming search due to axioms added by eval_str_int." << std::endl;);
            newConstraintTriggered = true;
            return FC_CONTINUE;
        }
        STRACE("str", tout << __LINE__ <<  " current time used: " << ":  " << ((float)(clock() - startClock))/CLOCKS_PER_SEC << std::endl;);
        bool addAxiom;
        expr_ref_vector diff(m);
        if (is_completed_branch(addAxiom, diff)){
            if (addAxiom)
                return FC_CONTINUE;
            else
                return FC_DONE;
        }

        dump_assignments();
        STRACE("str", tout << __LINE__ <<  " current time used: " << ":  " << ((float)(clock() - startClock))/CLOCKS_PER_SEC << std::endl;);
        obj_map<expr, int> non_fresh_vars;
        obj_map<expr, ptr_vector<expr>> eq_combination;
        if (init_chain_free(non_fresh_vars, eq_combination)){
            return FC_CONTINUE;
        }

        STRACE("str", tout << __LINE__ <<  " current time used: " << ":  " << ((float)(clock() - startClock))/CLOCKS_PER_SEC << std::endl;);
        if (!review_starting_ending_combination(eq_combination)){
            negate_equalities();
            return FC_CONTINUE;
        }
        STRACE("str", tout << __LINE__ <<  " current time used: " << ":  " << ((float)(clock() - startClock))/CLOCKS_PER_SEC << std::endl;);
        if (!review_disequalities_not_contain(eq_combination)){
            TRACE("str", tout << "Resuming search due to axioms added by review_disequalities_not_contain." << std::endl;);
            print_eq_combination(eq_combination);
            negate_context();
            return FC_CONTINUE;
        }
        STRACE("str", tout << __LINE__ <<  " current time used: " << ":  " << ((float)(clock() - startClock))/CLOCKS_PER_SEC << std::endl;);
        if (!is_notContain_consistent(eq_combination)) {
            TRACE("str", tout << "Resuming search due to axioms added by is_notContain_consistent check." << std::endl;);
            update_state();
            return FC_CONTINUE;
        }
        STRACE("str", tout << __LINE__ <<  " current time used: " << ":  " << ((float)(clock() - startClock))/CLOCKS_PER_SEC << std::endl;);
        print_eq_combination(eq_combination);

        STRACE("str", tout << __LINE__ <<  " current time used: " << ":  " << ((float)(clock() - startClock))/CLOCKS_PER_SEC << std::endl;);
        if (handle_contain_family(eq_combination)){
            TRACE("str", tout << "Resuming search due to axioms added by handle_contain_family propagation." << std::endl;);
            update_state();
            return FC_CONTINUE;
        }
        STRACE("str", tout << __LINE__ <<  " current time used: " << ":  " << ((float)(clock() - startClock))/CLOCKS_PER_SEC << std::endl;);
        if (handle_charAt_family(eq_combination)) {
            TRACE("str", tout << "Resuming search due to axioms added by handle_charAt_family propagation." << std::endl;);
            update_state();
            return FC_CONTINUE;
        }
        STRACE("str", tout << __LINE__ <<  " current time used: " << ":  " << ((float)(clock() - startClock))/CLOCKS_PER_SEC << std::endl;);
        if (propagate_eq_combination(eq_combination)) {
            TRACE("str", tout << "Resuming search due to axioms added by eq_combination propagation." << std::endl;);
            print_eq_combination(eq_combination);
            update_state();
            return FC_CONTINUE;
        }
        STRACE("str", tout << __LINE__ <<  " current time used: " << ":  " << ((float)(clock() - startClock))/CLOCKS_PER_SEC << std::endl;);
        if (refined_init_chain_free(non_fresh_vars, eq_combination)){
            return FC_CONTINUE;
        }
        STRACE("str", tout << __LINE__ <<  " current time used: " << ":  " << ((float)(clock() - startClock))/CLOCKS_PER_SEC << std::endl;);
        if (can_merge_combination(eq_combination)){
            TRACE("str", tout << "Resuming search due to axioms added by can_merge_combination propagation." << std::endl;);
            print_eq_combination(eq_combination);
            return FC_CONTINUE;
        }

        if (!parikh_image_check(eq_combination)){
            negate_context();
            return FC_CONTINUE;
        }

        STRACE("str", tout << __LINE__ <<  " current time used: " << ":  " << ((float)(clock() - startClock))/CLOCKS_PER_SEC << std::endl;);
        if (underapproximation(eq_combination, non_fresh_vars, diff)) {
            update_state();
            return FC_CONTINUE;
        }

        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " DONE." << std::endl;);
        return FC_DONE;
    }

    bool theory_trau::eval_str_int(){
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
            assert_axiom(createEqualOP(get_bound_str_int_control_var(), mk_int(str_int_bound)));
            if (str_int_bound >= max_str_int_bound)
                implied_facts.push_back(createEqualOP(get_bound_str_int_control_var(), mk_int(str_int_bound)));
            addedAxioms = true;
            need_change = false;
            newConstraintTriggered = true;
        }
        else if (string_int_conversion_terms.size() > 0 && need_change && str_int_bound < max_str_int_bound){
            str_int_bound = str_int_bound * rational(2);
            assert_axiom(createEqualOP(get_bound_str_int_control_var(), mk_int(str_int_bound)));
            if (str_int_bound >= max_str_int_bound)
                implied_facts.push_back(createEqualOP(get_bound_str_int_control_var(), mk_int(str_int_bound)));
            addedAxioms = true;
            need_change = false;
            newConstraintTriggered = true;
        }
        return addedAxioms;
    }

    bool theory_trau::eval_disequal_str_int(){
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << std::endl;);
        bool added_axioms = false;
        for (const auto &wi : m_wi_expr_memo) {
            if (!u.str.is_empty(wi.second.get()) && !u.str.is_empty(wi.first.get())) {
                expr* lhs = wi.first.get();
                expr* rhs = wi.second.get();
                expr* contain = nullptr;
                if (!is_contain_equality(lhs, contain) && !is_contain_equality(rhs, contain)) {

                    // lhs
                    bool is_const;
                    expr* const_val = get_eqc_value(lhs, is_const);
                    expr* i2s = nullptr;
                    if (is_const && eq_to_i2s(rhs, i2s)){
                        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " " << mk_pp(const_val, m) << " != " << mk_pp(i2s, m) << std::endl;);
                        zstring str_val;
                        u.str.is_string(const_val, str_val);
                        bool valid = false;
                        rational rational_val = string_to_int(str_val, valid);

                        rational val;
                        if (!get_arith_value(to_app(i2s)->get_arg(0), val)){

                            expr_ref_vector premise(m);
                            premise.push_back(createEqualOP(lhs, const_val));
                            premise.push_back(mk_not(m, createEqualOP(lhs, rhs)));

                            assert_axiom(rewrite_implication(createAndOP(premise), mk_not(m, createEqualOP(to_app(i2s)->get_arg(0), mk_int(rational_val)))));
                            added_axioms = true;
                        }
                        else {
                            STRACE("str",
                                   tout << __LINE__ << " *** " << __FUNCTION__ << " " << mk_pp(i2s, m) << " = " << val
                                        << std::endl;);
                            if (rational_val == val) {
                                negate_context();
                                added_axioms = true;
                            }
                        }
                    }

                    // rhs
                    const_val = get_eqc_value(rhs, is_const);
                    if (is_const && eq_to_i2s(lhs, i2s)){
                        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " " << mk_pp(const_val, m) << " != " << mk_pp(i2s, m) << std::endl;);
                        zstring str_val;
                        u.str.is_string(const_val, str_val);
                        bool valid = false;
                        rational rational_val = string_to_int(str_val, valid);

                        rational val;
                        if (!get_arith_value(to_app(i2s)->get_arg(0), val)){

                            expr_ref_vector premise(m);
                            premise.push_back(createEqualOP(rhs, const_val));
                            premise.push_back(mk_not(m, createEqualOP(lhs, rhs)));

                            assert_axiom(rewrite_implication(createAndOP(premise), mk_not(m, createEqualOP(to_app(i2s)->get_arg(0), mk_int(rational_val)))));
                            added_axioms = true;
                        }
                        else {
                            if (rational_val == val) {
                                negate_context();
                                added_axioms = true;
                            }
                        }
                    }
                }
            }
        }
        return added_axioms;
    }

    bool theory_trau::eq_to_i2s(expr* n, expr* &i2s){
        expr_ref_vector eqs(m);
        collect_eq_nodes(n, eqs);
        for (const auto& nn : eqs)
            if (u.str.is_itos(nn)) {
                i2s = nn;
                return true;
            }
        return false;
    }

    /*
     * Check agreement between integer and string theories for the term a = (str.to-int S).
     * Returns true if axioms were added, and false otherwise.
     */
    bool theory_trau::eval_str2int(app * a) {
        SASSERT(u.str.is_stoi(a));
        bool axiomAdd = false;
        context & ctx = get_context();

        expr * S = a->get_arg(0);

        // check integer theory
        rational i_val;
        bool i_val_exists = get_arith_value(a, i_val);
        if (i_val_exists) {
            STRACE("str", tout << __LINE__ << "integer theory assigns " << mk_pp(a, m) << " = " << i_val.to_string() << std::endl;);
            // if that value is not -1, we can assert (str.to.int S) = i_val --> S = "i_val"
            if (!i_val.is_minus_one()) {
            }
        }

        bool S_hasEqcValue;
        expr * S_str = get_eqc_value(S, S_hasEqcValue);
        if (S_hasEqcValue) {
            zstring str;
            u.str.is_string(S_str, str);
            bool valid = true;

            rational converted_representation = string_to_int(str, valid);
            if (i_val_exists && converted_representation == i_val)
                return false;
            // TODO this duplicates code a bit, we can simplify the branch on "conclusion" only
            if (valid) {
                // return actuan value
                expr_ref premise(ctx.mk_eq_atom(S, mk_string(str)), m);
                expr_ref conclusion(ctx.mk_eq_atom(a, m_autil.mk_numeral(converted_representation, true)), m);
                expr_ref axiom(rewrite_implication(premise, conclusion), m);
                if (!string_int_axioms.contains(axiom)) {
                    string_int_axioms.insert(axiom);
                    assert_axiom(axiom);
                    implied_facts.push_back(axiom.get());
                    m_trail_stack.push(insert_obj_trail<theory_trau, expr>(string_int_axioms, axiom));
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
                    implied_facts.push_back(axiom.get());
                    m_trail_stack.push(insert_obj_trail<theory_trau, expr>(string_int_axioms, axiom));
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
                STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " " << mk_pp(conclusion.get(), m) << std::endl;);
                expr_ref axiom(rewrite_implication(premise, conclusion), m);
                if (!string_int_axioms.contains(axiom)) {
                    string_int_axioms.insert(axiom);
                    assert_axiom(axiom);
                    implied_facts.push_back(axiom.get());
                    m_trail_stack.push(insert_obj_trail<theory_trau, expr>(string_int_axioms, axiom));
                    axiomAdd = true;
                }
            }
        }

        return axiomAdd;
    }

    rational theory_trau::string_to_int(zstring str, bool &valid){
        rational converted_representation(0);
        rational ten(10);
        if (str.length() == 0) {
            valid = false;
            converted_representation = rational(-1);
        } else {
            for (unsigned i = 0; i < str.length(); ++i) {
                if (!('0' <= str[i] && str[i] <= '9')) {
                    valid = false;
                    return rational(-1);
                } else {
                    // accumulate
                    char digit = (int)str[i];
                    std::string sDigit(1, digit);
                    int val = atoi(sDigit.c_str());
                    converted_representation = (ten * converted_representation) + rational(val);
                }
            }
        }
        return converted_representation;
    }

    int theory_trau::eval_invalid_str2int(expr* e, expr* &eq_node){
        expr_ref_vector eqs(m);
        collect_eq_nodes(e, eqs);
        for (const auto& n : eqs){
            if (u.str.is_concat(n)) {
                ptr_vector<expr> nodes;
                get_nodes_in_concat(n, nodes);
                zstring val;
                for (const auto& nn : nodes)
                    if (u.str.is_string(nn, val)) {
                        for (unsigned i = 0; i < val.length(); ++i)
                            if (val[i] < '0' || val[i] > '9') {
                                eq_node = n;
                                return -1;
                            }
                    }
            }
        }
        return 0;
    }

    bool theory_trau::eval_int2str(app * a) {
        bool axiomAdd = false;
        context & ctx = get_context();
        
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
                        implied_facts.push_back(axiom.get());
                        m_trail_stack.push(insert_obj_trail<theory_trau, expr>(string_int_axioms, axiom));
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
                expr_ref conclusion(ctx.mk_eq_atom(N, m_autil.mk_numeral(rational::minus_one(), true)), m);
                expr_ref axiom(rewrite_implication(premise, conclusion), m);
                if (!string_int_axioms.contains(axiom)) {
                    string_int_axioms.insert(axiom);
                    assert_axiom(axiom);
                    implied_facts.push_back(axiom.get());
                    m_trail_stack.push(insert_obj_trail<theory_trau, expr>(string_int_axioms, axiom));
                    axiomAdd = true;
                }
            }
        }
        return axiomAdd;
    }

    /*
     * sigma_domain: all letters appearing in concats
     * non_fresh_var: variables in disequalities: x != y, x does not contain y
     * eq_combination: all equalities over variable
     */

    bool theory_trau::init_chain_free(
            obj_map<expr, int> &non_fresh_vars,
            obj_map<expr, ptr_vector<expr>> &eq_combination){
        STRACE("str", tout << __LINE__ <<  " current time used: " << ":  " << ((float)(clock() - startClock))/CLOCKS_PER_SEC << std::endl;);
        sigma_domain = collect_char_domain_from_concat();
        STRACE("str", tout << __LINE__ <<  " current time used: " << ":  " << ((float)(clock() - startClock))/CLOCKS_PER_SEC << std::endl;);
        non_fresh_vars = collect_non_fresh_vars();
        STRACE("str", tout << __LINE__ <<  " current time used: " << ":  " << ((float)(clock() - startClock))/CLOCKS_PER_SEC << std::endl;);
        analyze_upper_bound_str_int();
        STRACE("str", tout << __LINE__ <<  " current time used: " << ":  " << ((float)(clock() - startClock))/CLOCKS_PER_SEC << std::endl;);
        expr_ref_vector subNodes(m);
        bool axiom_added = false;
        eq_combination = normalize_eq(subNodes, non_fresh_vars, axiom_added);
        STRACE("str", tout << __LINE__ <<  " current time used: " << ":  " << ((float)(clock() - startClock))/CLOCKS_PER_SEC << std::endl;);
        return axiom_added;
    }

    bool theory_trau::analyze_upper_bound_str_int(){
        rational bound = str_int_bound;
        bool all_upper_bounds = true;
        for (const auto& num : int_string_vars){
            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " upper_num_bound " << mk_pp(num, m) << std::endl;);
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

    rational theory_trau::log_10(rational n){
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

    rational theory_trau::ten_power(rational n){
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
     * sigma_domain: all letters appearing in eq_combination
     * non_fresh_var: variables in disequalities: x != y, x does not contain y
     * eq_combination: all equalities over variable
     */
    bool theory_trau::refined_init_chain_free(
            obj_map<expr, int> &non_fresh_vars,
            obj_map<expr, ptr_vector<expr>> &eq_combination){
        sigma_domain = collect_char_domain_from_eqmap(eq_combination);
        STRACE("str", tout << __LINE__ <<  " current time used: " << ":  " << ((float)(clock() - startClock))/CLOCKS_PER_SEC << std::endl;);
        expr_ref_vector notImportant(m);
        refine_important_vars(non_fresh_vars, notImportant, eq_combination);
        print_eq_combination(eq_combination);
        STRACE("str", tout << __LINE__ <<  " current time used: " << ":  " << ((float)(clock() - startClock))/CLOCKS_PER_SEC << std::endl;);
        expr_ref_vector subNodes(m);
        bool axiom_added = false;
        eq_combination = normalize_eq(subNodes, non_fresh_vars, axiom_added);
        STRACE("str", tout << __LINE__ <<  " current time used: " << ":  " << ((float)(clock() - startClock))/CLOCKS_PER_SEC << std::endl;);
        if (axiom_added)
            return axiom_added;
        refine_not_contain_vars(non_fresh_vars, eq_combination);
        STRACE("str", tout << __LINE__ <<  " current time used: " << ":  " << ((float)(clock() - startClock))/CLOCKS_PER_SEC << std::endl;);
        return false;
    }

    void theory_trau::refine_not_contain_vars(
            obj_map<expr, int> &non_fresh_vars,
            obj_map<expr, ptr_vector<expr>> const& eq_combination){
        TRACE("str", tout << __LINE__ << " " << __FUNCTION__ << std::endl;);
        
        for (const auto& nn : non_fresh_vars)
            STRACE("str", tout << __LINE__ << "\t "<< mk_pp(nn.m_key, m) << ": " << nn.m_value << std::endl;);

        expr* contain = nullptr;
        obj_hashtable<expr> not_imp;
        obj_hashtable<expr> mustbe_imp;
        for (const auto &wi : m_wi_expr_memo) {
            if (!u.str.is_empty(wi.second.get()) && !u.str.is_empty(wi.first.get())) {
                expr* lhs = wi.first.get();
                expr* rhs = wi.second.get();
                zstring needle;
                if (is_contain_equality(lhs, contain) && u.str.is_string(contain, needle) && !is_trivial_contain(needle)) {
                    expr_ref_vector vec(m);
                    collect_eq_nodes(rhs, vec);
                    if (is_not_important(rhs, needle, eq_combination, non_fresh_vars)){
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
                    if (is_not_important(lhs, needle, eq_combination, non_fresh_vars)){
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

        obj_map<expr, int> tmp;
        for (const auto& p : non_fresh_vars) {
            if (not_imp.find(p.m_key) != not_imp.end() &&
                p.m_value == -1 &&
                mustbe_imp.find(p.m_key) == mustbe_imp.end()) {
                continue;
            }
            else {
                tmp.insert(p.m_key, p.m_value);
            }
        }

        non_fresh_vars.reset();
        non_fresh_vars = tmp;

        TRACE("str", tout << __LINE__ << " " << __FUNCTION__ << std::endl;);
        for (const auto& nn : non_fresh_vars)
            STRACE("str", tout << "\t "<< mk_pp(nn.m_key, m) << ": " << nn.m_value << std::endl;);
    }

    bool theory_trau::is_not_important(expr* haystack, zstring needle, obj_map<expr, ptr_vector<expr>> const& eq_combination, obj_map<expr, int> const& non_fresh_vars){
        
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(haystack, m) << " " << needle << std::endl;);
        for (const auto& eq : eq_combination) {
            if (eq.get_value().size() > 1 && appear_in_eq(haystack, needle, eq.get_value(), non_fresh_vars)) {
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " appear_in_eq: " << mk_pp(haystack, m) << " " << needle << std::endl;);

                if (!appear_in_other_eq(eq.m_key, needle, eq_combination)) {
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " !appear_in_other_eq: " << mk_pp(haystack, m) << " " << needle << std::endl;);
                    return true;
                }
                else
                    return false;
            }
        }
        return false;
    }

    bool theory_trau::appear_in_eq(expr* haystack, zstring needle, ptr_vector<expr> const& s, obj_map<expr, int> const& non_fresh_vars) {
        for (const auto& n : s) {
            if (u.str.is_concat(n)) {
                ptr_vector<expr> nodes;
                get_nodes_in_concat(n, nodes);
                if (eq_in_list(haystack, nodes) && nodes.contains(u.str.mk_string(needle))) {
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(haystack, m) << " " << needle
                                       << " in " << mk_pp(n, m) << std::endl;);
                    // compare with other elements in s
                    for (const auto &nn : s)
                        if (nn != n) {
                            // shorten two parts
                            if (!can_omit(n, nn, needle)) {
                                return false;
                            }
                        }

                    // check if other eq do not contain non_fresh vars && const
                    for (const auto& ex : s)
                        if (n != ex) {
                            if (is_non_fresh(ex, non_fresh_vars) || u.str.is_string(ex))
                                return false;
                            ptr_vector<expr> ex_nodes;
                            get_nodes_in_concat(ex, ex_nodes);
                            for  (const auto& ex_node: ex_nodes)
                                if (is_non_fresh(ex_node, non_fresh_vars) ||  u.str.is_string(ex_node))
                                    return false;
                        }

                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(haystack, m) << " " << needle
                                       << " in " << mk_pp(n, m) << std::endl;);
                    return true;
                }
            }
        }
        return false;
    }

    bool theory_trau::eq_in_list(expr* n, ptr_vector<expr> const& nodes) {
        expr_ref_vector eqs(m);
        collect_eq_nodes(n, eqs);
        for (const auto& nn : eqs)
            if (nodes.contains(nn))
                return true;
        return false;
    }

    bool theory_trau::can_omit(expr* lhs, expr* rhs, zstring needle){
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
        for (int i = prefix; i < (int)rhsVec.size() - suffix; ++i)
            if (u.str.is_string(rhsVec[i], val))
                if (val.contains(needle) || needle.contains(val))
                    return false;

        return true;
    }

    bool theory_trau::appear_in_other_eq(expr* root, zstring needle, obj_map<expr, ptr_vector<expr>> const& eq_combination) {
        for (const auto& eq : eq_combination)
            if (eq.m_key != root) {
                for (const auto& n : eq.get_value()) {
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
    bool theory_trau::is_completed_branch(bool &addAxiom, expr_ref_vector &diff){
        
        addAxiom = false;
        expr_ref_vector guessed_eqs(m), guessed_diseqs(m);
        fetch_guessed_exprs_with_scopes(guessed_eqs, guessed_diseqs);

        if (at_same_eq_state(uState, diff) && at_same_diseq_state(guessed_eqs, guessed_diseqs, uState.disequalities)) {
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
                    handle_diseq_notcontain(true);
                    uState.diseqLevel = get_actual_trau_lvl();
                }

                uState.reassertDisEQ = true;
                uState.reassertEQ = true;

                addAxiom = true;
                return true;
            }
        }
        else {
            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " completed state " << completed_branches.size() << std::endl;);
            // check all completed state, skip the last one
            for (int i = 0; i < (int)completed_branches.size() - 1; ++i){
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " comparing with completed state " << uState.eqLevel << std::endl;);
                if (at_same_eq_state(completed_branches[i], diff) && at_same_diseq_state(guessed_eqs, guessed_diseqs, completed_branches[i].disequalities)){
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
    void theory_trau::update_state(){
        uState.eqLevel = get_actual_trau_lvl();
        uState.diseqLevel = get_actual_trau_lvl();
        uState.reassertEQ = true;
        uState.reassertDisEQ = true;
    }

    /*
     * a . b = c .d && |a| = |b| --> a = b
     */
    bool theory_trau::propagate_eq_combination(obj_map<expr, ptr_vector<expr>> const& eq_combination){
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << std::endl;);
        expr_ref_vector to_assert(m);
        for (const auto &c : eq_combination) {
            ptr_vector<expr> tmp = c.get_value();

            // compare with the root
            if (!c.get_value().contains(c.m_key))
                tmp.push_back(c.m_key);

            for (unsigned i = 0; i < tmp.size(); ++i)
                for (unsigned j = i + 1; j < tmp.size(); ++j) {
                    if (!propagate_equality(tmp[i], tmp[j], to_assert)){
                        // found some inconsistence
                        return true;
                    }
                }
        }
        if (to_assert.size() > 0){
            expr_ref_vector guessed_eqs(m), guessed_diseqs(m);
            fetch_guessed_exprs_with_scopes(guessed_eqs, guessed_diseqs);
            fetch_guessed_core_exprs(eq_combination, guessed_eqs, guessed_diseqs);
            expr* coreExpr = createAndOP(guessed_eqs);

            expr* tmp = createAndOP(to_assert);
            expr* assertingExpr = rewrite_implication(coreExpr, tmp);
            assert_axiom(tmp);
            implied_facts.push_back(assertingExpr);
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
    bool theory_trau::is_notContain_consistent(obj_map<expr, ptr_vector<expr>> const& eq_combination){
        expr_ref_vector eqList(m), diseqList(m);
        fetch_guessed_exprs_with_scopes(eqList, diseqList);
        fetch_guessed_core_exprs(eq_combination, eqList, diseqList);
        expr* core = createAndOP(eqList);

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
    bool theory_trau::is_notContain_consistent(expr* lhs, expr* rhs, expr* core){
        
        expr* contain = nullptr;
        expr_ref conclusion(createEqualOP(lhs, rhs), m);
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
    bool theory_trau::is_notContain_const_consistent(expr* lhs, zstring containKey, expr_ref conclusion){
        // find all related nodes
        
        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " contains(" << mk_pp(lhs, m) << ", " << containKey << ")" << std::endl;);
        expr_ref_vector relatedVars = check_contain_related_vars(lhs, containKey);
        if (relatedVars.size() > 0){
            expr_ref_vector eqs(m), diseqs(m);
            fetch_guessed_exprs_with_scopes(eqs);
            fetch_related_exprs(relatedVars, eqs);

            // implies that x contains A if needed, means negating the context
            expr_ref toAssert(rewrite_implication(createAndOP(eqs), conclusion), m);
            assert_axiom(toAssert);
            implied_facts.push_back(toAssert);
            return false;
        }
        return true;
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
    bool theory_trau::parikh_image_check(obj_map<expr, ptr_vector<expr>> const& eq_combination){
        
        expr_ref_vector ret(m);
        for (const auto& v : eq_combination) {
            for (const auto& e : v.get_value()){
                expr_ref_vector constList(m);
                if (get_image_in_expr(e, constList)){
                    for (const auto& nn : v.get_value())
                        if (nn != e){
                            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << std::endl;);
                            int cnt = get_lower_bound_image_in_expr(nn, constList[0].get());
                            if (cnt > (int)constList.size())
                                return false;
                        }
                }
                constList.reset();
                not_contain_string_in_expr(e, constList);
                for (const auto& s : constList){

                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(v.m_key, m) << " does not contain " << mk_pp(s, m) << std::endl;);
                    for (const auto& nn : v.get_value())
                        if (nn != e){
                            int cnt = get_lower_bound_image_in_expr(nn, s);
                            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << std::endl;);
                            if (cnt > 0)
                                return false;
                        }
                }

                zstring value;
                if (u.str.is_string(e, value)){
                    for (const auto& nn : v.get_value()){
                        if (!can_match(value, nn)) {
                            expr_ref tmp(mk_not(m, createEqualOP(e, nn)), m);
                            implied_facts.push_back(tmp.get());
                            assert_axiom(tmp);
                            return false;
                        }
                    }
                }

                for (const auto& ee : v.get_value())
                    if (e != ee){
                        if (!equal_parikh(e, ee))
                            return false;
                    }
                if (v.get_value().size() < 5)
                    for (const auto& ee : v.get_value())
                        if (e != ee){
                            if (!same_prefix_same_parikh(e, ee))
                                return false;
                        }
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(v.m_key, m) << std::endl;);
            }
        }
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " end" << std::endl;);
        return true;
    }

    bool theory_trau::same_prefix_same_parikh(expr* nn, expr* n){
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(nn, m) << " " << mk_pp(n, m) << std::endl;);
        ptr_vector<expr> nodes;
        get_nodes_in_concat(n, nodes);

        ptr_vector<expr> nnodes;
        get_nodes_in_concat(nn, nnodes);

        ptr_vector<expr> lhs;
        ptr_vector<expr> rhs;
        map<char, int, unsigned_hash, default_eq<char>> img_lhs;
        map<char, int, unsigned_hash, default_eq<char>> img_rhs;
        int diff_len = 0;
        for (unsigned i = 0; i < std::max(nodes.size(), nnodes.size()); ++i){
            zstring val;
            bool remove_lhs = false;
            bool remove_rhs = false;
            if (i < nodes.size()) {
                if (u.str.is_string(nodes[i], val)) {
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << val << std::endl;);
                    get_parikh_from_strs(val, img_lhs);
                    diff_len += (int)val.length();
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
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << val << std::endl;);
                    get_parikh_from_strs(val, img_rhs);
                    diff_len -= (int)val.length();
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

            if (lhs.size() == 0 && rhs.size() == 0 && diff_len == 0) {
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << i << std::endl;);
                if (!eq_parikh(img_lhs, img_rhs))
                    return false;
            }

            if (i < nodes.size() && !remove_lhs)
                lhs.push_back(nodes[i]);
            if (i < nnodes.size() && !remove_rhs)
                rhs.push_back(nnodes[i]);
            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(nn, m) << " " << mk_pp(n, m) << std::endl;);
        }

        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(nn, m) << " " << mk_pp(n, m) << std::endl;);
        return true;
    }

    bool theory_trau::equal_parikh(expr* nn, expr* n){
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

        map<char, int, unsigned_hash, default_eq<char>> parikh_n;
        map<char, int, unsigned_hash, default_eq<char>> parikh_nn;

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
        // check two parikhs
        if (!eq_parikh(parikh_n, parikh_nn))
            return false;

        return true;
    }

    void theory_trau::get_parikh_from_strs(zstring s, map<char, int, unsigned_hash, default_eq<char>> &img){
        for (unsigned i = 0; i < s.length(); ++i) {
            char ch = s[i];
            if (!img.contains(ch)) {
                img.insert(ch, 1);
            } else
                img[ch] = img[ch] + 1;
        }
    }

    bool theory_trau::eq_parikh(map<char, int, unsigned_hash, default_eq<char>> const& lhs, map<char, int, unsigned_hash, default_eq<char>> const& rhs){
        for (const auto& ch : lhs)
            if ((ch.m_value > 0 && (!rhs.contains(ch.m_key) || rhs[ch.m_key] != ch.m_value)) ||
                    (ch.m_value == 0 && rhs.contains(ch.m_key) && rhs[ch.m_key] != ch.m_value))
                return false;
        return true;
    }

    bool theory_trau::can_match(zstring value, expr* n){
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

    void theory_trau::not_contain_string_in_expr(expr* n, expr_ref_vector &constList){
        context &ctx = get_context();
        ptr_vector<expr> nodes;
        get_nodes_in_concat(n, nodes);
        for (const auto& nn : nodes){
            if (!u.str.is_string(nn)) {
                expr_ref_vector eqs(m);
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

    bool theory_trau::agree_on_not_contain(expr* n, expr* key){
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

    int theory_trau::get_lower_bound_image_in_expr(expr* n, expr* str){
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(str, m) << " " << mk_pp(n, m) << std::endl;);
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
            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " there are at least" << cnt << " in " << mk_pp(n, m) << std::endl;);
        return cnt;
    }

    bool theory_trau::get_image_in_expr(expr* n, expr_ref_vector &constList){

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

            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " there are " << constList.size() << " in " << mk_pp(constList[0].get(), m) << std::endl;);
            // can get the image here
            return true;
        }
        else
            return false;
    }

    bool theory_trau::not_contain(expr* haystack, expr* needle, expr* &realHaystack){
        context &ctx = get_context();
        expr_ref_vector eqs(m);
        collect_eq_nodes(haystack, eqs);
        for (const auto& s: eqs) {
            std::pair<expr *, expr *> key = std::make_pair(s, needle);
            if (contain_pair_bool_map.contains(key)) {
                STRACE("str",
                       tout << __LINE__ << " " << __FUNCTION__ << " not_contain check" << mk_pp(haystack, m)
                            << " " << mk_pp(needle, m) << std::endl;);

                switch (ctx.get_assignment(contain_pair_bool_map[key])) {
                    case l_true: STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " l_true"
                                                    << mk_pp(haystack, m) << " "
                                                    << mk_pp(needle, m) << std::endl;);
                        break;
                    case l_false: STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " l_false"
                                                     << mk_pp(haystack, m) << " "
                                                     << mk_pp(needle, m) << std::endl;);
                        realHaystack = s;
                        return true;
                    case l_undef: STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " l_undef"
                                                     << mk_pp(haystack, m) << " "
                                                     << mk_pp(needle, m) << std::endl;);
                        break;
                }
            }
        }
        return false;
    }

    bool theory_trau::does_contain(expr* haystack, expr* needle, expr* &realHaystack){
        context &ctx = get_context();
        expr_ref_vector eqs(m);
        collect_eq_nodes(haystack, eqs);
        for (const auto& s: eqs) {
            std::pair<expr *, expr *> key = std::make_pair(s, needle);
            if (contain_pair_bool_map.contains(key)) {
                STRACE("str",
                       tout << __LINE__ << " " << __FUNCTION__ << " does_contain check" << mk_pp(haystack, m)
                            << " " << mk_pp(needle, m) << std::endl;);

                switch (ctx.get_assignment(contain_pair_bool_map[key])) {
                    case l_true: STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " l_true"
                                                    << mk_pp(haystack, m) << " "
                                                    << mk_pp(needle, m) << std::endl;);
                        realHaystack = s;
                        return true;
                    case l_false: STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " l_false"
                                                     << mk_pp(haystack, m) << " "
                                                     << mk_pp(needle, m) << std::endl;);
                        break;
                    case l_undef: STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " l_undef"
                                                     << mk_pp(haystack, m) << " "
                                                     << mk_pp(needle, m) << std::endl;);
                        break;
                }
            }
        }
        return false;
    }

    int theory_trau::get_actual_trau_lvl(){
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
    bool theory_trau::at_same_eq_state(UnderApproxState const& state, expr_ref_vector &diff) {
        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << std::endl;);
        
        expr_ref_vector guessed_eqs(m),  guessed_diseqs(m);
        fetch_guessed_exprs_with_scopes(guessed_eqs, guessed_diseqs);
        guessed_eqs.append(guessed_diseqs);

        expr_ref_vector prev_guessed_eqs(m);
        fetch_guessed_exprs_from_cache(state, prev_guessed_eqs);

        if (state.equalities.size() == 0 && state.disequalities.size() == 0)
            return false;

        // compare all eq
        for(const auto& e : prev_guessed_eqs){
            if (e != m.mk_true() && !guessed_eqs.contains(e) ) {
                // check the case where some var disappear because of len = 0
                if (to_app(e)->get_num_args() != 2)
                    continue;

                // check if it is the bound var
                std::string toStr = expr2str(e);
                if (toStr.find("Bound!") != std::string::npos)
                    continue;
                expr* lhs = simplify_concat(to_app(e)->get_arg(0));
                expr* rhs = simplify_concat(to_app(e)->get_arg(1));
                expr* eq = createEqualOP(lhs, rhs);
                expr_ref_vector eqs(m);
                collect_eq_nodes(lhs, eqs);
                if (eq != m.mk_true() && !eqs.contains(rhs)) {
                    expr* not_e = mk_not(m, e);
                    if (guessed_diseqs.contains(not_e))
                        diff.push_back(not_e);
                    STRACE("str", tout << __LINE__ << " not at_same_state " << mk_pp(e, m) << std::endl;);
                    return false;
                }
                else
                    STRACE("str", tout << __LINE__ << " does contain expr at_same_state " << mk_pp(e, m) << " --> " << mk_pp(eq, m)<< std::endl;);
            }
        }

        return true;
    }

    bool theory_trau::at_same_diseq_state(expr_ref_vector const& curr_eq, expr_ref_vector const& curr_diseq, expr_ref_vector const& prev_diseq) {
        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << std::endl;);

        // compare all diseq
        for(const auto& e : prev_diseq){
            // skip x = ""
            if (is_empty_comparison(e))
                continue;
            if (!curr_diseq.contains(e) && curr_eq.contains(e)) {
                STRACE("str", tout << __LINE__ <<  " not at_same_state  " << mk_pp(e, m) << std::endl;);
                return false;
            }
        }

        return true;
    }

    bool theory_trau::is_empty_comparison(expr* e){
        expr *a = nullptr;
        if (m.is_not(e, a)){
            expr* lhs = to_app(a)->get_arg(0);
            expr* rhs = to_app(a)->get_arg(1);

            if (lhs == mk_string("") || rhs == mk_string(""))
                return true;
        }
        return false;
    }

    /*
     * for all constraints over a variable, if they start/end with const strings,
     *      const start/end strings should be consistent
     */
    bool theory_trau::review_starting_ending_combination(obj_map<expr, ptr_vector<expr>> const& eq_combination){
        for (const auto& c : eq_combination) {
            vector<zstring> starts;
            vector<zstring> ends;
            zstring constStr;
            for (const auto& concat : c.get_value())
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
            for (unsigned i = 0; i < starts.size(); ++i)
                for (unsigned j = i + 1; j < starts.size(); ++j)
                    if (starts[i].prefixof(starts[j]) || starts[j].prefixof(starts[i])) {

                    }
                    else {
                        
                        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " " << mk_pp(c.m_key, m) << " starts with " << starts[i] << " and " << starts[j] << std::endl;);
                        return false;
                    }

            // check all ends
            for (unsigned i = 0; i < ends.size(); ++i)
                for (unsigned j = i + 1; j < ends.size(); ++j)
                    if (ends[i].suffixof(ends[j]) || ends[j].suffixof(ends[i])) {

                    }
                    else {
                        
                        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " " << mk_pp(c.m_key, m) << " ends with " << ends[i] << " and " << ends[j] << std::endl;);
                        return false;
                    }
        }
        return true;
    }

    /*
     *
     */
    theory_trau::unsigned_set theory_trau::collect_char_domain_from_concat(){
        unsigned_set charDomain;
        for (const auto& we : m_we_expr_memo) {
            zstring value;
            // lhs
            if (u.str.is_concat(we.first.get())) {
                ptr_vector<expr> childNodes;
                get_nodes_in_concat(we.first.get(), childNodes);
                for (const auto& n : childNodes){
                    if (u.str.is_string(n, value)) {
                        for (unsigned i = 0; i < value.length(); ++i)
                            charDomain.insert(value[i]);
                    }
                }

            }
            else if (u.str.is_string(we.first.get(), value)) {
                for (unsigned i = 0; i < value.length(); ++i)
                    charDomain.insert(value[i]);
            }

            // rhs
            if (u.str.is_concat(we.second.get())) {
                ptr_vector<expr> childNodes;
                get_nodes_in_concat(we.second.get(), childNodes);
                for (const auto& n : childNodes){
                    if (u.str.is_string(n, value)) {
                        for (unsigned i = 0; i < value.length(); ++i)
                            charDomain.insert(value[i]);
                    }
                }

            }
            else if (u.str.is_string(we.second.get(), value)) {
                for (unsigned i = 0; i < value.length(); ++i)
                    charDomain.insert(value[i]);
            }
        }

        for (const auto& mem : membership_memo){
            string_set tmp = collect_strs_in_membership(mem.second);
            for (const auto& s : tmp)
                for (unsigned i = 0; i < s.length(); ++i)
                    charDomain.insert(s[i]);
        }

        if (string_int_conversion_terms.size() > 0) {
            charDomain.insert('-');
            for (int i = 0; i < 10; ++i)
                charDomain.insert('0' + i);
        }

        for (const auto& ch : charDomain)
            STRACE("str", tout << __LINE__ <<  " sigma_domain: " << ch << std::endl;);

        return charDomain;
    }

    theory_trau::unsigned_set theory_trau::collect_char_domain_from_eqmap(obj_map<expr, ptr_vector<expr>> const& eq_combination){
        unsigned_set charDomain;
        for (const auto& v : eq_combination) {
            // skip if it is a simple case
            if ((v.get_value().size() == 1 && v.m_key == *(v.get_value().begin())) || v.get_value().size() == 0)
                continue;

            zstring value;
            if (u.str.is_concat(v.m_key)) {
                ptr_vector<expr> childNodes;
                get_nodes_in_concat(v.m_key, childNodes);
                for (const auto& n : childNodes){
                    if (u.str.is_string(n, value)) {
                        for (unsigned i = 0; i < value.length(); ++i)
                            charDomain.insert(value[i]);
                    }
                }
            }
            else if (u.str.is_string(v.m_key, value)) {
                for (unsigned i = 0; i < value.length(); ++i)
                    charDomain.insert(value[i]);
            }

            for (const auto& e : v.get_value()) {
                if (u.str.is_concat(e)) {
                    ptr_vector<expr> childNodes;
                    get_nodes_in_concat(e, childNodes);
                    for (const auto& n : childNodes){
                        if (u.str.is_string(n, value)) {
                            for (unsigned i = 0; i < value.length(); ++i)
                                charDomain.insert(value[i]);
                        }
                    }
                }
                else if (u.str.is_string(e, value)) {
                    for (unsigned i = 0; i < value.length(); ++i)
                        charDomain.insert(value[i]);
                }
            }
        }

        for (const auto& mem : membership_memo){
            string_set tmp = collect_strs_in_membership(mem.second);
            for (const auto& s : tmp)
                for (unsigned i = 0; i < s.length(); ++i)
                    charDomain.insert(s[i]);
        }

        if (string_int_conversion_terms.size() > 0) {
            charDomain.insert('-');
            for (int i = 0; i < 10; ++i)
                charDomain.insert('0' + i);
        }

        return charDomain;
    }

    /*
     * x = y . indexOf1 . "A" . ...
     * x = y . replace1 . "A" . ...
     * --> indexOf1 = replace1
     */
    bool theory_trau::handle_contain_family(obj_map<expr, ptr_vector<expr>> const& eq_combination) {
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << std::endl;);
        
        expr_ref_vector ands(m);
        for (const auto &v : eq_combination)
            if (v.get_value().size() > 1) {
                ptr_vector<expr> tmpVector = v.get_value();
                for (unsigned i = 0; i < tmpVector.size(); ++i)
                    for (unsigned j = i + 1; j < tmpVector.size(); ++j) {
                        expr* tmp = create_equations_over_contain_vars(tmpVector[i], tmpVector[j]);
                        if (tmp != nullptr)
                            ands.push_back(tmp);
                    }
            }

        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << std::endl;);
        if (ands.size() > 0) {
            expr_ref_vector eqcores(m), diseqcores(m);
            fetch_guessed_exprs_with_scopes(eqcores, diseqcores);
            fetch_guessed_core_exprs(eq_combination, eqcores, diseqcores);
            expr_ref toAssert(createAndOP(ands), m);
            assert_axiom(toAssert.get());
            implied_facts.push_back(toAssert.get());
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
    expr* theory_trau::create_equations_over_contain_vars(expr* x, expr* y){
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << std::endl;);
        ptr_vector<expr> nodes_x;
        get_nodes_in_concat(x, nodes_x);

        ptr_vector<expr> nodes_y;
        get_nodes_in_concat(y, nodes_y);

        // remove all prefixes
        unsigned pos = 0;
        for (pos = 0; pos < std::min(nodes_x.size(), nodes_y.size()); ++pos) {
            if (!are_equal_exprs(nodes_x[pos], nodes_y[pos]))
                break;
        }

        if (pos >= std::min(nodes_x.size(), nodes_y.size()) - 1)
            return nullptr;
        else {
            std::string name_x = expr2str(nodes_x[pos]);
            std::string name_y = expr2str(nodes_y[pos]);
            bool is_pre_contain_x = (name_x.find("indexOf1") == 0 || name_x.find("replace1") == 0 || name_x.find("pre_contain") == 0 );
            bool is_pre_contain_y = (name_y.find("indexOf1") == 0 || name_y.find("replace1") == 0 || name_y.find("pre_contain") == 0 );

            zstring tmp01;
            zstring tmp02;
            if (is_pre_contain_x && is_pre_contain_y) {
                if (are_equal_exprs(nodes_x[pos + 1], nodes_y[pos + 1])) {
                    return createEqualOP(nodes_x[pos], nodes_y[pos]);
                }
                else {
                    zstring tmp00;
                    zstring tmp01;
                    if (u.str.is_string(nodes_x[pos + 1], tmp00) && u.str.is_string(nodes_y[pos + 1], tmp01)) {
                        if (tmp00.prefixof(tmp01) || tmp01.prefixof(tmp00))
                            return createEqualOP(nodes_x[pos], nodes_y[pos]);
                    }
                }
            }
            else if (is_pre_contain_x && pos + 1 < nodes_x.size() && are_equal_exprs(nodes_x[pos + 1], nodes_y[pos])){
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(x, m) << " " << mk_pp(y, m) << std::endl;);
                return createEqualOP(nodes_x[pos], mk_string(""));
            }
            else if (is_pre_contain_y && pos + 1 < nodes_y.size() && are_equal_exprs(nodes_y[pos + 1], nodes_x[pos])){
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(x, m) << " " << mk_pp(y, m) << std::endl;);
                return createEqualOP(nodes_y[pos], mk_string(""));
            }
            else if (is_pre_contain_x && pos + 1 < nodes_x.size() && u.str.is_string(nodes_x[pos + 1], tmp01) && u.str.is_string(nodes_y[pos], tmp02) && tmp01.prefixof(tmp02)){
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(x, m) << " " << mk_pp(y, m) << std::endl;);
                return createEqualOP(nodes_x[pos], mk_string(""));
            }
            else if (is_pre_contain_y && pos + 1 < nodes_y.size() && u.str.is_string(nodes_y[pos + 1], tmp01) && u.str.is_string(nodes_x[pos], tmp02) && tmp01.prefixof(tmp02)){
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(x, m) << " " << mk_pp(y, m) << std::endl;);
                return createEqualOP(nodes_y[pos], mk_string(""));
            }
        }
        return nullptr;
    }

    /*
     * charAt1 = charAt1 at beginning because they have the same len = 1
     */
    bool theory_trau::handle_charAt_family(obj_map<expr, ptr_vector<expr>> const& eq_combination) {
        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << std::endl;);
        
        expr_ref_vector ands(m);
        for (const auto &v : eq_combination)
            if (v.get_value().size() > 1) {
                ptr_vector<expr> tmpVector = v.get_value();
                for (unsigned i = 0; i < tmpVector.size(); ++i) {
                    ptr_vector<expr> nodes_i;
                    get_nodes_in_concat(tmpVector[i], nodes_i);
                    if (nodes_i.size() > 1) { // charAt
                        std::string name_i = expr2str(nodes_i[0]);
                        zstring value_i("");
                        if (name_i.find("charAt1") == 0 || (u.str.is_string(nodes_i[0], value_i) && value_i.length() > 0)) {
                            expr_ref_vector eqNodes1(m), eqNodes0(m);
                            collect_eq_nodes(nodes_i[1], eqNodes1);
                            collect_eq_nodes(nodes_i[0], eqNodes0);

                            for (unsigned j = i + 1; j < tmpVector.size(); ++j) {
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
                                                ands.push_back(createEqualOP(nodes_i[0], nodes_j[0]));

                                            }
                                            else {
                                                if (value_i.length() > 0) {
                                                    // indexof vs string
                                                    zstring valueIndexof = value_i.extract(0, 1);
                                                    if (!are_equal_exprs(nodes_j[0], u.str.mk_string(valueIndexof))) {
                                                        expr* tmp = createEqualOP(u.str.mk_string(valueIndexof), nodes_j[0]);
                                                        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " " << mk_pp(tmp, m) << std::endl;);
                                                        ands.push_back(tmp);
                                                    }
                                                }
                                                else if (value_j.length() > 0){
                                                    // indexof vs string
                                                    zstring valueIndexof = value_j.extract(0, 1);
                                                    if (!are_equal_exprs(nodes_i[0], u.str.mk_string(valueIndexof))) {
                                                        expr* tmp = createEqualOP(nodes_i[0], u.str.mk_string(valueIndexof));
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
            expr_ref toAssert(rewrite_implication(createAndOP(eqcores), createAndOP(ands)), m);
            assert_axiom(toAssert.get());
            implied_facts.push_back(toAssert.get());
            return true;
        }
        else
            return false;
    }

    bool theory_trau::are_equal_exprs(expr* x, expr* y){
        expr_ref_vector eqs(m);
        collect_eq_nodes(x, eqs);
        if (eqs.contains(y))
            return true;
        return false;
    }

    obj_hashtable<expr> theory_trau::get_eqc_roots(){
        context & ctx = get_context();

        obj_hashtable<expr> eqc_roots;
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

    void theory_trau::add_theory_aware_branching_info(expr * term, double priority, lbool phase) {
        context & ctx = get_context();
        ctx.internalize(term, false);
        bool_var v = ctx.get_bool_var(term);
        ctx.add_theory_aware_branching_info(v, priority, phase);
    }  

    bool theory_trau::propagate_concat(){
        clock_t t = clock();
        context & ctx = get_context();
        
        expr_ref_vector assignments(m);
        ctx.get_assignments(assignments);
        bool axiomAdded = false;

        expr_ref_vector vars(m);
        expr_ref_vector concats(m);

        // collect all concats in context
        for (const auto& e : assignments) {
            if (! ctx.is_relevant(e)) {
                continue;
            }
            if (m.is_eq(e)) {
                collect_var_concat(e, vars, concats);
            }
        }

        axiomAdded = axiomAdded || propagate_value(concats);
        axiomAdded = axiomAdded || propagate_length(vars, concats);
        STRACE("str", tout << __LINE__ <<  " time: " << __FUNCTION__ << ":  " << ((float)(clock() - t))/CLOCKS_PER_SEC << std::endl;);
        return axiomAdded;
    }

    /*
     *
     */
    bool  theory_trau::propagate_value(expr_ref_vector & concat_set){
        
        context & ctx = get_context();
        bool axiomAdded = false;
        // iterate each concat
        // if a concat doesn't have length info, check if the length of all leaf nodes can be resolved
        for (expr_ref_vector::iterator it = concat_set.begin(); it != concat_set.end(); it++) {
            app * concat = to_app(*it);

            expr * concat_lhs = concat->get_arg(0);
            expr * concat_rhs = concat->get_arg(1);
            expr_ref_vector eq_lhs(m);
            collect_eq_nodes(concat_lhs, eq_lhs);

            expr_ref_vector eq_rhs(m);
            collect_eq_nodes(concat_rhs, eq_rhs);

            rational len_lhs, len_rhs;
            bool has_len_lhs = get_len_value(concat_lhs, len_lhs);
            bool has_len_rhs = get_len_value(concat_rhs, len_rhs);

            expr_ref_vector eqs(m);
            collect_eq_nodes(*it, eqs);
            for (unsigned i = 0; i < eqs.size(); ++i)
                if (eqs[i].get() != *it) {
                    rational len_i;
                    if (get_len_value(eqs[i].get(), len_i)) {
                        if (has_len_lhs && len_i == len_lhs) {

                            // left = var, right = emtpy
                            zstring empty("");
                            expr_ref_vector rhs_terms(m);

                            if (!eq_lhs.contains(eqs[i].get()))
                                rhs_terms.push_back(ctx.mk_eq_atom(concat_lhs, eqs[i].get()));
                            if (!eq_rhs.contains(mk_string(empty)))
                                rhs_terms.push_back(ctx.mk_eq_atom(concat_rhs, mk_string(empty)));

                            if (rhs_terms.size() > 0) {
                                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(*it, m) << " = "
                                                   << mk_pp(eqs[i].get(), m) << std::endl
                                                   << "LHS ~= " << mk_pp(eqs[i].get(), m) << " RHS ~= empty"
                                                   << std::endl;);
                                continue;
                                expr_ref_vector lhs_terms(m);
                                expr_ref expr1(ctx.mk_eq_atom(*it, eqs[i].get()), m);
                                expr_ref expr2(ctx.mk_eq_atom(mk_strlen(concat_lhs), mk_strlen(eqs[i].get())), m);

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

                            if (!eq_rhs.contains(eqs[i].get()))
                                rhs_terms.push_back(ctx.mk_eq_atom(concat_rhs, eqs[i].get()));
                            if (!eq_lhs.contains(mk_string(empty)))
                                rhs_terms.push_back(ctx.mk_eq_atom(concat_lhs, mk_string(empty)));

                            if (rhs_terms.size() > 0) {
                                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(*it, m) << " = "
                                                   << mk_pp(eqs[i].get(), m) << std::endl
                                                   << "RHS ~= " << mk_pp(eqs[i].get(), m) << " LHS ~= empty"
                                                   << std::endl;);
                                continue;
                                expr_ref_vector lhs_terms(m);
                                expr_ref expr1(ctx.mk_eq_atom(*it, eqs[i].get()), m);
                                expr_ref expr2(ctx.mk_eq_atom(mk_strlen(concat_rhs), mk_strlen(eqs[i].get())), m);

                                lhs_terms.push_back(expr1);
                                lhs_terms.push_back(expr2);

                                expr_ref lhs(mk_and(lhs_terms), m);
                                expr_ref rhs(mk_and(rhs_terms), m);
                                assert_implication(lhs, rhs);

                                axiomAdded = true;
                            }
                        }
                    }

                    expr *i_lhs = nullptr;
                    expr *i_rhs = nullptr;
                    if (u.str.is_concat(eqs[i].get(), i_lhs, i_rhs)) {
                        rational len_i_lhs, len_i_rhs;
                        if (get_len_value(i_lhs, len_i_lhs) && has_len_lhs && len_i_lhs == len_lhs) {

                            // left = left, right = right
                            expr_ref_vector rhs_terms(m);

                            if (!eq_rhs.contains(i_rhs))
                                rhs_terms.push_back(ctx.mk_eq_atom(concat_rhs, i_rhs));
                            if (!eq_lhs.contains(i_lhs))
                                rhs_terms.push_back(ctx.mk_eq_atom(concat_lhs, i_lhs));

                            if (rhs_terms.size() > 0) {
                                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(*it, m) << " = "
                                                   << mk_pp(eqs[i].get(), m) << std::endl
                                                   << "LHS ~= " << mk_pp(i_lhs, m) << " RHS ~= " << mk_pp(i_rhs, m)
                                                   << std::endl;);
                                continue;
                                expr_ref_vector lhs_terms(m);
                                expr_ref expr1(ctx.mk_eq_atom(*it, eqs[i].get()), m);
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

                            if (!eq_rhs.contains(i_rhs))
                                rhs_terms.push_back(ctx.mk_eq_atom(concat_rhs, i_rhs));
                            if (!eq_lhs.contains(i_lhs))
                                rhs_terms.push_back(ctx.mk_eq_atom(concat_lhs, i_lhs));

                            if (rhs_terms.size() > 0) {
                                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(*it, m) << " = "
                                                   << mk_pp(eqs[i].get(), m) << std::endl
                                                   << "LHS ~= " << mk_pp(i_lhs, m) << " RHS ~= " << mk_pp(i_rhs, m)
                                                   << std::endl;);
                                continue;
                                expr_ref_vector lhs_terms(m);
                                expr_ref expr1(ctx.mk_eq_atom(*it, eqs[i].get()), m);
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

    bool theory_trau::propagate_length(expr_ref_vector & varSet, expr_ref_vector & concatSet) {
        context & ctx = get_context();
        
        bool axiomAdded = false;

        // iterate each concat
        // if a concat doesn't have length info, check if the length of all leaf nodes can be resolved
        for (const auto& concat : concatSet) {
            rational lenValue;
            expr_ref concatlenExpr (mk_strlen(concat), m) ;
            bool allLeafResolved = true;
            if (! get_arith_value(concatlenExpr, lenValue)) {
                // the length of concat is unresolved yet
                if (get_len_value(concat, lenValue)) {
                    // but all leaf nodes have length information
                    TRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " " <<  mk_ismt2_pp(concat, m) << "| = " << lenValue << std::endl;);
                    expr_ref_vector leafNodes(m);
                    get_unique_non_concat_nodes(concat, leafNodes);
                    expr_ref_vector l_items(m);
                    for (expr_ref_vector::iterator leafIt = leafNodes.begin(); leafIt != leafNodes.end(); ++leafIt) {
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
                ptr_vector<expr> leaf_nodes;
                get_nodes_in_concat(concat, leaf_nodes);
                obj_map<expr, int> unresolved_nodes;
                expr_ref_vector l_items(m);

                expr_ref concatLenValueExpr (mk_int(lenValue), m);
                expr_ref lcExpr (ctx.mk_eq_atom(concatlenExpr, concatLenValueExpr), m);
                l_items.push_back(lcExpr);
                int pos = -1;
                for (unsigned i = 0; i < leaf_nodes.size(); ++i) {
                    rational leafLenValue;
                    if (get_len_value(leaf_nodes[i], leafLenValue)) {
                        expr_ref leafItLenExpr (mk_strlen(leaf_nodes[i]), m);
                        expr_ref leafLenValueExpr (mk_int(leafLenValue), m);
                        expr_ref lcExpr (ctx.mk_eq_atom(leafItLenExpr, leafLenValueExpr), m);
                        l_items.push_back(lcExpr);

                        lenValue = lenValue - leafLenValue;
                    } else {
                        if (!unresolved_nodes.contains(leaf_nodes[i])) {
                            unresolved_nodes.insert(leaf_nodes[i], 1);
                            if (unresolved_nodes.size() > 1)
                                break;
                            pos = i;
                        }
                        else
                            unresolved_nodes[leaf_nodes[i]] = unresolved_nodes[leaf_nodes[i]] + 1;
                    }
                }

                if (unresolved_nodes.size() == 1){
                    STRACE("str", tout <<  " Number of unresolved nodes  " << unresolved_nodes.size() << " at " << mk_ismt2_pp(leaf_nodes[pos], m) <<  std::endl;);
                    // get the node
                    SASSERT(pos != -1);
                    rational tmp(unresolved_nodes[leaf_nodes[pos]]);
                    rational newLen = div(lenValue, tmp);
                    expr_ref nodeLenExpr (mk_strlen(leaf_nodes[pos]), m) ;

                    expr_ref axl(m.mk_and(l_items.size(), l_items.c_ptr()), m);
                    expr_ref lenValueExpr (mk_int(newLen), m);
                    expr_ref axr(ctx.mk_eq_atom(nodeLenExpr, lenValueExpr), m);
                    assert_implication(axl, axr);
                    STRACE("str", tout <<  mk_ismt2_pp(axl, m) << "  --->  " <<  mk_ismt2_pp(axr, m)<< std::endl;);
                    axiomAdded = true;
                }
                else {
                    STRACE("str", tout <<  " Number of unresolved nodes  " << unresolved_nodes.size() << std::endl;);
                }
            }
        }

        // if no concat length is propagated, check the length of variables.
        if (! axiomAdded) {
            for (const auto& var : varSet) {
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

    void theory_trau::collect_var_concat(expr * node, expr_ref_vector & vars, expr_ref_vector & concats) {
        if (variable_set.find(node) != variable_set.end()) {
            vars.push_back(node);
        }
        else if (is_app(node)) {
            app * aNode = to_app(node);
            if (u.str.is_length(aNode)) {
                // Length
                return;
            }
            if (u.str.is_concat(aNode)) {
                if (!concats.contains(node)) {
                    concats.push_back(node);
                }
            }
            // recursively visit all arguments
            for (unsigned i = 0; i < aNode->get_num_args(); ++i) {
                expr * arg = aNode->get_arg(i);
                collect_var_concat(arg, vars, concats);
            }
        }
    }

    void theory_trau::get_unique_non_concat_nodes(expr * node, expr_ref_vector & argSet) {
        app * a_node = to_app(node);
        expr * leftArg = nullptr;
        expr * rightArg = nullptr;
        if (!u.str.is_concat(a_node, leftArg, rightArg) && !argSet.contains(node)) {
            argSet.push_back(node);
            return;
        } else {
            get_unique_non_concat_nodes(leftArg, argSet);
            get_unique_non_concat_nodes(rightArg, argSet);
        }
    }

    bool theory_trau::propagate_length_within_eqc(expr * var) {
        bool res = false;
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

    bool theory_trau::underapproximation(
            obj_map<expr, ptr_vector<expr>> const& eq_combination,
            obj_map<expr, int> & non_fresh_vars,
            expr_ref_vector const& diff) {
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** (" << m_scope_level << "/" << mful_scope_levels.size() << ")" << connectingSize << std::endl;);
        
        print_eq_combination(eq_combination, __LINE__);

        expr_ref_vector guessed_eqs(m), guessed_diseqs(m);
        fetch_guessed_exprs_with_scopes(guessed_eqs, guessed_diseqs);
        fetch_guessed_core_exprs(eq_combination, guessed_eqs, guessed_diseqs);
        UnderApproxState state(m, get_actual_trau_lvl(), get_actual_trau_lvl(), eq_combination, non_fresh_vars, guessed_eqs, guessed_diseqs, str_int_bound);

        if (is_equal(uState, state)) {
            bool axiomAdded = assert_state(guessed_eqs, guessed_diseqs);
            return axiomAdded;
        }
        else {
            uState = state;
            uState.str_int_bound = str_int_bound;
        }

        init_underapprox(eq_combination, non_fresh_vars);
        for (const auto& n : non_fresh_vars)
            STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " " << mk_pp(n.m_key, m) << " " << n.m_value << std::endl;);

        handle_diseq_notcontain();

        bool axiomAdded = handle_str_int();
        guessed_eqs.append(diff);
        axiomAdded = convert_equalities(eq_combination, non_fresh_vars, createAndOP(guessed_eqs)) || axiomAdded;
        STRACE("str", tout << __LINE__ <<  " current time used: " << ":  " << ((float)(clock() - startClock))/CLOCKS_PER_SEC << std::endl;);
        completed_branches.push_back(uState);
        return axiomAdded;
    }

    bool theory_trau::assert_state(expr_ref_vector const& guessed_eqs, expr_ref_vector const& guessed_diseqs){
        expr_ref_vector corePrev(m);
        fetch_guessed_exprs_from_cache(uState, corePrev);

        // update guessed exprs
        uState.equalities.reset();
        uState.equalities.append(guessed_eqs);

        uState.disequalities.reset();
        uState.disequalities.append(guessed_diseqs);

        bool axiomAdded = false;
        if (is_equal(corePrev, guessed_eqs)) {
            axiomAdded = true;
            underapproximation_cached();
            handle_diseq_notcontain(true);
            uState.eqLevel = get_actual_trau_lvl();
            uState.diseqLevel = get_actual_trau_lvl();
        }
        else if (!uState.reassertDisEQ){
            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " reassertDisEQ = false " << uState.diseqLevel << std::endl;);
            handle_diseq_notcontain(true);
            uState.diseqLevel = get_actual_trau_lvl();
            axiomAdded = true;
        }
        uState.reassertEQ = true;
        uState.reassertDisEQ = true;
        return axiomAdded;
    }

    bool theory_trau::handle_str_int(){
        if (string_int_conversion_terms.size() > 0) {

            
            STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << std::endl;);
            expr_ref_vector guessed_eqs(m), guessed_diseqs(m);
            fetch_guessed_str_int_with_scopes(guessed_eqs, guessed_diseqs);
            for (const auto &e : guessed_eqs) {
                STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " " << mk_pp(e, m) << std::endl;);
                app* a = to_app(e);
                expr* a0 = nullptr;
                if (u.str.is_stoi(a->get_arg(0), a0)){
                    handle_str2int(a->get_arg(1), a0);
                }
                else if (u.str.is_itos(a->get_arg(0), a0)){
                    if (!m_autil.is_numeral(a0))
                        handle_int2str(a0, a->get_arg(1));
                }
                else if (u.str.is_stoi(a->get_arg(1), a0)){
                    handle_str2int(a->get_arg(0), a0);

                }
                else if (u.str.is_itos(a->get_arg(1), a0)){
                    if (!m_autil.is_numeral(a0))
                        handle_int2str(a0, a->get_arg(0));
                }
            }

            for (const auto &e : guessed_diseqs) {
                app* a = to_app(to_app(e)->get_arg(0));
                STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " " << mk_pp(a, m) << std::endl;);
                expr* a0 = nullptr;
                if (u.str.is_stoi(a->get_arg(0), a0)){
                    handle_str2int(a->get_arg(1), a0);
                }
                else if (u.str.is_itos(a->get_arg(0), a0)){
                    if (!m_autil.is_numeral(a0))
                        handle_int2str(a0, a->get_arg(1));
                }
                else if (u.str.is_stoi(a->get_arg(1), a0)){
                    handle_str2int(a->get_arg(0), a0);
                }
                else if (u.str.is_itos(a->get_arg(1), a0)){
                    if (!m_autil.is_numeral(a0))
                        handle_int2str(a0, a->get_arg(0));
                }
            }
            return true;
        }
        return false;
    }

    void theory_trau::handle_str2int(expr* num, expr* str){
        
        rational len_val;
        if (get_len_value(str, len_val) && len_val == rational(0)){
            assert_axiom(rewrite_implication(createEqualOP(str, mk_string("")), createEqualOP(num, mk_int(-1))));
            return;
        }
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << std::endl;);
        if (quickpath_str2int(num, str)) {
            return;
        }

        expr* unrollConstraint = unroll_str_int(num, str);
//        expr* lenConstraint = lower_bound_str_int(num, str);
        expr* boundConstraint = createEqualOP(get_bound_str_int_control_var(), mk_int(str_int_bound));
        expr* fill_0 = fill_0_1st_loop(num, str);
        rational max_value = get_max_s2i(str);
        expr_ref_vector conclusions(m);

//        conclusions.push_back(lenConstraint);
        conclusions.push_back(unrollConstraint);
        conclusions.push_back(createLessEqOP(num, mk_int(max_value)));
        conclusions.push_back(fill_0);

        expr_ref_vector premises(m);
        premises.push_back(boundConstraint);
        premises.push_back(createEqualOP(num, u.str.mk_stoi(str)));

        expr* to_assert = rewrite_implication(createAndOP(premises), createAndOP(conclusions));
        assert_axiom(to_assert);
        implied_facts.push_back(to_assert);
    }

    rational theory_trau::get_max_s2i(expr* n){
        rational len;
        if (get_len_value(n, len)) {
            if (get_assign_lvl(mk_strlen(n), mk_int(len)) == 0)
                return ten_power(len) - rational(1);
        }

        return ten_power(str_int_bound) - rational(1);
    }

    /*
     * str2int(int2str(x)) = x
     * str2int("0" "0" ... int2str(x)) = x
     */
    bool theory_trau::quickpath_str2int(expr* num, expr* str, bool cached){
        expr* arg0 = nullptr;
        if (u.str.is_itos(str, arg0)){
            expr* to_assert = rewrite_implication(createEqualOP(num, u.str.mk_stoi(str)), createEqualOP(num, arg0));
            assert_axiom(to_assert);
            if (cached)
                implied_facts.push_back(to_assert);
            return true;
        }
        else {
            if (u.str.is_concat(str)){
                ptr_vector <expr> nodes;
                get_nodes_in_concat(str, nodes);
                if (u.str.is_itos(nodes[nodes.size() - 1], arg0)) {
                    expr* zero = u.str.mk_string(zstring("0"));
                    for (unsigned i = 0; i < nodes.size() - 1; ++i)
                        if (nodes[i] != zero)
                            return false;

                    expr* to_assert = rewrite_implication(createEqualOP(num, u.str.mk_stoi(str)), createEqualOP(num, arg0));
                    assert_axiom(to_assert);
                    if (cached)
                        implied_facts.push_back(to_assert);
                    return true;
                }
            }
        }
        return false;
    }

    void theory_trau::handle_int2str(expr* num, expr* str){
        
        rational len_val;
        if (get_len_value(str, len_val) && len_val == rational(0)){
            assert_axiom(rewrite_implication(createEqualOP(str, mk_string("")), createEqualOP(num, mk_int(-1))));
            return;
        }

        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << std::endl;);
        if (quickpath_int2str(num, str)) {
            return;
        }

        expr* unrollConstraint = unroll_str_int(num, str);
        expr* lenConstraint = lower_bound_int_str(num, str);
        expr* boundConstraint = createEqualOP(get_bound_str_int_control_var(), mk_int(str_int_bound));
        expr* fill_0 = fill_0_1st_loop(num, str);

        rational max_value = get_max_s2i(str);

        expr_ref_vector conclusions(m);

        conclusions.push_back(lenConstraint);
        conclusions.push_back(unrollConstraint);
        conclusions.push_back(createLessEqOP(num, mk_int(max_value)));
        conclusions.push_back(fill_0);

        expr_ref_vector premises(m);
        premises.push_back(boundConstraint);
        premises.push_back(createEqualOP(str, u.str.mk_itos(num)));

        expr* to_assert = rewrite_implication(createAndOP(premises), createAndOP(conclusions));
        assert_axiom(to_assert);
        implied_facts.push_back(to_assert);
    }

    /*
     * int2str(str2int(int2str(x))) = int2str(x)
     * int2str(str2int("0" "0" ... int2str(x))) = int2str(x)
     */
    bool theory_trau::quickpath_int2str(expr* num, expr* str, bool cached){
        expr* arg0 = nullptr;
        if (u.str.is_stoi(num, arg0)){
            if (u.str.is_itos(arg0)) {
                expr *to_assert = rewrite_implication(createEqualOP(str, u.str.mk_itos(num)), createEqualOP(str, arg0));
                assert_axiom(to_assert);
                if (cached)
                    implied_facts.push_back(to_assert);
                return true;
            }
            else if (u.str.is_concat(arg0)){
                ptr_vector <expr> nodes;
                get_nodes_in_concat(arg0, nodes);
                if (u.str.is_itos(nodes[nodes.size() - 1])) {
                    expr* zero = u.str.mk_string(zstring("0"));
                    for (unsigned i = 0; i < nodes.size() - 1; ++i) {
                        if (nodes[i] != zero)
                            return false;
                    }
                    expr *to_assert = rewrite_implication(createEqualOP(str, u.str.mk_itos(num)), createEqualOP(str, nodes[nodes.size() - 1]));
                    assert_axiom(to_assert);
                    if (cached)
                        implied_facts.push_back(to_assert);
                    return true;
                }
            }
        }
        return false;
    }

    expr* theory_trau::unroll_str2int(expr* n){
        
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " " << mk_pp(n, m) << std::endl;);
        rational ten(10);
        rational zero(0);
        rational zeroChar(48);
        rational coeff(1);
        expr_ref_vector adds(m);
        rational pos = str_int_bound - rational(1);
        expr* arr = get_var_flat_array(n);
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " " << mk_pp(arr, m) << std::endl;);
        while (pos >= zero){
            adds.push_back(createMulOP(createSelectOP(arr, mk_int(pos)), mk_int(coeff)));
            rational base = zeroChar * coeff * rational(-1);
            adds.push_back(mk_int(base));
            pos = pos - 1;
            coeff = coeff * ten;
        }
        return createAddOP(adds);
    }

    expr* theory_trau::unroll_str_int(expr* num, expr* str){
        
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " " << mk_pp(str, m) << std::endl;);
        rational ten(10);
        rational one(1);
        rational zero(0);
        rational zeroChar(48);
        rational pos = str_int_bound - one;
        expr* arr = get_var_flat_array(str);
        SASSERT(arr);
        expr* strLen = mk_strlen(str);
        expr_ref_vector ands(m);
        ands.push_back(rewrite_implication(createEqualOP(strLen, mk_int(0)), createEqualOP(num, mk_int(- 1))));


        expr_ref_vector ands_tmp(m);
        rational consider_len = str_int_bound;

        if (is_char_at(str))
            consider_len = one;

        for (rational len = one; len <= consider_len; len = len + one) {
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
                    at_pos = createSelectOP(arr, createAddOP(adds_tmp));
                }
                else
                    at_pos = createSelectOP(arr, mk_int(pos));
                adds.push_back(createMulOP(at_pos, mk_int(coeff)));
                rational base = zeroChar * coeff * rational(-1);
                adds.push_back(mk_int(base));
                pos = pos - 1;
                coeff = coeff * ten;
            }

            expr* premise = nullptr;
            if (len == str_int_bound)
                premise = createGreaterEqOP(strLen, mk_int(len));
            else
                premise = createEqualOP(strLen, mk_int(len));
            expr* conclusion = createEqualOP(num, createAddOP(adds));
            ands_tmp.push_back(rewrite_implication(premise, conclusion));
        }

        // if !valid --> value = -1, else ands_tmp
        expr* valid_s2i = valid_str_int(str);
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " valid_s2i: " << mk_pp(valid_s2i, m) << std::endl;);
        ands.push_back(rewrite_implication(valid_s2i, createAndOP(ands_tmp)));
        ands.push_back(rewrite_implication(mk_not(m, valid_s2i), createEqualOP(num, mk_int(- 1))));
        return createAndOP(ands);
    }

    expr* theory_trau::valid_str_int(expr* str){
        if (is_char_at(str)){
            
            expr *arr = get_var_flat_array(str);
            expr_ref_vector conclusions(m);
            conclusions.push_back(createGreaterEqOP(
                    createSelectOP(arr, mk_int(0)),
                    mk_int('0')));
            conclusions.push_back(createLessEqOP(
                    createSelectOP(arr, mk_int(0)),
                    mk_int('9')));
            return createAndOP(conclusions);
        }
        else {
            // from 0 - q_bound
            
            expr_ref_vector ands(m);
            expr *arr = get_var_flat_array(str);
            expr *strLen = mk_strlen(str);
            for (int i = 0; i < q_bound.get_int64(); ++i) {
                expr *premise = createGreaterEqOP(strLen, mk_int(i + 1));
                expr_ref_vector conclusions(m);
                conclusions.push_back(createGreaterEqOP(
                        createSelectOP(arr, mk_int(i)),
                        mk_int('0')));
                conclusions.push_back(createLessEqOP(
                        createSelectOP(arr, mk_int(i)),
                        mk_int('9')));
                ands.push_back(rewrite_implication(premise, createAndOP(conclusions)));
            }

            for (int i = 0; i < str_int_bound; ++i) {
                expr *premise = createGreaterEqOP(strLen, mk_int(q_bound.get_int64() + i));
                rational to_minus = rational(-1) * rational(i);
                expr *pos = createAddOP(strLen, mk_int(to_minus));

                expr_ref_vector conclusions(m);
                conclusions.push_back(createGreaterEqOP(
                        createSelectOP(arr, pos),
                        mk_int('0')));
                conclusions.push_back(createLessEqOP(
                        createSelectOP(arr, pos),
                        mk_int('9')));
                ands.push_back(rewrite_implication(premise, createAndOP(conclusions)));
            }
            return createAndOP(ands);
        }
    }

    bool theory_trau::is_char_at(expr* str){
        if (u.str.is_at(str))
            return true;
        else {
            std::string name_str = expr2str(str);
            if (name_str.find("charAt1") == 0)
                return true;
        }
        return false;
    }

    /*
     * 0 <= val < 10 --> len < 2
     * 10 <= val < 100 --> len < 3
     * ..
     * -1 >= val > -10 --> len < 3
     * -10 >= val > -100 --> len < 4
     */
    expr* theory_trau::lower_bound_str_int(expr* num, expr* str){
        
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
            expr* premise = createGreaterEqOP(num, mk_int(powerOf));
            expr* conclusion = createGreaterEqOP(len_e, mk_int(len));
            ands.push_back(rewrite_implication(premise, conclusion));
        }
//        ands.push_back(createLessEqOP(len_e, mk_int(str_int_bound)));
        return createAndOP(ands);
    }

    /*
     * 0 <= val < 10 --> len < 2
     * 10 <= val < 100 --> len < 3
     * ...
     */
    expr* theory_trau::lower_bound_int_str(expr* num, expr* str){
        
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
            tmpAnds.push_back(createGreaterEqOP(num, mk_int(prePower)));
            tmpAnds.push_back(createLessEqOP(num, mk_int(powerOf_minus_one)));
            ands.push_back(rewrite_implication(
                    createAndOP(tmpAnds),
                    createEqualOP(mk_strlen(str), mk_int(len_minus_one))));
            prePower = powerOf;
        }
        ands.push_back(createLessEqOP(len_e, mk_int(str_int_bound)));
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(createAndOP(ands), m) << std::endl;);
        return createAndOP(ands);
    }

    expr* theory_trau::fill_0_1st_loop(expr* num, expr* str){
        
        if (is_char_at(str))
            return m.mk_true();

        expr_ref_vector ands(m);

        rational one(1);
        rational len = str_int_bound;
        rational zero_char(48);
        expr* zero_e = mk_int(zero_char);
        expr* arr = get_var_flat_array(str);
        expr* len_n = mk_strlen(str);

        while (len < str_int_bound + q_bound){
            expr* premise = createGreaterEqOP(len_n, mk_int(len));

            rational tmp = len - str_int_bound;
            expr* conclusion = createEqualOP(createSelectOP(arr, mk_int(tmp)), zero_e);
            ands.push_back(rewrite_implication(premise, conclusion));
            len = len + 1;
        }

        expr* premise = createGreaterEqOP(num, mk_int(0));

        return rewrite_implication(premise, createAndOP(ands));
    }

    void theory_trau::print_eq_combination(obj_map<expr, ptr_vector<expr>> const& eq_combination, int line){
        
        for (const auto& com : eq_combination){
            if (com.m_value.size() == 1 && com.m_key == com.m_value[0])
                continue;
            if (line > 0) {
                STRACE("str", tout << line << " EQ set of " << mk_pp(com.m_key, m) << std::endl;);
            }
            else
                STRACE("str", tout << "EQ set of " << mk_pp(com.m_key, m) << std::endl;);
            for (const auto& e : com.get_value())
            STRACE("str",
                   if (!u.str.is_concat(e))
                       tout << "\t\t" << mk_pp(e, m) << std::endl;
                   else {
                       ptr_vector<expr> nodes;
                       get_nodes_in_concat(e, nodes);
                       tout << "\t\t";
                       for (unsigned i = 0; i < nodes.size(); ++i)
                           tout << mk_pp(nodes[i], m)  << " ";
                       tout << std::endl;
                   });
        }
    }

    bool theory_trau::is_equal(UnderApproxState const& preState, UnderApproxState const& currState){
        return false;

        obj_map<expr, ptr_vector<expr>> _eq_combination = preState.eq_combination;

        if (_eq_combination.size() != currState.eq_combination.size()) {
            STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << ": " << _eq_combination.size() << " vs " << currState.eq_combination.size() <<  std::endl;);
            return false;
        }

        for (const auto& v : currState.non_fresh_vars)
            if (!preState.non_fresh_vars.contains(v.m_key)) {
                expr_ref_vector eqs(m);
                collect_eq_nodes(v.m_key, eqs);
                bool found = false;
                for (const auto& eq : eqs)
                    // check if there are any equivalent variables
                    if (preState.non_fresh_vars.contains(eq)) {
                        found = true;
                        break;
                    }

                if (!found) {
                    STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " NOT EQ " << mk_pp(v.m_key, m) << std::endl;);
                    return false;
                }
            }

        expr_ref_vector checked(m);

        for (const auto& n : currState.eq_combination) {
            ptr_vector <expr> comb;
            if (_eq_combination.contains(n.m_key)) {
                comb.append(_eq_combination[n.m_key]);
                checked.push_back(n.m_key);
            }
            else {
                // check if there are any equivalent combinations
                expr_ref_vector eqs(m);
                collect_eq_nodes(n.m_key, eqs);
                for (const auto& eq : eqs)
                    if (_eq_combination.contains(eq)){
                        comb.append(_eq_combination[eq]);
                        checked.push_back(eq);
                        break;
                    }
            }


            for (const auto &e : n.get_value()) {

                if (!comb.contains(e)) {
                    // check if there are any equivalent combinations, can be the case that some empty variables are omitted
                    if (!are_some_empty_vars_omitted(e, comb)) {
                        STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " NOT EQ " << mk_pp(n.m_key, m) << " == " << mk_pp(e, m) << std::endl;);
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
                if (!checked.contains(n.m_key)) {
                    // it is not in curr_state.eq_combination
                    if (!is_trivial_combination(n.m_key, n.get_value(), currState.non_fresh_vars))
                        return false;
                }
        }

        return true;
    }

    bool theory_trau::are_some_empty_vars_omitted(expr* n, ptr_vector<expr> const& v){
        
        ptr_vector <expr> elements;
        get_nodes_in_concat(n, elements);
        rational len;
        for (const auto& nn : v){
            ptr_vector <expr> tmp;
            get_nodes_in_concat(nn, tmp);
            if (elements.size() <= tmp.size()){
                int pos = 0;

                for (unsigned i = 0; i < tmp.size(); ++i){
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
                if (pos == (int)elements.size())
                    return true;
            }
        }
        return false;
    }

    bool theory_trau::is_equal(expr_ref_vector const& corePrev, expr_ref_vector const& coreCurr){
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << std::endl;);

        if (coreCurr.size() != corePrev.size())
            return false;

        for (const auto& e : coreCurr)
            if (!corePrev.contains(e))
                return false;

        return true;
    }

    bool theory_trau::underapproximation_cached(){
        

        expr_ref_vector guessed_exprs(m);
        fetch_guessed_exprs_from_cache(uState, guessed_exprs);
        expr* causexpr = createAndOP(guessed_exprs);

        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** eqLevel = " << uState.eqLevel << "; bound = " << uState.str_int_bound << " @lvl " << m_scope_level << std::endl;);
        if (uState.asserting_constraints.size() > 0)
            init_underapprox_cached();
        bool axiomAdded = false;

//        for (const auto& a : uState.asserting_constraints){
//            axiomAdded = true;
//            ensure_enode(a);
//
//            if (m.is_and(a)) {
//                assert_axiom(rewrite_implication(causexpr, a));
//            }
//            else
//                assert_axiom(a);
//        }

        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** completed_branches" << completed_branches.size() << std::endl;);
        for (const auto& b : completed_branches){
            expr_ref_vector b_guessed_exprs(m);
            fetch_guessed_exprs_from_cache(b, b_guessed_exprs);
            causexpr = createAndOP(b_guessed_exprs);
            for (const auto& a : b.asserting_constraints){
                axiomAdded = true;
                ensure_enode(a);

                if (m.is_and(a)) {
                    assert_axiom(rewrite_implication(causexpr, a));
                }
                else
                    assert_axiom(a);
            }
        }
        return axiomAdded;
    }

    void theory_trau::handle_diseq_notcontain(bool cached){
        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " cached = " << cached << " @lvl " << m_scope_level << "\n";);
        if (!cached){
            handle_disequalities();
            handle_not_contain();
        }
        else {
            handle_disequalities_cached();
            handle_not_contain_cached();
        }

    }

    void theory_trau::handle_disequalities(){
        for (const auto &wi : m_wi_expr_memo) {
            if (!u.str.is_empty(wi.second.get()) && !u.str.is_empty(wi.first.get())) {
                expr* lhs = wi.first.get();
                expr* rhs = wi.second.get();
                expr* contain = nullptr;
                if (!is_contain_equality(lhs, contain) && !is_contain_equality(rhs, contain)) {
                    handle_disequality(lhs, rhs);
                }
            }
        }
    }

    void theory_trau::handle_disequalities_cached(){
        for (const auto& b : completed_branches) {
            for (const auto &wi : b.disequalities) {
                SASSERT(to_app(wi)->get_num_args() == 1);
                expr *equality = to_app(wi)->get_arg(0);

                SASSERT(to_app(equality)->get_num_args() == 2);
                expr *lhs = to_app(equality)->get_arg(0);
                expr *rhs = to_app(equality)->get_arg(1);
                if (!u.str.is_empty(lhs) && !u.str.is_empty(lhs)) {
                    expr *contain = nullptr;
                    if (!is_contain_equality(lhs, contain) && !is_contain_equality(rhs, contain)) {
                        handle_disequality(lhs, rhs);
                    }
                }
            }
        }
    }

    void theory_trau::handle_disequality(expr *lhs, expr *rhs){
        expr* contain = nullptr;
        if (!is_contain_equality(lhs, contain) && !is_contain_equality(rhs, contain)) {
            
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
                handle_disequality_const(rhs, value);
            else if (constRhs != nullptr && u.str.is_string(constRhs, value))
                handle_disequality_const(lhs, value);
            else
                handle_disequality_var(lhs, rhs);

        }
    }

    bool theory_trau::review_disequalities_not_contain(obj_map<expr, ptr_vector<expr>> const& eq_combination){
        for (const auto &wi : m_wi_expr_memo) {
            if (!u.str.is_empty(wi.second.get()) && !u.str.is_empty(wi.first.get())) {
                expr* lhs = wi.first.get();
                expr* rhs = wi.second.get();
                expr* contain = nullptr;
                if (is_contain_equality(lhs, contain)){
                    if (!review_not_contain(rhs, contain, eq_combination)){
                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " Invalid (" << mk_pp(lhs, m) << " != " << mk_pp(rhs, m) << ")\n";);
                        return false;
                    }
                }
                else if (is_contain_equality(rhs, contain)){
                    if (!review_not_contain(lhs, contain, eq_combination)){
                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " Invalid (" << mk_pp(lhs, m) << " != " << mk_pp(rhs, m) << ")\n";);
                        return false;
                    }
                }
                else {
                    if (!review_disequality(lhs, rhs, eq_combination)) {
                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " Invalid (" << mk_pp(lhs, m) << " != " << mk_pp(rhs, m) << ")\n";);
                        return false;
                    }
                }
            }
        }
        return true;
    }

    bool theory_trau::review_not_contain(expr* lhs, expr* needle, obj_map<expr, ptr_vector<expr>> const& eq_combination){
        
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(lhs, m) << " not contain " << mk_pp(needle, m) << ")\n";);
        expr* new_needle = remove_empty_in_concat(needle);
        if (!review_notcontain_trivial(lhs, new_needle)){
            return false;
        }
        context & ctx = get_context();
        expr* root_lhs = ctx.get_enode(lhs)->get_root()->get_owner();
        if (u.str.is_string(lhs))
            root_lhs = lhs;

        if (eq_combination.contains(root_lhs)){
            for (const auto& s : eq_combination[root_lhs]){
                ptr_vector <expr> nodes;
                get_nodes_in_concat(s, nodes);
                for (const auto& nn : nodes)
                    if (in_same_eqc(nn, new_needle)) {
                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " Invalid (" << mk_pp(root_lhs, m) << " not contain " << mk_pp(needle, m) << ")\n";);
                        return false;
                    }
            }
        }

        return true;
    }

    expr* theory_trau::remove_empty_in_concat(expr* s){
        ptr_vector <expr> nodes;
        get_nodes_in_concat(s, nodes);

        ptr_vector <expr> new_nodes;
        rational ra;
        for (const auto& ss : nodes)
            if (get_len_value(ss, ra) && ra.get_int64() == 0){

            }
            else {
                new_nodes.push_back(ss);
            }
        return create_concat_from_vector(new_nodes);
    }

    bool theory_trau::review_notcontain_trivial(expr* lhs, expr* needle){

        expr_ref_vector eqs(m);
        collect_eq_nodes(lhs, eqs);
        for (const auto& eq: eqs) {
            ptr_vector<expr> nodes;
            get_nodes_in_concat(eq, nodes);
            for (const auto &nn : nodes)
                if (in_same_eqc(nn, needle)) {
                    
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " Invalid (" << mk_pp(lhs, m) << " not contain " << mk_pp(needle, m) << ")\n";);
                    return false;
                }
        }
        return true;
    }

    bool theory_trau::review_disequality(expr* lhs, expr* rhs, obj_map<expr, ptr_vector<expr>> const& eq_combination){

        if (!review_disequality_trivial(lhs, rhs)){
            return false;
        }
        context & ctx = get_context();
        expr* root_lhs = ctx.get_enode(lhs)->get_root()->get_owner();
        expr* root_rhs = ctx.get_enode(rhs)->get_root()->get_owner();
        if (u.str.is_string(lhs))
            root_lhs = lhs;

        if (u.str.is_string(root_rhs))
            root_rhs = rhs;

        if (eq_combination.contains(root_lhs) && eq_combination.contains(root_rhs)){
            for (const auto& s : eq_combination[root_lhs])
                for (const auto& ss: eq_combination[root_rhs]){
                    if (are_equal_concat(s, ss))
                        return false;
                }
        }

        return true;
    }

    bool theory_trau::review_disequality_trivial(expr* lhs, expr* rhs){

        ptr_vector <expr> lhs_nodes;
        get_nodes_in_concat(lhs, lhs_nodes);
        ptr_vector <expr> rhs_nodes;
        get_nodes_in_concat(rhs, rhs_nodes);

        unsigned counter_l = 0;
        unsigned counter_r = 0;
        while (counter_l < lhs_nodes.size() || counter_r < rhs_nodes.size()){
            rational len;
            if (counter_l < lhs_nodes.size() && get_len_value(lhs_nodes[counter_l], len) && len.get_int64() == 0) {
                ++counter_l;
                continue;
            }

            if (counter_r < rhs_nodes.size() && get_len_value(rhs_nodes[counter_r], len) && len.get_int64() == 0) {
                ++counter_r;
                continue;
            }

            if (counter_l < lhs_nodes.size() && counter_r < rhs_nodes.size()){
                if (in_same_eqc(rhs_nodes[counter_r], lhs_nodes[counter_l])) {
                    ++counter_r;
                    ++counter_l;
                }
                else
                    return true;
            }
            else
                return true;
        }
        return false;
    }

    void theory_trau::handle_disequality_var(expr *lhs, expr *rhs){
        
        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " not (" << mk_pp(lhs, m) << " = " << mk_pp(rhs, m) << ")\n";);

        expr_ref_vector cases(m);
        expr_ref lenLhs(mk_strlen(lhs), m);
        expr_ref lenRhs(mk_strlen(rhs), m);
        expr_ref eqref(createEqualOP(lenLhs.get(),lenRhs.get()), m);
        cases.push_back(mk_not(m, eqref));

        int len1, len2;
        if (is_non_fresh(lhs, len1) && is_non_fresh(rhs, len2) && is_var_var_inequality(lhs, rhs)) {
            rational len_lhs;
            rational len_rhs;
            int bound = std::min(len1, len2);
            if (get_len_value(lhs, len_lhs) && get_len_value(rhs, len_rhs)) {
                if (len_lhs != len_rhs)
                    return;
                else {
                    bound = len_lhs.get_int64();
                }
            }
            expr* arrLhs = get_var_flat_array(lhs);
            expr* arrRhs = get_var_flat_array(rhs);
            if (arrLhs != nullptr && arrRhs != nullptr) {
                STRACE("str", tout << __LINE__ << " min len: " << bound << "\n";);
                for (int i = 0; i < bound; ++i) {
                    expr_ref_vector subcases(m);
                    subcases.push_back(createGreaterEqOP(lenLhs.get(), m_autil.mk_int(i + 1)));
                    STRACE("str", tout << __LINE__ << "  " << mk_pp(subcases[0].get(), m) << ")\n";);
                    subcases.push_back(createGreaterEqOP(lenRhs.get(), m_autil.mk_int(i + 1)));
                    STRACE("str", tout << __LINE__ << "  " << mk_pp(arrLhs, m) << "  " << mk_pp(arrRhs, m) << ")\n";);
                    expr_ref tmp(createEqualOP(createSelectOP(arrLhs, m_autil.mk_int(i)),
                                               createSelectOP(arrRhs, m_autil.mk_int(i))), m);
                    STRACE("str", tout << __LINE__ << "  " << mk_pp(tmp.get(), m) << ")\n";);
                    subcases.push_back(mk_not(m, tmp.get()));
                    cases.push_back(createAndOP(subcases));
                }

                expr *assertExpr = createOrOP(cases);
                assert_axiom(rewrite_implication(mk_not(m, createEqualOP(lhs, rhs)), assertExpr));
            }
        }


    }

    void theory_trau::handle_disequality_const(expr *lhs, zstring rhs){
        
        expr_ref_vector cases(m);
        expr_ref lenLhs(mk_strlen(lhs), m);
        expr_ref lenRhs(mk_int(rhs.length()), m);
        expr_ref eqref(createEqualOP(lenLhs.get(),lenRhs.get()), m);
        expr_ref notLenEq(mk_not(m, eqref.get()), m);

        cases.push_back(notLenEq);
        int val = -1;
        if (is_non_fresh(lhs, val) && !is_trivial_inequality(lhs, rhs)) {
            STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " not (" << mk_pp(lhs, m) << " = " << rhs << ")\n";);
            expr* arrLhs = get_var_flat_array(lhs);
            if (arrLhs == nullptr)
                return;

            for (unsigned i = 0; i < rhs.length(); ++i) {
                expr_ref_vector subcases(m);
                subcases.push_back(createGreaterEqOP(lenLhs.get(), m_autil.mk_int(i + 1)));
                expr_ref tmp(createEqualOP(createSelectOP(arrLhs, m_autil.mk_int(i)), m_autil.mk_int(rhs[i])), m);
                subcases.push_back(mk_not(m, tmp));
                cases.push_back(createAndOP(subcases));
            }
            expr_ref premise(mk_not(m, createEqualOP(lhs, u.str.mk_string(rhs))), m);
            ensure_enode(premise.get());
            expr_ref conclusion(createOrOP(cases), m);


            expr_ref tmpAxiom(createEqualOP(premise.get(), conclusion.get()), m);
            assert_axiom(tmpAxiom.get());
        }

    }

    void theory_trau::handle_not_contain(){
        for (const auto &wi : m_wi_expr_memo) {
            if (!u.str.is_empty(wi.second.get()) && !u.str.is_empty(wi.first.get())) {
                expr* lhs = wi.first.get();
                expr* rhs = wi.second.get();

                handle_not_contain(lhs, rhs);
            }
        }
    }

    void theory_trau::handle_not_contain_cached(){
        for (const auto &wi : uState.disequalities) {
            expr* equality = to_app(wi)->get_arg(0);

            expr* lhs = to_app(equality)->get_arg(0);
            expr* rhs = to_app(equality)->get_arg(1);

            handle_not_contain(lhs, rhs, true);
        }
    }

    void theory_trau::handle_not_contain(expr *lhs, expr *rhs, bool cached){
        
        expr* contain = nullptr;
        expr* premise = mk_not(m, createEqualOP(lhs, rhs));
        if (is_contain_equality(lhs, contain)) {
            zstring value;
            if (u.str.is_string(contain, value))
                handle_not_contain_const(rhs, value, premise, cached);
            else
                handle_not_contain_var(rhs, contain, premise, cached);
        }
        else if (is_contain_equality(rhs, contain)) {
            zstring value;
            if (u.str.is_string(contain, value))
                handle_not_contain_const(lhs, value, premise, cached);
            else
                handle_not_contain_var(lhs, contain, premise, cached);
        }
    }

    void theory_trau::handle_not_contain_var(expr *lhs, expr *rhs, expr *premise, bool cached){

    }

    void theory_trau::handle_not_contain_const(expr *lhs, zstring rhs, expr *premise, bool cached){
        zstring tmp("U");
        if (rhs == tmp)
            return;
        
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



        if (is_non_fresh(lhs, bound) && !is_trivial_contain(rhs)){
            expr_ref_vector cases(m);
            expr* lenExpr = mk_strlen(lhs);
            expr* arr = get_var_flat_array(lhs);

            if (arr == nullptr)
                return;

            for (int i = (int)rhs.length(); i <= bound; ++i){
                expr_ref_vector subcases(m);
//                subcases.push_back(createLessEqOP(lenExpr, mk_int(i - 1)));
                for (unsigned k = 0; k < rhs.length(); ++k) {
                    unsigned pos = k + i - rhs.length();
                    subcases.push_back(mk_not(m, createEqualOP(
                            createSelectOP(arr, mk_int(pos)),
                            mk_int(rhs[k]))));
                }
                cases.push_back(createOrOP(subcases));
            }
            cases.push_back(createLessEqOP(lenExpr, mk_int(bound)));

            expr_ref axiom(createAndOP(cases), m);
            assert_axiom(createEqualOP(premise, axiom.get()));
//            assert_axiom(axiom.get(), mk_not(m, mk_contains(lhs, u.str.mk_string(rhs))));

//            expr_ref tmpAxiom(createEqualOP(mk_not(m, mk_contains(lhs, u.str.mk_string(rhs))), axiom.get()), m);
//            uState.add_asserting_constraints(axiom);
        }
    }

    bool theory_trau::is_trivial_contain(zstring s){
        for (unsigned i = 0; i < s.length(); ++i)
            if (sigma_domain.find(s[i]) == sigma_domain.end())
                return true;

        return false;
    }

    bool theory_trau::is_contain_equality(expr* n){
        expr_ref_vector eqs(m);
        collect_eq_nodes(n, eqs);
        for  (const auto& nn : eqs) {
            if (u.str.is_concat(nn)) {
                ptr_vector<expr> nodes;
                get_nodes_in_concat(nn, nodes);
                if (nodes.size() >= 3) {
                    // check var name
                    std::string n1 = expr2str(nodes[0]);
                    std::string n3 = expr2str(nodes[nodes.size() - 1]);
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
            if (is_haystack(nn))
                return true;
        }

        return false;
    }

    bool theory_trau::is_contain_equality(expr* n, expr* &contain){
        if (u.str.is_concat(n)){
            ptr_vector<expr> nodes;
            get_nodes_in_concat(n, nodes);
            if (nodes.size() >= 3) {
                // check var name
                std::string n1 = expr2str(nodes[0]);
                std::string n3 = expr2str(nodes[nodes.size() - 1]);
                if ((n1.find("pre_contain!tmp") != std::string::npos &&
                     n3.find("post_contain!tmp") != std::string::npos) ||
                    (n1.find("indexOf1!tmp") != std::string::npos &&
                     n3.find("indexOf2!tmp") != std::string::npos) ||
                        (n1.find("replace1!tmp") != std::string::npos &&
                         n3.find("replace2!tmp") != std::string::npos)) {
                    nodes.pop_back();
                    contain = create_concat_from_vector(nodes, 0);
                    return true;
                }
            }
        }
        contain = nullptr;
        return false;
    }

    void theory_trau::static_analysis(obj_map<expr, ptr_vector<expr>> const& eq_combination){
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << connectingSize << std::endl;);

        obj_hashtable<expr> all_str_exprs;
        obj_hashtable<expr> all_consts;
        for (const auto& v : eq_combination){
            expr_ref_vector eqs(m);
            collect_eq_nodes(v.m_key, eqs);
            for (unsigned i = 0; i < eqs.size(); ++i)
                all_str_exprs.insert(eqs[i].get());

            if (u.str.is_string(v.m_key) && v.m_value.size() > 0)
                all_consts.insert(v.m_key);

            for (const auto& eq : v.get_value()){
                if (is_app(eq)){
                    ptr_vector<expr> nodes;
                    get_nodes_in_concat(eq, nodes);
                    for (unsigned i = 0; i < nodes.size(); ++i) {
                        all_str_exprs.insert(nodes[i]);
                        if (u.str.is_string(nodes[i]))
                            all_consts.insert(nodes[i]);
                    }
                }
            }
        }

        // calculate sum consts
        int sumConst = 0;
        for (const auto& s: all_consts){
            zstring tmp;
            u.str.is_string(s, tmp);
            sumConst += tmp.length();
        }

        sumConst = std::min(sumConst, 100);

        int maxInt = -1;

        for (const auto& v: all_str_exprs){
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
        for (const auto& v: all_str_exprs){
            if (!is_internal_var(v) && !u.str.is_string(v))
                cnt++;
        }
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << maxInt << " " << cnt << " " << sumConst << std::endl;);
        connectingSize = std::min(maxInt + cnt + sumConst, std::max(300, maxInt));
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << connectingSize << std::endl;);
    }

    void theory_trau::init_underapprox(
            obj_map<expr, ptr_vector<expr>> const& eq_combination, obj_map<expr, int> &non_fresh_vars){
        static_analysis(eq_combination);
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << connectingSize << std::endl;);
        
        context & ctx = get_context();
        expr_ref_vector all_str_exprs(m);
        flat_var_counter = 0;
        for (const auto& v : eq_combination){
            if (is_app(v.m_key)) {
                app *ap = to_app(v.m_key);
                if (!u.str.is_concat(ap)) {
                    if (!all_str_exprs.contains(v.m_key))
                        all_str_exprs.push_back(v.m_key);
                }
                else {
                    if (is_non_fresh(v.m_key, non_fresh_vars))
                        if (!all_str_exprs.contains(v.m_key))
                            all_str_exprs.push_back(v.m_key);
                    ptr_vector<expr> nodes;
                    get_nodes_in_concat(v.m_key, nodes);
                    for (unsigned i = 0; i < nodes.size(); ++i) {
                        if (!all_str_exprs.contains(nodes[i]))
                            all_str_exprs.push_back(nodes[i]);
                    }
                    expr* tmp = ctx.get_enode(v.m_key)->get_root()->get_owner();
                    if (!u.str.is_concat(tmp)) {
                        if (!all_str_exprs.contains(tmp))
                            all_str_exprs.push_back(tmp);
                    }
                    else {
                        expr_ref_vector eqs(m);
                        collect_eq_nodes(tmp, eqs);
                        for (unsigned i = 0; i < eqs.size(); ++i)
                            if (!u.str.is_concat(eqs[i].get())) {
                                if (!all_str_exprs.contains(eqs[i].get()))
                                    all_str_exprs.push_back(eqs[i].get());
                                break;
                            }
                    }

                }
            }

            for (const auto& eq : v.get_value()){
                if (is_app(eq)){
                    ptr_vector<expr> nodes;
                    get_nodes_in_concat(eq, nodes);
                    for (unsigned i = 0; i < nodes.size(); ++i)
                        if (!all_str_exprs.contains(nodes[i]))
                            all_str_exprs.push_back(nodes[i]);
                }
            }
        }

        for (const auto& we: non_membership_memo) {
            all_str_exprs.push_back(we.first);
        }

        for (const auto& we: membership_memo) {
            all_str_exprs.push_back(we.first);
        }

        obj_map<expr, int> str_int_vars;
        collect_non_fresh_vars_str_int(str_int_vars);
        setup_flats();
        for (const auto& we: str_int_vars) {
            all_str_exprs.push_back(we.m_key);
        }

        // create all tmp vars
        for(const auto& v : all_str_exprs){
            mk_and_setup_arr(v, non_fresh_vars);
        }

        create_notcontain_map();
        create_const_set();

        init_connecting_size(eq_combination, non_fresh_vars, false);
        init_connecting_size(eq_combination, non_fresh_vars);
        create_appearance_map(eq_combination);
    }

    void theory_trau::mk_and_setup_arr(
            expr* v,
            obj_map<expr, int> &non_fresh_vars){
        
        context & ctx = get_context();

        expr* arr_var = get_var_flat_array(v);
        if (arr_var != nullptr) {
            // check if we can use that: cannot use if two nodes are not equal

            ensure_enode(arr_var);
            std::string arr_str = expr2str(arr_var);
            SASSERT(arr_str.find_last_of("!", arr_str.length() - 3) != std::string::npos);

            arr_str = arr_str.substr(0, arr_str.find_last_of("!", arr_str.length() - 3));

            if (arr_str[0] == '|')
                arr_str = arr_str.substr(1, arr_str.length() - 1);

            SASSERT(arr_linker.contains(arr_var));
            if (!are_equal_exprs(v, arr_linker[arr_var])) {
                STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** changing array " << mk_pp(v, m)  << " " << mk_pp(arr_var, m) << std::endl;);
                arr_var = nullptr;
            }
            else {
                STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** reuse existing array " << mk_pp(v, m) << " " << mk_pp(arr_var, m) << " " << std::endl;);
                zstring val;
                if (u.str.is_string(v, val)) {
                    if (v != arr_linker[arr_var])
                        setup_str_const(val, arr_var, createEqualOP(v, arr_linker[arr_var]));
                    else
                        setup_str_const(val, arr_var);
                }
                return;
            }
        }

        if ((!u.str.is_concat(v) || non_fresh_vars.contains(v)) && arr_var == nullptr) {
            zstring flat_arr = gen_flat_arr(std::make_pair(ctx.get_enode(v)->get_root()->get_owner(), 0));
            expr_ref v1(m);
            if (array_map_reverse.contains(flat_arr)) {
                v1 = array_map_reverse[flat_arr];
            }
            else {
                v1 = mk_arr_var(flat_arr);
                array_map_reverse.insert(flat_arr, v1);
                STRACE("str", tout << __LINE__ << " making arr: " << flat_arr << " --> " << mk_pp(v1, m) << std::endl;);
                arr_linker.insert(v1, v);
            }

            {
                expr_ref_vector eqs(m);
                collect_eq_nodes(v, eqs);

                for (const auto& vv : eqs)
                    array_map.insert(vv, v1);
            }


            STRACE("str", tout << __LINE__ << " arr: " << flat_arr << " : " << mk_pp(v1, m) << std::endl;);

            zstring val;
            expr* rexpr = nullptr;
            if (u.str.is_string(v, val)){
                setup_str_const(val, v1);
            }
            else if (is_internal_regex_var(v, rexpr)) {
                if (!non_fresh_vars.contains(v)) {
                    STRACE("str", tout << __LINE__ << " arr: " << flat_arr << " : " << mk_pp(v, m) << std::endl;);
                    SASSERT(false);
                }
                expr *to_assert = setup_regex_var(v, rexpr, v1, rational(non_fresh_vars[v]), mk_int(0));
                assert_axiom(to_assert);
            }
            else if (is_str_int_var(v)){
                // setup_str_int_arr
            }
        }
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << std::endl;);
    }

    void theory_trau::setup_str_int_arr(expr* v, int start){
        
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << mk_pp(v, m) << std::endl;);
        expr_ref_vector ands(m);
        rational one(1);
        rational zero((int)('0'));
        rational nine((int)('9'));
        expr* arr = get_var_flat_array(v);
        expr* zero_e(mk_int(zero));
        expr* nine_e(mk_int(nine));
        for (rational i = one - one; i < str_int_bound; i = i + one){
            expr* rhs = leng_prefix_rhs(std::make_pair(v, start + 1), true);
            ands.push_back(createGreaterEqOP(createSelectOP(arr, createAddOP(rhs, mk_int(i))), zero_e));
            ands.push_back(createLessEqOP(createSelectOP(arr, createAddOP(rhs, mk_int(i))), nine_e));
        }

        expr *len = mk_strlen(v);

        // flat 1 = zero
        for (rational i = one; i <= q_bound; i = i + one) {
            rational total_len = str_int_bound + i;
            expr* premise = createGreaterEqOP(len, mk_int(total_len));
            rational j = i - one;
            expr* conclusion = createEqualOP(createSelectOP(arr, mk_int(j)), zero_e);
            ands.push_back(rewrite_implication(premise, conclusion));
        }

        expr_ref tmp(createAndOP(ands), m);
        assert_axiom(tmp.get());
        implied_facts.push_back(tmp);
    }

    void theory_trau::setup_str_const(zstring val, expr* arr, expr* premise){
        STRACE("str", tout << __LINE__ << " " << mk_pp(arr, m) << " = " << val << std::endl;);
        expr_ref_vector ands(m);
        for (unsigned i = 0; i < val.length(); ++i){
            ands.push_back(createEqualOP(createSelectOP(arr, mk_int(i)), mk_int(val[i])));
        }

        expr* to_assert = createAndOP(ands);
        if (premise != nullptr) {
            expr* tmp = rewrite_implication(premise, to_assert);
            assert_axiom(tmp);
            implied_facts.push_back(tmp);
        }
        else {
            assert_axiom(to_assert);
            implied_facts.push_back(to_assert);
        }
    }

    expr* theory_trau::setup_regex_var(expr* var, expr* rexpr, expr* arr, rational bound, expr* prefix){
        expr* ret = setup_char_range_arr(rexpr, arr, bound, prefix);
        if (ret != nullptr) {
        }
        else {
            STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " ***" << mk_pp(var, m) << std::endl;);
            vector<zstring> elements;
            expr_ref_vector ors(m);
            collect_alternative_components(rexpr, elements);
            for (unsigned i = 0; i < elements.size(); ++i) {
                expr_ref_vector ands(m);
                for (int j = 0; j < bound.get_int64(); ++j) {
                    int pos = j % elements[i].length();
                    ands.push_back(createEqualOP(createSelectOP(arr, createAddOP(prefix, mk_int(j))), mk_int(elements[i][pos])));
                }

                expr_ref tmp01(m_autil.mk_mod(mk_strlen(var), mk_int(elements[i].length())), m);
                m_rewrite(tmp01);
                STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " ***" << mk_pp(tmp01, m) << " " << elements[i] << " " << bound << std::endl;);

                ands.push_back(createEqualOP(tmp01, mk_int(0)));
                ors.push_back(createAndOP(ands));
            }
            ret = createOrOP(ors);
        }

        return ret;
    }

    expr* theory_trau::setup_char_range_arr(expr* e, expr* arr, rational bound, expr* prefix){
        vector<std::pair<int, int>> charRange = collect_char_range(e);
        if (charRange[0].first != -1) {
            expr_ref_vector ret(m);

            for (unsigned i = 0; i < bound.get_int64(); ++i) {
                expr_ref_vector ors(m);
                expr_ref_vector ors_range(m);
                for (unsigned j = 0; j < charRange.size(); ++j) {
                    expr_ref_vector ands(m);
                    ands.push_back(createGreaterEqOP(
                            createSelectOP(arr, createAddOP(prefix, m_autil.mk_int(i))),
                            m_autil.mk_int(charRange[j].first)));
                    ands.push_back(createLessEqOP(
                            createSelectOP(arr, createAddOP(prefix, m_autil.mk_int(i))),
                            m_autil.mk_int(charRange[j].second)));
                    ors_range.push_back(createAndOP(ands));
                }
                ret.push_back(createOrOP(ors_range));
            }
            return createAndOP(ret);
        }
        return nullptr;
    }

    void theory_trau::setup_flats(){
        if (should_use_flat() && p_bound == rational(0)) {
            p_bound = rational(2);
            q_bound = rational(5);
            assert_axiom(createEqualOP(get_bound_p_control_var(), mk_int(p_bound)));
            assert_axiom(createEqualOP(get_bound_q_control_var(), mk_int(q_bound)));
            if (p_bound >= max_p_bound)
                implied_facts.push_back(createEqualOP(get_bound_p_control_var(), mk_int(p_bound)));
            if (q_bound >= max_q_bound)
                implied_facts.push_back(createEqualOP(get_bound_q_control_var(), mk_int(q_bound)));
        }
        else if (should_use_flat() && (p_bound < max_p_bound || q_bound < max_q_bound)){
            if (p_bound < max_p_bound) {
//                p_bound = p_bound + rational(1);
                assert_axiom(createEqualOP(get_bound_p_control_var(), mk_int(p_bound)));
                if (p_bound >= max_p_bound)
                    implied_facts.push_back(createEqualOP(get_bound_p_control_var(), mk_int(p_bound)));
            }
            if (q_bound < max_q_bound) {
//                q_bound = q_bound + rational(5);
                assert_axiom(createEqualOP(get_bound_q_control_var(), mk_int(q_bound)));
                if (q_bound >= max_q_bound)
                    implied_facts.push_back(createEqualOP(get_bound_q_control_var(), mk_int(q_bound)));
            }
        }
    }

    bool theory_trau::should_use_flat(){
        if (string_int_vars.size() > 0)
            return true;
        return false;
    }

    void theory_trau::init_underapprox_cached(){
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << connectingSize << std::endl;);
        context & ctx = get_context();
        expr_ref_vector all_str_exprs(m);
        flat_var_counter = 0;
        for (const auto& v : uState.eq_combination){
            if (v.get_value().size() == 0)
                continue;
            ensure_enode(v.m_key);

            if (is_app(v.m_key)) {
                app *ap = to_app(v.m_key);
                if (!u.str.is_concat(ap)) {
                    if (!all_str_exprs.contains(v.m_key))
                        all_str_exprs.push_back(v.m_key);
                }
                else {
                    expr* tmp = ctx.get_enode(v.m_key)->get_root()->get_owner();
                    if (!u.str.is_concat(tmp)) {
                        if (!all_str_exprs.contains(tmp))
                            all_str_exprs.push_back(tmp);
                    }
                    else {
                        expr_ref_vector eqs(m);
                        collect_eq_nodes(tmp, eqs);
                        for (unsigned i = 0; i < eqs.size(); ++i)
                            if (!u.str.is_concat(eqs[i].get())) {
                                if (!all_str_exprs.contains(eqs[i].get()))
                                    all_str_exprs.push_back(eqs[i].get());
                                break;
                            }
                    }

                }
            }
            for (const auto& eq : v.get_value()){
                ensure_enode(eq);
                STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << mk_pp(eq, m) << std::endl;);
                if (is_app(eq)){
                    ptr_vector<expr> nodes;
                    get_nodes_in_concat(eq, nodes);
                    for (unsigned i = 0; i < nodes.size(); ++i)
                        if (!all_str_exprs.contains(nodes[i]))
                            all_str_exprs.push_back(nodes[i]);
                }
            }
        }

        for (const auto& we: non_membership_memo) {
            all_str_exprs.push_back(we.first);
        }

        for (const auto& we: membership_memo) {
            all_str_exprs.push_back(we.first);
        }

        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << connectingSize << std::endl;);
        obj_map<expr, int> str_int_vars;
        collect_non_fresh_vars_str_int(str_int_vars);
        for (const auto& we: str_int_vars) {
            all_str_exprs.push_back(we.m_key);
        }

        // create all tmp vars
        for(const auto& v : all_str_exprs){
            app *ap = to_app(v);
            expr* arrVar = get_var_flat_array(v);
            if (arrVar == nullptr)
                continue;
            if (!u.str.is_concat(ap) && arrVar == nullptr) {
                zstring flatArr = gen_flat_arr(std::make_pair(ctx.get_enode(v)->get_root()->get_owner(), 0));
                if (u.str.is_string(v))
                    flatArr = gen_flat_arr(std::make_pair(v, 0));

                expr_ref v1(m);
                if (array_map_reverse.contains(flatArr)) {
                    v1 = array_map_reverse[flatArr];

                    if (!ctx.e_internalized(v1.get())){
                        ctx.internalize(v1, false);
                    }
                }
                else {
                    v1 = mk_arr_var(flatArr);
                    array_map_reverse.insert(flatArr, v1);
                }
                {
                    expr_ref_vector eqs(m);
                    collect_eq_nodes(v, eqs);

                    for (const auto& vv : eqs)
                        array_map[vv] = v1;
                }
            }
            else if (arrVar != nullptr) {
                ensure_enode(arrVar);
                // I'm assuming that this combination will do the correct thing in the integer theory.
                m_trail.push_back(arrVar);
            }
        }
        for  (const auto& arr : array_map_reverse) {
            ensure_enode(arr.m_value);
        }
    }

    void theory_trau::create_notcontain_map(){
        
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
                        if (!not_contain_map.contains(rhs))
                            not_contain_map.insert(rhs, {});
                        not_contain_map[rhs].insert(exprVector[1]);
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
                        if (!not_contain_map.contains(lhs))
                            not_contain_map.insert(lhs, {});
                        not_contain_map[lhs].insert(exprVector[1]);
                    }
                }
            }
        }


    }

    void theory_trau::create_const_set(){
        const_set.reset();
        for (const auto _eq : uState.eq_combination) {
            zstring value;
            if (u.str.is_string(_eq.m_key, value)) {
                const_set.insert(value);
            }
            for (const auto v: _eq.get_value()){
                ptr_vector<expr> nodes;
                get_nodes_in_concat(v, nodes);
                /* push to map */
                for (unsigned i = 0; i < nodes.size(); ++i)
                    if (u.str.is_string(nodes[i], value)){
                        const_set.insert(value);
                    }
            }
        }
    }

    char theory_trau::setup_default_char(unsigned_set const& included_chars, unsigned_set const& exclude_chars){
        char default_char = 'a';
        for (const auto& ch : included_chars)
            if (exclude_chars.find(ch) == exclude_chars.end()) {
                default_char = ch;
                break;
            }
        return default_char;
    }

    theory_trau::unsigned_set theory_trau::init_excluded_char_set(){
        unsigned_set exclude_chars;
        for (const auto& s : const_set){
            for (unsigned i = 0; i < s.length(); ++i) {
                exclude_chars.insert(s[i]);
            }
        }
        return exclude_chars;
    }

    /*
     *
     */
    theory_trau::unsigned_set theory_trau::init_included_char_set(){
        unsigned_set included_chars;
        if (included_chars.size() == 0)
            for (unsigned i = 32; i <= 126; ++i)
                included_chars.insert(i);

        return included_chars;
    }

    void theory_trau::create_appearance_map(obj_map<expr, ptr_vector<expr>> const& eq_combination){
        appearance_map.reset();
        for (const auto& var : eq_combination){
            for (const auto& eq : var.get_value()) {
                ptr_vector<expr> nodes;
                get_nodes_in_concat(eq, nodes);
                for (unsigned i = 0; i < nodes.size(); ++i)
                    if (appearance_map.contains(nodes[i]))
                        appearance_map[nodes[i]].insert(var.m_key);
                    else {
                        expr_set tmp;
                        tmp.insert(var.m_key);
                        appearance_map.insert(nodes[i], tmp);
                    }
            }
        }
    }

    /*
     *
     */
    void theory_trau::init_connecting_size(
            obj_map<expr, ptr_vector<expr>> const& eq_combination,
            obj_map<expr, int> &non_fresh_vars, bool prep){
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << connectingSize << std::endl;);
        int oldConnectingSize = connectingSize;
        static_analysis(eq_combination);
        if (!prep){
            connectingSize = std::max(CONNECTINGSIZE, connectingSize);
        }
        for (auto &v : non_fresh_vars) {
            rational len;
            if (v.m_value == -1 || v.m_value == oldConnectingSize) {
                if (get_len_value(v.m_key, len)) {
                    if (get_assign_lvl(mk_strlen(v.m_key), mk_int(len)) == 0)
                        v.m_value = len.get_int64();
                    else
                        v.m_value = connectingSize;
                }
                else
                    v.m_value = connectingSize;
            }
        }
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << connectingSize << std::endl;);
    }

    bool theory_trau::convert_equalities(obj_map<expr, ptr_vector<expr>> const& eq_combination,
                                         obj_map<expr, int> & non_fresh_vars,
                                       expr* premise){
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << std::endl;);
         
        curr_var_pieces_counter.reset();
        generated_equalities.reset();

        for (const auto& n : non_fresh_vars)
            STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " " << mk_pp(n.m_key, m) << " " << n.m_value << std::endl;);

        expr_ref_vector asserted_constraints(m);
        bool axiomAdded = false;
        for (const auto& vareq : eq_combination) {
            if (vareq.get_value().size() == 0)
                continue;

            expr* reg = nullptr;
            if ((is_internal_regex_var(vareq.m_key, reg)) || is_non_fresh(vareq.m_key) || u.str.is_string(vareq.m_key)){
                STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << mk_pp(vareq.m_key, m) << std::endl;);
                expr *result = convert_const_nonfresh_equalities(vareq.m_key, vareq.get_value(), non_fresh_vars);
                assert_breakdown_combination(result, premise, asserted_constraints, axiomAdded);
                if (result == nullptr)
                    return true;

                expr* regexExpr;
                if (is_regex_var(vareq.m_key, regexExpr) && !is_internal_var(vareq.m_key)){
                    STRACE("str", tout << __LINE__ <<  "  " << mk_pp(vareq.m_key, m) << " = " << mk_pp(regexExpr, m) << " " << getStdRegexStr(regexExpr) << std::endl;);
                    convert_regex_equalities(regexExpr, vareq.m_key, non_fresh_vars, asserted_constraints, axiomAdded);
                }
            }
            else if (is_long_equality(vareq.get_value())) {
                /* add an eq = flat . flat . flat, then other equalities will compare with it */
                expr *result = convert_long_equalities(vareq.m_key, vareq.get_value(), non_fresh_vars);
                assert_breakdown_combination(result, premise, asserted_constraints, axiomAdded);
                if (result == nullptr)
                    return true;
            }
            else {
                STRACE("str", tout << __LINE__ <<  " work as usual " << std::endl;);
                expr* result = convert_other_equalities(vareq.get_value(), non_fresh_vars);
                assert_breakdown_combination(result, premise, asserted_constraints, axiomAdded);
                if (result == nullptr)
                    return true;
            }

        }

        if (asserted_constraints.size() > 0) {
            expr_ref tmp(createAndOP(asserted_constraints), m);
            uState.add_asserting_constraints(tmp);
        }
        return axiomAdded;
    }

    bool theory_trau::is_long_equality(ptr_vector<expr> const& eqs){
        return findMaxP(eqs) > 6;
    }

    expr* theory_trau::convert_other_equalities(ptr_vector<expr> const& eqs, obj_map<expr, int> const& non_fresh_vars){
        
        STRACE("str", tout << __LINE__ <<  " work as usual " << std::endl;);
        expr_ref_vector ands(m);
        /* work as usual */
        for (unsigned i = 0; i < eqs.size(); ++i)
            for (unsigned j = i + 1; j < eqs.size(); ++j) {
                /* optimize: find longest common prefix and posfix */
                ptr_vector<expr> lhs;
                ptr_vector<expr> rhs;
                optimize_equality(eqs[i], eqs[j], lhs, rhs);

                if (lhs.size() == 0 || rhs.size() == 0){
                    continue;
                }

                /* [i] = [j] */
                pair_expr_vector lhs_elements = create_equality(lhs);
                pair_expr_vector rhs_elements = create_equality(rhs);
                expr* result = equality_to_arith(
                        lhs_elements,
                        rhs_elements,
                        non_fresh_vars
                );
                if (result == nullptr)
                    return nullptr;
                else
                    ands.push_back(result);
            }
        return createAndOP(ands);
    }

    expr* theory_trau::convert_long_equalities(expr* var, ptr_vector<expr> const& eqs, obj_map<expr, int> & non_fresh_vars){
        /* add an eq = flat . flat . flat, then other equalities will compare with it */
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << mk_pp(var, m) << std::endl;);
        expr_ref_vector ands(m);
        pair_expr_vector lhs_elements = create_equality(var, false);
        uState.non_fresh_vars.insert(var, connectingSize);
        non_fresh_vars.insert(var, connectingSize);
        mk_and_setup_arr(var, non_fresh_vars);

        /* compare with others */
        for (const auto& element: eqs) {
            pair_expr_vector rhs_elements = create_equality(element);
            expr* result = equality_to_arith(
                    lhs_elements,
                    rhs_elements,
                    non_fresh_vars
            );

            if (result == nullptr)
                return nullptr;
            else
                ands.push_back(result);
        }
        return createAndOP(ands);
    }

    expr* theory_trau::convert_const_nonfresh_equalities(expr* var, ptr_vector<expr> const& eqs, obj_map<expr, int> const& non_fresh_vars){
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << mk_pp(var, m) << std::endl;);
        expr_ref_vector ands(m);
        expr* root_tmp = find_equivalent_variable(var);
        for (const auto& element: eqs) {
            if (element == var && !u.str.is_concat(element)){
                continue;
            }
            ptr_vector<expr> lhs;
            ptr_vector<expr> rhs;
            optimize_equality(root_tmp, element, lhs, rhs);
            pair_expr_vector lhs_elements = create_equality(var, false);
            pair_expr_vector rhs_elements = create_equality(element);
            expr* containKey = nullptr;
            rational lenVal;
            zstring rootStr;
            if (u.str.is_string(root_tmp, rootStr) && is_contain_equality(element, containKey) && get_len_value(containKey, lenVal)){
                expr* tmp = const_contains_key(rootStr, getMostLeftNodeInConcat(element), containKey, lenVal);
                if (tmp == nullptr)
                    return nullptr;
                else
                    ands.push_back(tmp);
            }
            else {
                expr* tmp = equality_to_arith(lhs_elements, rhs_elements, non_fresh_vars);
                if (tmp == nullptr)
                    return nullptr;
                else
                    ands.push_back(tmp);
            }
        }
        return createAndOP(ands);
    }

    void theory_trau::convert_regex_equalities(expr* regexExpr, expr* var, obj_map<expr, int> const& non_fresh_vars, expr_ref_vector &assertedConstraints, bool &axiomAdded){

        expr_ref_vector regex_elements = combine_const_str(parse_regex_components(remove_star_in_star(regexExpr)));
        expr_ref_vector ors(m);
        for (const auto& v : regex_elements){
            STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << mk_pp(v, m) << std::endl;);
            ptr_vector <expr> elements;
            get_nodes_in_reg_concat(v, elements);
            ptr_vector<expr> lhs;
            ptr_vector<expr> rhs;
            optimize_equality(var, elements, lhs, rhs);
            pair_expr_vector lhs_elements = create_equality(lhs);
            pair_expr_vector rhs_elements = create_equality(rhs);

            expr* result = equality_to_arith(lhs_elements,
                                             rhs_elements,
                                             non_fresh_vars);

            if (result != nullptr) {
                expr_ref tmp(result, m);
                ors.push_back(tmp);
            }
        }

        if (ors.size() > 0) {
            expr_ref tmp(createOrOP(ors), m);
            assertedConstraints.push_back(tmp);
            assert_axiom(tmp.get());
            axiomAdded = true;
        }
    }

    expr* theory_trau::const_contains_key(zstring c, expr* pre_contain, expr* key, rational len){
        zstring constKey;
        int lenInt = len.get_int32();

        if (u.str.is_string(key, constKey)){
            if (c.contains(constKey)) {
                int index = c.indexof(constKey, 0);
                return m_autil.mk_eq(mk_strlen(pre_contain), mk_int(index));
            }
        }
        else if (lenInt > 0 && lenInt <= (int)c.length()){
            expr_ref_vector ors(m);
            expr* arr = get_var_flat_array(key);

            for (unsigned i = 0; i <= c.length() - len.get_int32(); ++i) {
                expr_ref_vector ands(m);
                // | pre_contain | = i
                ands.push_back(createEqualOP(mk_strlen(pre_contain), mk_int(i)));

                // arr = ?
                for (int j = 0; j < lenInt; ++j) {
                    ands.push_back(createEqualOP(createSelectOP(arr, mk_int(j)), mk_int(c[i + j])));
                }
                ors.push_back(createAndOP(ands));
            }
            return createOrOP(ors);
        }
        return nullptr;
    }

    void theory_trau::assert_breakdown_combination(expr* e, expr* premise, expr_ref_vector &assertedConstraints, bool &axiomAdded){
        
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

    void theory_trau::assert_breakdown_combination(expr* e, expr* premise){
        ensure_enode(e);
        assert_axiom(e, premise);
    }

    void theory_trau::negate_equalities(){
        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << std::endl;);
        
        expr_ref_vector guessed_eqs(m), guessed_diseqs(m);
        fetch_guessed_exprs_with_scopes(guessed_eqs, guessed_diseqs);

        expr_ref tmp(mk_not(m, createAndOP(guessed_eqs)), m);
        assert_axiom(tmp.get());
        implied_facts.push_back(tmp.get());
    }

    void theory_trau::negate_context(){
        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << std::endl;);
        
        expr_ref_vector guessed_eqs(m), guessed_diseqs(m);
        fetch_guessed_exprs_with_scopes(guessed_eqs, guessed_diseqs);
        guessed_eqs.append(guessed_diseqs);

        expr_ref tmp(mk_not(m, createAndOP(guessed_eqs)), m);
        assert_axiom(tmp.get());
        implied_facts.push_back(tmp.get());
    }

    void theory_trau::negate_context(expr* premise){
        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << std::endl;);
        
        expr_ref tmp(mk_not(m,premise), m);
        assert_axiom(tmp.get());
        implied_facts.push_back(tmp.get());
    }

    void theory_trau::negate_context(expr_ref_vector const& v){
        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << std::endl;);
        
        expr_ref_vector guessed_eqs(m), guessed_diseqs(m);
        fetch_guessed_exprs_with_scopes(guessed_eqs, guessed_diseqs);
        guessed_eqs.append(v);
        guessed_eqs.append(guessed_diseqs);
        expr_ref tmp(mk_not(m, createAndOP(guessed_eqs)), m);
        assert_axiom(tmp.get());
    }

    expr* theory_trau::find_equivalent_variable(expr* e){
        if (u.str.is_concat(e)) {
            // change from concat to variable if it is possible
            expr_ref_vector eqNodeSet(m);
            collect_eq_nodes(e, eqNodeSet);
            for (unsigned i = 0; i < eqNodeSet.size(); ++i)
                if (!u.str.is_concat(eqNodeSet[i].get())) {
                    return eqNodeSet[i].get();
                }
        }
        return e;
    }

    bool theory_trau::is_internal_var(expr* e){
        std::string tmp = expr2str(e);
        return tmp.find("!tmp") != std::string::npos;
    }

    bool theory_trau::is_internal_regex_var(expr* e, expr* &regex){
        expr_ref_vector eqs(m);
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

    bool theory_trau::is_internal_regex_var(expr* e){
        expr_ref_vector eqs(m);
        collect_eq_nodes(e, eqs);
        for (const auto& we: membership_memo) {
            if (eqs.contains(we.first)){
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

    bool theory_trau::is_splitable_regex(expr* e){
        if (u.re.is_concat(e) || u.re.is_union(e))
            return true;
        else if (u.re.is_plus(e) || u.re.is_star(e))
            return is_splitable_regex(to_app(e)->get_arg(0));
        else if (u.re.is_full_seq(e) || u.re.is_range(e))
            return true;
        else if (u.re.is_to_re(e))
            return false;
        return false;
    }

    /*
     * (abc)* -> abc
     */
    zstring theory_trau::parse_regex_content(zstring str){
        int pos = str.indexof("*", 0);
        if (pos == -1)
            pos = str.indexof("+", 0);

        return str.extract(1, pos - 2);
    }

    /*
     * (abc)*__XXX -> abc
     */
    zstring theory_trau::parse_regex_content(expr* e){
        expr* reg = nullptr;
        if (is_internal_regex_var(e, reg)){
            return parse_regex_content(reg);
        }

        SASSERT (u.re.is_star(e) || u.re.is_plus(e) || u.re.is_union(e));

        if (u.re.is_union(e)) {
            return "";
        }
        else {
            expr *arg0 = to_app(e)->get_arg(0);
            expr *arg00 = nullptr;
            if (u.re.is_to_re(arg0, arg00)) { 
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
    expr_ref_vector theory_trau::combine_const_str(expr_ref_vector const& v){
        expr_ref_vector result(m);
        for (const auto& e : v){
            STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << mk_pp(e, m) << std::endl;);
            ptr_vector<expr> nodes;
            get_nodes_in_reg_concat(e, nodes);
            if (nodes.size() > 0) {
                ptr_vector<expr> tmp_nodes;
                tmp_nodes.push_back(nodes[0]);
                expr* tmp00 = nullptr, *tmp01 = nullptr;
                for (unsigned i = 1; i < nodes.size(); ++i) {
                    if (u.re.is_to_re(nodes[i], tmp01) && u.re.is_to_re(tmp_nodes[tmp_nodes.size() - 1], tmp00)) {
                        // group them
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

    bool theory_trau::isRegexStr(zstring str){
        return str.contains(")*") || str.contains(")+");
    }

    bool theory_trau::isUnionStr(zstring str){
        return str.contains("|");
    }

    /*
     *
     */
    expr_ref_vector theory_trau::parse_regex_components(expr* reg){
        expr_ref_vector result(m);
        ensure_enode(reg);
        expr_ref_vector components = collect_alternative_components(reg);
        unsigned cnt = 0;
        if (components.size() > 1){
            for (const auto& c : components) {
                cnt++;
                if (cnt >= 20)
                    break;
                expr_ref_vector tmp = parse_regex_components(c);
                for (const auto& comp : tmp)
                    result.push_back(comp);
            }
        }
        else {
            expr* arg0 = nullptr;
            expr* arg1 = nullptr;
            if (u.re.is_concat(reg, arg0, arg1)) {
                expr_ref_vector tmp00(m);
                tmp00.append(parse_regex_components(arg0));
                expr_ref_vector tmp01(m);
                tmp01.append(parse_regex_components(arg1));

                for (int i = 0; i < std::min((int)tmp00.size(), 10); i ++)
                    for (int j = 0; j < std::min((int)tmp01.size(), 10); j ++) {
                        expr* tmp = u.re.mk_concat(tmp00[i].get(), tmp01[j].get());
                        ensure_enode(tmp);
                        result.push_back(tmp);
                    }

                return result;
            }
            else {
                result.push_back(reg);
            }
        }
        return result;
    }

    /*
     * (a) | (b) --> {a, b}
     */
    vector<zstring> theory_trau::collect_alternative_components(zstring str){
        if (str.length() <= 2)
            return init_zstring_vector(str);
        else if (str[0] == '(' && str[str.length() - 1] == ')' && find_correspond_right_parentheses(0, str) == (int)str.length() - 1) {
            return collect_alternative_components(str.extract(1, str.length() - 2));
        }
        else {
            vector<zstring> result;
            int counter = 0;
            unsigned startPos = 0;
            for (unsigned j = 0; j < str.length(); ++j) {
                if (str[j] == ')') {
                    counter--;
                } else if (str[j] == '(') {
                    counter++;
                } else if ((str[j] == '|' || str[j] == '~') && counter == 0) {
                    zstring tmp = str.extract(startPos, j - startPos);
                    vector<zstring> tmp_vec = collect_alternative_components(tmp);
                    result.append(tmp_vec);
                    startPos = j + 1;
                }
            }
            if (startPos != 0) {
                zstring tmp = str.extract(startPos, str.length() - startPos);
                vector<zstring> tmp_vec = collect_alternative_components(tmp);
                result.append(tmp_vec);
            }
            else {
                return init_zstring_vector(str);
            }
            return result;
        }
    }

    int theory_trau::find_correspond_right_parentheses(int leftParentheses, zstring str){
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

    expr_ref_vector theory_trau::collect_alternative_components(expr* v){
        expr_ref_vector result(m);
        if (!collect_alternative_components(v, result))
            result.reset();
        return result;
    }

    bool theory_trau::collect_alternative_components(expr* v, expr_ref_vector& ret){
        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " " << mk_pp(v, m) << std::endl;);
        expr *arg0 = nullptr, *arg1 = nullptr;
        if (u.re.is_to_re(v)){
            ret.push_back(v);
        }
        else if (u.re.is_union(v, arg0, arg1)){
            if (!collect_alternative_components(arg0, ret))
                return false;
            if (!collect_alternative_components(arg1, ret))
                return false;
        }
        else if (u.re.is_star(v) || u.re.is_plus(v)) {
            ret.push_back(v);
        }
        else if (u.re.is_concat(v, arg0, arg1)){
            expr* tmp = is_regex_plus_breakdown(v);
            if (tmp) {
                collect_alternative_components(tmp, ret);
            }
            else {
                expr_ref_vector lhs(m);
                expr_ref_vector rhs(m);
                collect_alternative_components(arg0, lhs);
                collect_alternative_components(arg1, rhs);

                for (const auto &l : lhs) {
                    for (const auto &r: rhs) {
                        expr *tmp = u.re.mk_concat(l, r);
                        ret.push_back(tmp);
                    }
                }
            }
        }
        else if (u.re.is_range(v, arg0, arg1)){
            zstring start, finish;
            u.str.is_string(arg0, start);
            u.str.is_string(arg1, finish);

            for (unsigned i = start[0]; i <= finish[0]; ++i){
                ret.push_back(mk_string(i));
            }
        }
        else {
            STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << mk_pp(v, m) << std::endl;);
            SASSERT(false);
        }
        return true;
    }

    bool theory_trau::collect_alternative_components(expr* v, vector<zstring>& ret){
        expr *arg0 = nullptr, *arg1 = nullptr;
        if (u.re.is_to_re(v, arg0)){
            zstring tmpStr;
            u.str.is_string(arg0, tmpStr);
            ret.push_back(tmpStr);
        }
        else if (u.re.is_union(v, arg0, arg1)){
            if (!collect_alternative_components(arg0, ret))
                return false;
            if (!collect_alternative_components(arg1, ret))
                return false;
        }
        else if (u.re.is_star(v, arg0) || u.re.is_plus(v, arg0)) {
            return collect_alternative_components(arg0, ret);
        }
        else if (u.re.is_concat(v, arg0, arg1)){
            expr* tmp = is_regex_plus_breakdown(v);
            if (tmp != nullptr){
                return collect_alternative_components(tmp, ret);
            }
            else
                return false;
        }
        else if (u.re.is_range(v, arg0, arg1)){
            zstring start, finish;
            u.str.is_string(arg0, start);
            u.str.is_string(arg1, finish);
            for (unsigned i = start[0]; i <= finish[0]; ++i){
                ret.push_back(zstring(i));
            }
        }
        else {
            STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << mk_pp(v, get_manager()) << std::endl;);
            SASSERT(false);
        }
        return true;
    }

    theory_trau::string_set theory_trau::collect_strs_in_membership(expr* v){
        string_set ret;
        collect_strs_in_membership(v, ret);
        return ret;
    }

    void theory_trau::collect_strs_in_membership(expr* v, string_set &ret) {
        expr *arg0 = nullptr, *arg1 = nullptr;
        if (u.re.is_to_re(v, arg0)){
            zstring tmpStr;
            u.str.is_string(arg0, tmpStr);
            ret.insert(tmpStr);
        }
        else if (u.re.is_union(v, arg0, arg1)){
            collect_strs_in_membership(arg0, ret);
            collect_strs_in_membership(arg1, ret);
        }
        else if (u.re.is_star(v, arg0) || u.re.is_plus(v, arg0)) {
            collect_strs_in_membership(arg0, ret);
        }
        else if (u.re.is_concat(v, arg0, arg1)){
            collect_strs_in_membership(arg0, ret);
            collect_strs_in_membership(arg1, ret);
        }
        else if (u.re.is_range(v, arg0, arg1)){
            zstring start, finish;
            u.str.is_string(arg0, start);
            u.str.is_string(arg1, finish);
            SASSERT(start.length() == 1);
            SASSERT(finish.length() == 1);

            for (unsigned i = start[0]; i <= finish[0]; ++i) {
                ret.insert(zstring(i));
            }
        }
        else
            NOT_IMPLEMENTED_YET();
    }

    expr* theory_trau::remove_star_in_star(expr* reg){
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << mk_pp(reg, m) << std::endl;);
        expr *arg0 = nullptr, *arg1 = nullptr;
        if (u.re.is_star(reg, arg0)){
            if (contain_star(arg0)) {
                return remove_star_in_star(arg0);
            }
            else
                return u.re.mk_star(remove_star_in_star(arg0));
        }
        else if (u.re.is_plus(reg, arg0)){
            if (contain_star(arg0))
                return remove_star_in_star(arg0);
            else {
                return u.re.mk_plus(remove_star_in_star(arg0));
            }
        }
        else if (u.re.is_concat(reg, arg0, arg1)) {
            if (u.re.is_star(arg0) && arg0 == arg1)
                return arg0;
            if (u.re.is_plus(arg0) && arg0 == arg1)
                return arg0;
            else if (u.re.is_star(arg0) && u.re.is_plus(arg1) && to_app(arg0)->get_arg(0) == to_app(arg1)->get_arg(0))
                return arg1;
            else if (u.re.is_star(arg1) && u.re.is_plus(arg0) && to_app(arg0)->get_arg(0) == to_app(arg1)->get_arg(0))
                return arg0;
            else {
                expr* tmp0 = is_regex_plus_breakdown(arg0);
                expr* tmp1 = is_regex_plus_breakdown(arg1);
                if (tmp0 != nullptr && tmp1 != nullptr && tmp0 == tmp1){
                    STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << mk_pp(reg, m) << std::endl;);
                    return arg0;
                }
                else {
                    if (tmp0 == nullptr)
                        tmp0 = arg0;
                    if (tmp1 == nullptr)
                        tmp1 = arg1;

                    expr* tmp2 = remove_star_in_star(tmp0);
                    expr* tmp3 = remove_star_in_star(tmp1);
                    expr* tmp4 = u.re.mk_concat(tmp2, tmp3);
                    m_trail.push_back(tmp4);
                    STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << mk_pp(tmp2, m) << " "<< mk_pp(tmp3, m) << std::endl;);
                    if (tmp2 == tmp3 && tmp4 != reg) {
                        return remove_star_in_star(tmp4);
                    }
                    else
                        return tmp4;
                }
            }
        }
        else if (u.re.is_union(reg, arg0, arg1)) {
            if (arg0 == arg1)
                return arg0;
            else {
                expr* tmp0 = is_regex_plus_breakdown(arg0);
                expr* tmp1 = is_regex_plus_breakdown(arg1);

                if (tmp0 != nullptr && tmp1 != nullptr && tmp0 == tmp1){
                    STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << mk_pp(reg, m) << std::endl;);
                    return arg0;
                }
                else {
                    if (tmp0 == nullptr)
                        tmp0 = arg0;
                    if (tmp1 == nullptr)
                        tmp1 = arg1;
                    expr *tmp2 = remove_star_in_star(tmp0);
                    expr *tmp3 = remove_star_in_star(tmp1);
                    expr *tmp4 = u.re.mk_union(tmp2, tmp3);
                    STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << mk_pp(tmp2, m) << " "<< mk_pp(tmp3, m) << std::endl;);
                    m_trail.push_back(tmp4);
                    if (tmp2 == tmp3) {
                        return remove_star_in_star(tmp4);
                    } else {
                        return tmp4;
                    }
                }
            }
        }
        else
            return reg;
    }

    bool theory_trau::contain_star(expr* reg){
        expr* arg0 = nullptr;
        expr* arg1 = nullptr;
        if (u.re.is_star(reg)){
            return true;
        }
        if (u.re.is_plus(reg)){
            return true;
        }
        else if (u.re.is_concat(reg, arg0, arg1)) {
            return contain_star(arg0) || contain_star(arg1);
        }
        else if (u.re.is_union(reg, arg0, arg1)) {
            return contain_star(arg0) || contain_star(arg1);
        }
        else
            return false;
    }

    /*
     *
     */
    zstring theory_trau::getStdRegexStr(expr* regex) {
        expr* arg0 = nullptr;
        expr* arg1 = nullptr;
        if (u.re.is_to_re(regex, arg0)) {
            zstring value;
            u.str.is_string(arg0, value);
            return value;
        } else if (u.re.is_concat(regex, arg0, arg1)) {
            zstring reg1Str = getStdRegexStr(arg0);
            zstring reg2Str = getStdRegexStr(arg1);
            STRACE("str", tout << __LINE__ <<  " " << zstring("(") + reg1Str + ")(" + reg2Str + ")" << std::endl;);
            return zstring("(") + reg1Str + ")(" + reg2Str + ")";
        } else if (u.re.is_union(regex, arg0, arg1)) {
            zstring reg1Str = getStdRegexStr(arg0);
            zstring reg2Str = getStdRegexStr(arg1);
            STRACE("str", tout << __LINE__ <<  " " << zstring("(") + reg1Str + ")~(" + reg2Str + ")" << std::endl;);
            return  zstring("(") + reg1Str + ")~(" + reg2Str + ")";
        } else if (u.re.is_star(regex, arg0)) {
            zstring reg1Str = getStdRegexStr(arg0);
            STRACE("str", tout << __LINE__ <<  " " << zstring("(") + reg1Str + ")*" << std::endl;);
            return zstring("(") + reg1Str + ")*";
        } else if (u.re.is_range(regex, arg0, arg1)) {
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
            unsigned_set tobeEncoded;
            setup_encoded_chars(tobeEncoded);
            zstring tmp;
            for (int i = 32; i <= 126; ++i)
                if (!tobeEncoded.contains((char)i))
                    tmp = tmp + "(" + (char)i + ")~";
            return zstring("(") + tmp.extract(0, tmp.length() - 1) + ")*";
        }
        else if (u.re.is_full_char(regex)){
            unsigned_set tobeEncoded;
            setup_encoded_chars(tobeEncoded);
            zstring tmp;
            for (int i = 32; i <= 126; ++i)
                if (!tobeEncoded.contains((char)i))
                    tmp = tmp + "(" + (char)i + ")~";
            return tmp.extract(0, tmp.length() - 1);
        } else
            SASSERT(false);
        return nullptr;
    }

    void theory_trau::setup_encoded_chars(unsigned_set &s){
        s.insert('?');
        s.insert('\\');
        s.insert('|');
        s.insert('?');
        s.insert('(');
        s.insert(')');
        s.insert('~');
        s.insert('&');
        s.insert('\'');
        s.insert('+');
        s.insert('%');
        s.insert('#');
        s.insert('*');
    }

    /*
     * convert lhs == rhs to SMT formula
     */
    expr* theory_trau::equality_to_arith(
            pair_expr_vector const& lhs_elements,
            pair_expr_vector const& rhs_elements,
            obj_map<expr, int> const& non_fresh_variables,
            int p){
        //swap if lhs > rhs
        if (lhs_elements.size() > rhs_elements.size()){
            return equality_to_arith_ordered(rhs_elements, lhs_elements, non_fresh_variables, p);
        }
        else
            return equality_to_arith_ordered(lhs_elements, rhs_elements, non_fresh_variables, p);
    }

    /*
     * convert lhs == rhs to SMT formula
     */
    expr* theory_trau::equality_to_arith_ordered(
            pair_expr_vector const& lhs_elements,
            pair_expr_vector const& rhs_elements,
            obj_map<expr, int> const& non_fresh_variables,
            int p){
        zstring rep = create_string_representation(lhs_elements, rhs_elements);

        if (!generated_equalities.contains(rep) &&
            lhs_elements.size() != 0 && rhs_elements.size() != 0){
            expr_ref_vector cases = arrange(
                    lhs_elements,
                    rhs_elements,
                    non_fresh_variables,
                    p);
            generated_equalities.insert(rep);
            if (cases.size() > 0) {
                expr_ref tmp(createOrOP(cases), m);
                return tmp.get();
            }
            else {
                return nullptr;
            }
        }
        else
            return m.mk_true();
    }

    zstring theory_trau::create_string_representation(pair_expr_vector const& lhs_elements, pair_expr_vector const& rhs_elements){
        std::string ret = "";
        for (unsigned i = 0; i < lhs_elements.size(); ++i)
            ret = ret + "-" + expr2str(lhs_elements[i].first);
        for (unsigned i = 0; i < rhs_elements.size(); ++i)
            ret = ret + "+" + expr2str(rhs_elements[i].first);
        return zstring(ret.c_str());
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
    expr_ref_vector theory_trau::arrange(
            pair_expr_vector const& lhs_elements,
            pair_expr_vector const& rhs_elements,
            obj_map<expr, int> const& non_fresh_variables,
            int p){
        /* first base case */
        

        /* because arrangements are reusable, we use "general" functions */
        setup_0_0_general();
        /* second base case : first row and first column */
        setup_0_n_general(lhs_elements.size(), rhs_elements.size());
        setup_n_0_general(lhs_elements.size(), rhs_elements.size());
        /* general cases */
        setup_n_n_general(lhs_elements.size(), rhs_elements.size());

        /* because of "general" functions, we need to refine arrangements */
        vector<Arrangment> possibleCases;
        get_arrangements(lhs_elements, rhs_elements, non_fresh_variables, possibleCases);

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

            arrangements[std::make_pair(lhs_elements.size() - 1, rhs_elements.size() - 1)][i].print("Checking case");
            expr* tmp = to_arith(p, possibleCases[i].left_arr, possibleCases[i].right_arr, lhs_elements, rhs_elements, non_fresh_variables);

            if (tmp != nullptr) {
                cases.push_back(tmp);
                arrangements[std::make_pair(lhs_elements.size() - 1, rhs_elements.size() - 1)][i].print("Correct case");
            }
            else {
            }
        }
        return cases;

    }

    void theory_trau::get_arrangements(pair_expr_vector const& lhs_elements,
                                        pair_expr_vector const& rhs_elements,
                                        obj_map<expr, int> const& non_fresh_variables,
                                        vector<Arrangment> &possibleCases) {
        std::string firstVar = expr2str(lhs_elements[0].first);
        if ((firstVar.find(FLATPREFIX) != std::string::npos && lhs_elements.size() == p_bound.get_int64()) ||
            (lhs_elements.size() == 2 &&
             ((non_fresh_variables.contains(lhs_elements[0].first) && lhs_elements[1].second % p_bound.get_int64() == 1) ||
              (lhs_elements[0].second % p_bound.get_int64() == -1 && lhs_elements[1].first == lhs_elements[0].first)))) {
            /* create manually */
            /*9999999 10000000 vs 1 1 1 1 1 */
            possibleCases.push_back(create_arrangments_manually(lhs_elements, rhs_elements));
        } else {
            update_possible_arrangements(lhs_elements, rhs_elements,
                                         arrangements[std::make_pair(lhs_elements.size() - 1, rhs_elements.size() - 1)],
                                         possibleCases);
        }
    }

    void theory_trau::update_possible_arrangements(
            pair_expr_vector const& lhs_elements,
            pair_expr_vector const& rhs_elements,
            vector<Arrangment> const& tmp,
            vector<Arrangment> &possibleCases) {
        for (const auto& a : tmp)
            if (a.is_possible_arrangement(lhs_elements, rhs_elements))
                possibleCases.push_back(a);
    }

    /*
     *
     */
    theory_trau::Arrangment theory_trau::create_arrangments_manually(
            pair_expr_vector const& lhs_elements,
            pair_expr_vector const& rhs_elements){

        /* create manually */
        /*10000000 10000000 vs 0 0 1 1 1 */
        int_vector left_arr;
        int_vector right_arr;
        unsigned mid = rhs_elements.size() / 2;
        if (false) {
            left_arr.push_back(SUMFLAT);
            left_arr.push_back(SUMFLAT);
            for (unsigned i = 0; i <= mid; ++i)
                right_arr.push_back(0);
            for (unsigned i = mid + 1; i < rhs_elements.size(); ++i)
                right_arr.push_back(1);
        }
        else {
            left_arr.push_back(EMPTYFLAT);
            left_arr.push_back(SUMFLAT);
            for (unsigned i = 0; i < rhs_elements.size(); ++i)
                right_arr.push_back(1);
        }
        return Arrangment(left_arr, right_arr);
    }

    /*
     * a_1 + a_2 + b_1 + b_2 = c_1 + c_2 + d_1 + d_2 ---> SMT
     */
    expr* theory_trau::to_arith(int p,
                                int_vector const& left_arr,
                                int_vector const& right_arr,
                                pair_expr_vector const& lhs_elements,
                                pair_expr_vector const& rhs_elements,
                                obj_map<expr, int> const& non_fresh_variables){
        
        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__  << std::endl;);
        expr_ref_vector result(m);

        bool check_left[10000];
        bool check_right[10000];
        memset(check_left, 0, sizeof check_left);
        memset(check_right, 0, sizeof check_right);

        expr* leftConstraint = to_arith_left(check_left, check_right, p, left_arr, right_arr, lhs_elements,rhs_elements, non_fresh_variables);
        if (leftConstraint == nullptr)
            return nullptr;
        else
            result.push_back(leftConstraint);

        expr* rightConstraint = to_arith_right(check_left, check_right, p, left_arr, right_arr, lhs_elements,rhs_elements, non_fresh_variables);
        if (rightConstraint == nullptr)
            return nullptr;
        else
            result.push_back(rightConstraint);

        expr* emptyflats = to_arith_emptyflats(check_left, check_right, left_arr, right_arr, lhs_elements, rhs_elements);
        if (emptyflats == nullptr)
            return nullptr;
        else
            result.push_back(emptyflats);

        expr* others = to_arith_others(check_left, check_right, p, left_arr, right_arr, lhs_elements,rhs_elements, non_fresh_variables);
        if (others == nullptr)
            return nullptr;
        else
            result.push_back(others);

        for (unsigned i = 0 ; i < rhs_elements.size(); ++i)
            if (check_right[i] == false) {
                STRACE("str", tout << __LINE__ <<  " error rhs@i: " << i << std::endl;);
                SASSERT (false);
            }
        for (unsigned i = 0 ; i < lhs_elements.size(); ++i)
            if (check_left[i] == false) {
                STRACE("str", tout << __LINE__ <<  " error lhs@i: " << i << std::endl;);
                SASSERT (false);
            }
        STRACE("str", tout << __LINE__ <<  " current time used: " << ":  " << ((float)(clock() - startClock))/CLOCKS_PER_SEC << std::endl;);
        return createAndOP(result);
    }

    expr* theory_trau::to_arith_others(bool (&check_left)[10000], bool (&check_right)[10000], int p,
                                           int_vector const& left_arr,
                                           int_vector const& right_arr,
                                           pair_expr_vector const& lhs_elements,
                                           pair_expr_vector const& rhs_elements,
                                            obj_map<expr, int> const& non_fresh_variables){
        
        expr_ref_vector result(m);
        for (unsigned i = 0 ; i < lhs_elements.size(); ++i)
            if (check_left[i] == false) {
                check_left[i] = true;
                check_right[left_arr[i]] = true;

                unsigned j = 0;
                for (j = 0; j < right_arr.size(); ++j)
                    if (right_arr[j] == (int)i) {
                        check_right[j] = true;
                        break;
                    }

                /* select optimization mode */
                int optimizing = optimized_lhs(i, -1, j, left_arr, right_arr, vectorExpr2vectorStr(lhs_elements),
                                               vectorExpr2vectorStr(rhs_elements));
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
                        check_left[i + 1] = true;
                        check_right[j + 1] = true;
                        break;
                    case RIGHT_SUM:
                    SASSERT (false);
                        break;
                    default:
                    SASSERT (false);
                        break;
                }
                expr* tmp = gen_constraint01(
                        lhs_elements[i],
                        (expr_int) rhs_elements[left_arr[i]],
                        p,
                        non_fresh_variables,
                        optimizing != NONE);
                if (tmp == nullptr) { /* cannot happen due to const */
                    return nullptr;
                }
                result.push_back(tmp);
            }
        return createAndOP(result);
    }

    expr* theory_trau::to_arith_emptyflats(bool (&check_left)[10000], bool (&check_right)[10000],
                                           int_vector const& left_arr,
                                           int_vector const& right_arr,
                                           pair_expr_vector const& lhs_elements,
                                           pair_expr_vector const& rhs_elements){
        
        for (unsigned i = 0; i < left_arr.size(); ++i)
            if (!check_left[i]) {
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
                    check_left[i] = true;
                }
            }

        for (unsigned i = 0; i < right_arr.size(); ++i)
            if (!check_right[i]){
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
                    check_right[i] = true;
                }
            }

        return m.mk_true();
    }

    expr* theory_trau::to_arith_right(bool (&check_left)[10000], bool (&check_right)[10000], int p,
                                     int_vector const& left_arr,
                                     int_vector const& right_arr,
                                     pair_expr_vector const& lhs_elements,
                                     pair_expr_vector const& rhs_elements,
                                      obj_map<expr, int> const& non_fresh_variables){
        
        expr_ref_vector result(m);
        for (unsigned i = 0; i < right_arr.size(); ++i)
            if (!check_right[i]){
                if (right_arr[i] == SUMFLAT) { /* a = bx + cy */
                    check_right[i] = true;

                    pair_expr_vector elements;
                    unsigned j = 0;
                    int startPos = -1;
                    for (j = 0; j < left_arr.size(); ++j)
                        if (left_arr[j] == (int)i) {
                            if (startPos == -1)
                                startPos = (int)j;
                            elements.push_back(lhs_elements[j]);
                            check_left[j] = true;
                        }
                        else if (startPos >= 0)
                            break;
                    j--;
                    /* select optimization mode */
                    int optimizing = NONE;
                    if (!flat_enabled)
                        optimized_rhs(j, startPos, i, left_arr, right_arr, vectorExpr2vectorStr(lhs_elements),
                                      vectorExpr2vectorStr(rhs_elements));
                    STRACE("str", tout << __LINE__ <<  "  optimizing mode: " << optimizing << std::endl;);
                    switch (optimizing) {
                        case NONE:
                            break;
                        case LEFT_EMPTY:
//                            if (right_arr.size() != 2)
//                                return nullptr;
                            check_right[i - 1] = true;
                            break;
                        case LEFT_EQUAL:
                            check_right[i - 1] = true;
                            check_left[startPos - 1] = true;
                            insert_top(lhs_elements[startPos - 1], elements);
                            break;
                        case LEFT_SUM:
                        SASSERT (false);
                            break;
                        case RIGHT_EMPTY:
                            check_right[i + 1] = true;
                            break;
                        case RIGHT_EQUAL:
                            return nullptr; // duplicate case
                            check_right[i + 1] = true;
                            check_left[j + 1] = true;
                            elements.push_back(lhs_elements[j + 1]);
                            break;
                        case RIGHT_SUM:
                            return nullptr; // duplicate case
                            check_right[i + 1] = true;
                            for (unsigned k = j + 1; k < left_arr.size(); ++k)
                                if (left_arr[k] == (int)i + 1) {
                                    elements.push_back(lhs_elements[k]);
                                    check_left[k] = true;
                                }
                            break;
                        default:
                        SASSERT (false);
                            break;
                    }
                    expr_ref tmp(gen_constraint02(
                            rhs_elements[i],
                            elements,
                            p,
                            non_fresh_variables, optimizing != NONE), m);
                    if (tmp == nullptr) { /* cannot happen due to const */
                        STRACE("str", tout << __LINE__ <<  " 02 because of rhs@i: " << i << std::endl;);
                        return nullptr;
                    }
                    STRACE("str", tout << __LINE__ <<  " done 02 " << i << std::endl;);
                    result.push_back(tmp);
                }
            }
        return createAndOP(result);
    }

    expr* theory_trau::to_arith_left(bool (&check_left)[10000], bool (&check_right)[10000], int p,
                                     int_vector const& left_arr,
                                     int_vector const& right_arr,
                                     pair_expr_vector const& lhs_elements,
                                     pair_expr_vector const& rhs_elements,
                                     obj_map<expr, int> const& non_fresh_variables){
        
        expr_ref_vector result(m);
        for (unsigned i = 0; i < left_arr.size(); ++i)
            if (!check_left[i]) {
                if (left_arr[i] == SUMFLAT) { /* a = bx + cy */
                    check_left[i] = true;

                    pair_expr_vector elements;
                    unsigned j = 0;
                    int startPos = -1;
                    for (j = 0; j < right_arr.size(); ++j)
                        if (right_arr[j] == (int)i) {
                            if (startPos == -1)
                                startPos = (int)j;
                            elements.push_back(rhs_elements[j]);
                            check_right[j] = true;
                        }
                        else if (startPos >= 0)
                            break;
                    j--;
                    /* select optimization mode */
                    int optimizing = NONE;
                    if (!flat_enabled)
                        optimizing = optimized_lhs(i, startPos, j, left_arr, right_arr,
                                                   vectorExpr2vectorStr(lhs_elements),
                                                   vectorExpr2vectorStr(rhs_elements));
                    STRACE("str", tout << __LINE__ <<  "  optimizing mode: " << optimizing << std::endl;);

                    switch (optimizing) {
                        case NONE:
                            break;
                        case LEFT_EMPTY:
//                            if (left_arr.size() != 2)
//                                return nullptr;

                            check_left[i - 1] = true;
                            break;
                        case LEFT_EQUAL:
                            check_left[i - 1] = true;
                            check_right[startPos - 1] = true;
                            insert_top(rhs_elements[startPos - 1], elements);
                            break;
                        case LEFT_SUM:
                        SASSERT (false);
                            break;
                        case RIGHT_EMPTY:
                            check_left[i + 1] = true;
                            break;
                        case RIGHT_EQUAL:
                            return nullptr; // duplicate case
                            check_left[i + 1] = true;
                            check_right[j + 1] = true;
                            elements.push_back(rhs_elements[j + 1]);
                            STRACE("str", tout << __LINE__ <<  "  RIGHT_EQUAL: elements size: " << elements.size() << std::endl;);
                            break;
                        case RIGHT_SUM:
                            return nullptr; // duplicate case
                            check_left[i + 1] = true;
                            for (unsigned k = j + 1; k < right_arr.size(); ++k)
                                if (right_arr[k] == (int)i + 1) {
                                    elements.push_back(rhs_elements[k]);
                                    check_right[k] = true;
                                }
                                else
                                    break;
                            break;
                        default:
                        SASSERT (false);
                            break;
                    }

                    expr_ref tmp(gen_constraint02(
                            lhs_elements[i],
                            elements,
                            p,
                            non_fresh_variables,
                            optimizing != NONE), m);

                    if (tmp == nullptr) { /* cannot happen due to const */
                        STRACE("str", tout << __LINE__ <<  " 02 because of lhs@i: " << i << std::endl;);
                        return nullptr;
                    }
                    else
                        STRACE("str", tout << __LINE__ <<  " done 02 " << i << std::endl;);
                    result.push_back(tmp);

                }
            }
        return createAndOP(result);
    }

    void theory_trau::insert_top(expr_int const& e, pair_expr_vector &v){
        pair_expr_vector tmp = init_expr_vector(e);
        tmp.append(v);
        v.reset();
        v.append(tmp);
    }
    /*
	 * Flat = Flat
	 * size = size && it = it  ||
	 * size = size && it = 1
	 */
    expr* theory_trau::gen_constraint01(
            expr_int a, expr_int b,
            int pMax,
            obj_map<expr, int> const& non_fresh_variables,
            bool optimizing){
        
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(a.first, m) << " " << mk_pp(b.first, m)<< std::endl;);
        bool isConstA = a.second < 0;
        bool isConstB = b.second < 0;
        expr_ref_vector result(m);

        /*
         * str-int var
         */
        expr* extra_assert = nullptr;
        if (!const_vs_str_int(a.first, init_expr_vector(b), extra_assert)){
            result.push_back(extra_assert);
        }

        expr* reg = nullptr;
        if (is_internal_regex_var(a.first, reg)) {
            if (!const_vs_regex(reg, init_expr_vector(b)))
                return nullptr;
            else {
            }

        }
        else if (is_internal_regex_var(b.first, reg)) {
            if (!const_vs_regex(reg, init_expr_vector(a)))
                return nullptr;
        }
        expr* nameA = nullptr;
        expr* nameB = nullptr;
        if (optimizing){
            nameA = get_var_size(a);
            nameB = get_var_size(b);
        }
        else {
            nameA = get_var_flat_size(a);
            nameB = get_var_flat_size(b);
        }

        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(a.first, m) << " " << mk_pp(b.first, m)<< std::endl;);
        /* do not need AND */
        result.push_back(createEqualOP(nameA, nameB));

        if (!isConstA && !isConstB) {
            /* size = size && it = it */
            gen_constraint01_var_var(a, b, pMax, non_fresh_variables, optimizing, nameA, result);
        }
        else if (isConstA && isConstB) {
            gen_constraint01_const_const(a, b, optimizing, nameA, result);
        }

        else if (isConstA) {
            gen_constraint01_const_var(a, b, non_fresh_variables, optimizing, result);
        }

        else { /* isConstB */
            gen_constraint01_const_var(b, a, non_fresh_variables, optimizing, result);
        }

        return createAndOP(result);
    }

    theory_trau::pair_expr_vector theory_trau::init_expr_vector(expr_int p){
        pair_expr_vector ret;
        ret.insert(p);
        return ret;
    }

    vector<zstring> theory_trau::init_zstring_vector(zstring p){
        vector<zstring> ret;
        ret.push_back(p);
        return ret;
    }

    void theory_trau::gen_constraint01_const_var(
            expr_int a, expr_int b,
            obj_map<expr, int> const& non_fresh_variables,
            bool optimizing,
            expr_ref_vector &result){
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(a.first, m) << " " << mk_pp(b.first, m)<< std::endl;);
        if (non_fresh_variables.contains(b.first)){
            pair_expr_vector elements;
            if (optimizing) {
                elements.push_back(std::make_pair(a.first, -1));
                elements.push_back(std::make_pair(a.first, -2));
            }
            else
                elements.push_back(a);
            result.push_back(unroll_non_fresh_variable(b, elements, non_fresh_variables, optimizing));
        }
    }

    void theory_trau::gen_constraint01_const_const(
            expr_int a, expr_int b,
            bool optimizing,
            expr *nameA,
            expr_ref_vector &result){
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(a.first, m) << " " << mk_pp(b.first, m)<< std::endl;);
        if ((p_bound.get_int64() == 1 || optimizing) && a.first != b.first) /* const = const */ {
            result.push_back(m.mk_false());
            return;
        }

        expr* reg_a = nullptr;
        if (a.second <= REGEX_CODE)
            is_internal_regex_var(a.first, reg_a);

        expr* reg_b = nullptr;
        if (b.second <= REGEX_CODE)
            is_internal_regex_var(b.first, reg_b);
        expr* tmp = nullptr;
        if (a.second <= REGEX_CODE && b.second <= REGEX_CODE && reg_a != reg_b) {
            tmp = gen_constraint01_regex_regex(a, b, nameA);
        }
        if (a.second <= REGEX_CODE && b.second <= REGEX_CODE && reg_a == reg_b) {
            tmp = m.mk_true();
        }
        else if (a.second <= REGEX_CODE && b.second % p_bound.get_int64() == -1){
            tmp = gen_constraint01_regex_head(a, b, nameA);
        }
        else if (a.second <= REGEX_CODE && b.second % p_bound.get_int64() == 0){
            tmp = gen_constraint01_regex_tail(a, b, nameA);
        }
        else if (b.second <= REGEX_CODE && a.second % p_bound.get_int64() == -1){
            tmp = gen_constraint01_regex_head(b, a, nameA);
        }
        else if (b.second <= REGEX_CODE && a.second % p_bound.get_int64() == 0){
            tmp = gen_constraint01_regex_tail(b, a, nameA);
        }
        else if (!optimizing) {
            tmp = gen_constraint01_const_const(a, b, nameA);
        }
        if (tmp == nullptr || tmp == m.mk_false())
            result.push_back(m.mk_false());
        else
            result.push_back(tmp);

    }

    expr* theory_trau::gen_constraint01_regex_head(
            expr_int a, expr_int b,
            expr *nameA){
        
        expr_ref_vector ors(m);
        zstring valB;
        u.str.is_string(b.first, valB);
        expr* regex = nullptr;
        is_internal_regex_var(a.first, regex);
        unsigned length = 0;
        if (u.re.is_plus(regex))
            length = 1;
        while (length <= valB.length()) {
            zstring regexValue = valB.extract(0, length);
            if (match_regex(regex, regexValue)) {
                expr_ref_vector ands(m);
                ands.push_back(createEqualOP(nameA, m_autil.mk_int(length)));
                for (int i = 0; i < (int)length - 1; ++i) {
                    // TODO arr vs arr
                }
                ors.push_back(createEqualOP(nameA, m_autil.mk_int(length)));
            }
            length++;
            STRACE("str", tout << __LINE__ <<  "  accept: " << regexValue << std::endl;);
        }
        return createOrOP(ors);
    }

    expr* theory_trau::gen_constraint01_regex_tail(
            expr_int a, expr_int b,
            expr *nameA){
        expr_ref_vector ors(m);
        zstring valB;
        u.str.is_string(b.first, valB);
        expr* regex = nullptr;
        is_internal_regex_var(a.first, regex);

        unsigned length = 0;
        if (u.re.is_plus(regex))
            length = 1;
        while (length <= valB.length()) {
            zstring regexValue = valB.extract(valB.length() - length, length);
            if (match_regex(regex, regexValue)) {
                // TODO arr vs arr
                ors.push_back(createEqualOP(nameA, m_autil.mk_int(length)));
            }
            length++;
            STRACE("str", tout << __LINE__ <<  "  accept: " << regexValue << std::endl;);
        }
        return createOrOP(ors);
    }

    expr* theory_trau::gen_constraint01_regex_regex(
            expr_int a, expr_int b,
            expr *nameA){
        NOT_IMPLEMENTED_YET();
        expr_ref_vector ors(m);
        expr* regexA = nullptr;
        is_internal_regex_var(a.first, regexA);
        unsigned length = 0;
        if (u.re.is_plus(regexA))
            length = 1;

        expr* regexB = nullptr;
        is_internal_regex_var(b.first, regexB);
        if (u.re.is_plus(regexB))
            length = 1;

        if (match_regex(regexA, regexB)) {
            vector<zstring> aComp;
            collect_alternative_components(regexA, aComp);
            vector<zstring> bComp;
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
                ors.push_back(createEqualOP(m_autil.mk_int(0), createModOP(nameA,
                                                                                     m_autil.mk_int(
                                                                                             lcdLength))));
            }
        }
        else {
            ors.push_back(createEqualOP(nameA, m_autil.mk_int(0)));
        }

        return createOrOP(ors);
    }

    expr* theory_trau::gen_constraint01_const_const(
            expr_int a, expr_int b,
            expr *nameA){ 
        zstring valA;
        zstring valB;
        u.str.is_string(a.first, valA);
        u.str.is_string(b.first, valB);
        expr_ref_vector cases(m);

        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(a.first, m) << std::endl;);
        if ((a.second % p_bound.get_int64() == -1 || valA.length() == 1) && (b.second % p_bound.get_int64()  == -1 || valB.length() == 1)) /* head vs head */ {
            expr* realHaystack = nullptr;
            if (not_contain(a.first, b.first, realHaystack) || not_contain(b.first, a.first, realHaystack))
                return nullptr;


            STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(a.first, m) << std::endl;);
            for (int i = std::min(valA.length(), valB.length()); i >= 0; --i) {
                if (valA.extract(0, i) == valB.extract(0, i)) {
                    /* size can be from 0..i */
                    cases.push_back(createLessEqOP(nameA, m_autil.mk_int(i)));
                }
            }
        }
        else if ((a.second % p_bound.get_int64() == -1 || valA.length() == 1) && b.second % p_bound.get_int64() == 0) /* head vs tail */ {
            STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(a.first, m) << std::endl;);
            for (int i = std::min(valA.length(), valB.length()); i >= 0; --i) {
                if (valA.extract(0, i) == valB.extract(valB.length() - i, i)) {
                    /* size can be i */
                    cases.push_back(createEqualOP(nameA, m_autil.mk_int(i)));
                }
            }
        }
        else if (a.second % p_bound.get_int64() == 0 && (b.second % p_bound.get_int64()  == -1 || valB.length() == 1)) /* tail vs head */ {
            STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(a.first, m) << std::endl;);
            for (int i = std::min(valA.length(), valB.length()); i >= 0; --i) {
                if (valB.extract(0, i) == valA.extract(valA.length() - i, i)) {
                    /* size can be i */
                    cases.push_back(createEqualOP(nameA, m_autil.mk_int(i)));
                }
            }
        }
        else if (a.second % p_bound.get_int64() == 0 && b.second % p_bound.get_int64() == 0) /* tail vs tail */ {
            STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(a.first, m) << std::endl;);
            for (int i = std::min(valA.length(), valB.length()); i >= 0; --i) {
                if (valA.extract(valA.length() - i, i) == valB.extract(valB.length() - i, i)) {
                    /* size can be i */
                    cases.push_back(createLessEqOP(nameA, m_autil.mk_int(i)));
                }
            }
        }
        return createOrOP(cases);
    }

    void theory_trau::gen_constraint01_var_var(
            expr_int a, expr_int b,
            int pMax,
            obj_map<expr, int> const& non_fresh_variables,
            bool optimizing,
            expr *nameA,
            expr_ref_vector &result){
        

        if (non_fresh_variables.contains(b.first) && non_fresh_variables.contains(a.first)){

            if (!optimizing) {
                STRACE("str", tout << __LINE__ <<  " generateConstraint01: non_fresh_Var " << mk_pp(a.first, m) << " == non_fresh_Var " << mk_pp(b.first, m) << std::endl;);
                if (!flat_enabled)
                    result.push_back(unroll_non_fresh_variable(b, init_expr_vector(a), non_fresh_variables, optimizing, pMax));
                else {
                    if ((string_int_vars.find(a.first) != string_int_vars.end() && a.second % p_bound.get_int64() == 1) ||
                        (string_int_vars.find(b.first) != string_int_vars.end() && b.second % p_bound.get_int64() == 1))
                        result.push_back(gen_constraint_flat_flat(a, init_expr_vector(b), 0, pMax, str_int_bound));
                    else
                        result.push_back(gen_constraint_flat_flat(a, init_expr_vector(b), 0, pMax, p_bound));
                }
            }
            else {
                STRACE("str", tout << __LINE__ <<  " generateConstraint01: non_fresh_Var " << mk_pp(a.first, m) << " == non_fresh_Var " << mk_pp(b.first, m) << std::endl;);
                if (!flat_enabled) {
                    expr *arrA = get_var_flat_array(a);
                    expr *arrB = get_var_flat_array(b);
                    for (int i = 0; i < std::max(non_fresh_variables[b.first], non_fresh_variables[a.first]); ++i) {
                        expr_ref_vector ors(m);
                        ors.push_back(createEqualOP(createSelectOP(arrA, m_autil.mk_int(i)),
                                                    createSelectOP(arrB, m_autil.mk_int(i))));
                        ors.push_back(createLessEqOP(nameA, m_autil.mk_int(i)));
                        result.push_back(createOrOP(ors));
                    }
                }
                else {
                    result.push_back(gen_constraint_var_var(a, b, pMax, p_bound));
                }
            }
        }
    }

    expr* theory_trau::gen_constraint_var_var(
            expr_int a,
            expr_int b,
            int pMax,
            rational bound){
        
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(a.first, m) << " = " << mk_pp(b.first, m) << std::endl;);
        expr_ref_vector ands(m);
        a.second = 0;
        b.second = 0;
        for (int i = 1; i <= p_bound.get_int64(); i = i + 1) {
            if (i == 2 && (string_int_vars.find(a.first) != string_int_vars.end() || string_int_vars.find(b.first) != string_int_vars.end()))
                ands.push_back(gen_constraint_flat_flat(a, init_expr_vector(b), 0, pMax, str_int_bound));
            else
                ands.push_back(gen_constraint_flat_flat(a, init_expr_vector(b), 0, pMax, bound));
            a.second = a.second + 1;
            b.second = b.second + 1;
        }
        return createAndOP(ands);
    }

    expr* theory_trau::gen_constraint_flat_var(
            expr_int a,
            pair_expr_vector const& elements,
            int pos,
            int pMax,
            rational bound){
        
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(a.first, m) << " = " << mk_pp(elements[pos].first, m) << std::endl;);
        expr_ref_vector ands(m);
        for (int i = 1; i <= p_bound.get_int64(); i = i + 1) {
            if (i == 2 && (string_int_vars.find(a.first) != string_int_vars.end() || string_int_vars.find(elements[pos].first) != string_int_vars.end()))
                ands.push_back(gen_constraint_flat_flat(a, elements, pos, pMax, str_int_bound));
            else
                ands.push_back(gen_constraint_flat_flat(a, elements, pos, pMax, bound));
            pos = pos + 1;
        }
        return createAndOP(ands);
    }

    expr* theory_trau::gen_constraint_flat_flat(
            expr_int a,
            pair_expr_vector const& elements,
            int pos,
            int pMax,
            rational bound,
            bool skip_init){
        
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(a.first, m) << " = " << mk_pp(elements[pos].first, m) << std::endl;);
        rational zero(0);
        rational one(1);
        bool unrollMode = pMax == PMAX;
        expr_int b = elements[pos];

        expr* lenA = get_var_flat_size(a);
        expr* lenB = get_var_flat_size(b);
        expr* arrA = get_var_flat_array(a);
        expr* arrB = get_var_flat_array(b);
        expr* iterA = get_flat_iter(a);
        expr* iterB = get_flat_iter(b);
        expr* pre_lhs = leng_prefix_lhs(a, elements, pos, false, unrollMode);
        expr* pre_rhs = leng_prefix_rhs(b, unrollMode);
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " pre_rhs: " << mk_pp(pre_rhs, m) << std::endl;);
        expr_ref_vector ands(m);

        if (elements.size() == 1) {
            ands.push_back(createEqualOP(iterA, iterB));
            ands.push_back(createEqualOP(lenA, lenB));

            for (rational i = one; i <= bound; i = i + one) {
                expr *at_i = mk_int(i);
                rational i_1 = i - one;
                expr *at_i_1 = mk_int(i_1);
                expr *premise = createGreaterEqOP(lenA, at_i);
                expr *conclusion = createEqualOP(
                        createSelectOP(arrA, createAddOP(pre_lhs, at_i_1)),
                        createSelectOP(arrB, createAddOP(pre_rhs, at_i_1)));
                ands.push_back(rewrite_implication(premise, conclusion));
            }
        }
        else {
            STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " pre_rhs: " << mk_pp(pre_rhs, m) << std::endl;);
            for (rational i = one; i <= bound; i = i + one) {
                expr *at_i = mk_int(i);
                rational i_1 = i - one;
                expr *at_i_1 = mk_int(i_1);
                expr *premise = createGreaterEqOP(lenB, at_i);
                zstring val;
                expr* arr_b = nullptr;
                if (pre_rhs == mk_int(0) && u.str.is_string(elements[pos].first, val))
                    arr_b = mk_int(val[i_1.get_int64()]);
                else
                    arr_b = createSelectOP(arrB, createAddOP(pre_rhs, at_i_1));
                expr *conclusion = createEqualOP(
                        createSelectOP(arrA, createAddOP(pre_lhs, at_i_1)),
                        arr_b);
                ands.push_back(rewrite_implication(premise, conclusion));
            }
        }

        if (!skip_init) {
            expr *reg = nullptr;
            if (is_internal_regex_var(a.first, reg)) {
                expr *to_assert = setup_regex_var(a.first, reg, arrA, bound, pre_lhs);
                ands.push_back(to_assert);
            }

            if (is_internal_regex_var(elements[pos].first, reg)) {
                expr *to_assert = setup_regex_var(a.first, reg, arrB, bound, pre_rhs);
                ands.push_back(to_assert);
            }
        }
        return createAndOP(ands);
    }

    int theory_trau::lcd(int x, int y) {
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

    bool theory_trau::match_regex(expr* a, zstring b){
        if (u.re.is_full_seq(a))
            return true;
        expr* tmp = u.re.mk_to_re(u.str.mk_string(b));
        return match_regex(a, tmp);
    }

    bool theory_trau::match_regex(expr* a, expr* b) {
        if (u.re.is_full_seq(a) || u.re.is_full_seq(b))
            return true;
        expr* intersection = u.re.mk_inter(a, b);
        eautomaton *au01 = get_automaton(intersection);
        return !au01->is_empty();
    }

    /*
     * Flat = sum (flats)
     */
    expr* theory_trau::gen_constraint02(
            expr_int a,
            pair_expr_vector const& elements,
            int pMax,
            obj_map<expr, int> const& non_fresh_variables,
            bool optimizing){

        
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(a.first, m) << std::endl;);
        for (unsigned i = 0; i < elements.size(); ++i)
            STRACE("str", tout << "  " << mk_pp(elements[i].first, m););
        STRACE("str", tout <<  std::endl;);

        if (!length_base_split(a.first, elements)){
            return nullptr;
        }

        expr_ref_vector result(m);
        expr* extra_assert = nullptr;
        if (!const_vs_str_int(a.first, elements, extra_assert)) {
            result.push_back(extra_assert);
        }

        if (!not_contain_check(a.first, elements)){
            return nullptr;
        }

        if (a.second < 0 && !is_reg_union(a.first)) { /* const string or regex */
            if (!gen_constraint02_const_regex(a, elements, pMax, non_fresh_variables, optimizing, result))
                return nullptr;
        }

        else {
            if (!generate_constraint02_var(a, elements, non_fresh_variables, optimizing, result))
                return nullptr;
        }

        expr_ref tmp(createAndOP(result), m);
        return tmp.get();
    }

    bool theory_trau::gen_constraint02_const_regex(expr_int a,
                                                   pair_expr_vector const& elements,
                                                   int pMax,
                                                   obj_map<expr, int> const& non_fresh_variables,
                                                   bool optimizing,
                                                   expr_ref_vector &result){
        
        if (a.second > REGEX_CODE) {
            zstring value;
            u.str.is_string(a.first, value);
            int max_lhs = value.length();
            int min_rhs = 0;
            for (unsigned i = 0; i < elements.size(); ++i) {
                if (elements[i].second % p_bound.get_int64() == -1) {
                    u.str.is_string(elements[i].first, value);
                    if (p_bound.get_int64() == 2 && i + 1 < elements.size() && elements[i + 1].second % p_bound.get_int64() == 0)
                        min_rhs += value.length();
                    else if (p_bound.get_int64() == 1)
                        min_rhs += value.length();
                }
                else if (elements[i].second <= REGEX_CODE){
                }
            }
            if (max_lhs < min_rhs) {
                return false;
            }
        }
        else {
            /* regex */
            // TODO: to be completed
        }

        /* collect */
        /* only handle the case of splitting const string into two parts*/
        expr_ref_vector adds(m);
        for (unsigned i = 0 ; i < elements.size(); ++i)
            if (elements[i].second <= REGEX_CODE) {
                expr_ref tmp(get_var_flat_size(elements[i]), m);
                adds.push_back(tmp.get());
            }
            else {
                zstring tmpValue;
                if (u.str.is_string(elements[i].first, tmpValue) && tmpValue.length() == 1)
                    adds.push_back(mk_int(1));
                else
                    adds.push_back(createMulOP(get_var_flat_size(elements[i]),
                                               get_flat_iter(elements[i])));
            }
        expr_ref len_lhs(m);
        if (optimizing)
            result.push_back(createEqualOP(get_var_size(a), createAddOP(adds)));
        else
            result.push_back(createEqualOP(get_var_flat_size(a), createAddOP(adds)));

        int splitType = choose_split_type(elements, non_fresh_variables, a.first);
        /*
         * 0: No const, No non_fresh_ var
         * 1: const		No non_fresh_ var
         * 2: no const, non_fresh_ var
         * 3: have both
         */
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(a.first, m) << std::endl;);
        vector<int_vector> all_possible_splits;
        expr_ref_vector strSplits(m);
        expr* reg = nullptr;
        switch (splitType) {
            case SIMPLE_CASE:
                if (is_internal_regex_var(a.first, reg))
                    result.push_back(gen_constraint_non_fresh_var(
                            a, elements,
                            non_fresh_variables,
                            optimizing,
                            pMax));
                break;
            case NON_FRESH__ONLY:
                /* handle non_fresh_ var */
                result.push_back(gen_constraint_non_fresh_var(
                        a, elements,
                        non_fresh_variables,
                        optimizing,
                        pMax));
                break;
            case CONST_ONLY:
                /* handle const */
                all_possible_splits = collect_splits(a, elements, optimizing);
                for (unsigned i = 0; i < all_possible_splits.size(); ++i) {
                    expr_ref_vector tmpp(m);
                    tmpp.append(gen_constraint_without_non_fresh_vars(a, elements, all_possible_splits[i], optimizing));
                    strSplits.push_back(createAndOP(tmpp));
                }
                if (strSplits.size() > 0)
                    result.push_back(createOrOP(strSplits));
                else
                    return false;
                break;

            case 3:
                /* handle non_fresh_ var */
                /* handle const */
                all_possible_splits = collect_splits(a, elements, optimizing);
                for (unsigned i = 0; i < all_possible_splits.size(); ++i) {
                    /* check feasibility */
                    strSplits.push_back(
                            gen_constraint_non_fresh_var_const(
                                    a,
                                    elements,
                                    all_possible_splits[i],
                                    non_fresh_variables,
                                    optimizing,
                                    pMax));
                }
                if (strSplits.size() > 0)
                    result.push_back(createOrOP(strSplits));
                else
                    return false;
                break;
            default:
                SASSERT (false);
                break;
        }
        return true;
    }

    bool theory_trau::generate_constraint02_var(expr_int a,
                                                 pair_expr_vector const& elements,
                                                 obj_map<expr, int> const& non_fresh_variables,
                                                 bool optimizing,
                                                 expr_ref_vector &result){
        
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(a.first, m) << std::endl;);

        /* do not need AND */
        /* result = sum (length) */
        expr_ref_vector adds(m);
        for (unsigned i = 0; i < elements.size(); ++i) {
            bool skip = false;
            if (i < elements.size() - 1) {
                if (elements[i].first == elements[i + 1].first &&
                    ((elements[i].second >= 0 && elements[i].second + 1 == elements[i + 1].second) ||
                     (elements[i].second < 0 && elements[i].second - 1 == elements[i + 1].second))) {

                    if (elements[i].second < 0) {
                        zstring valueStr;
                        u.str.is_string(elements[i].first, valueStr);
                        adds.push_back(mk_int(valueStr.length()));
                    }
                    else {
                        adds.push_back(mk_strlen(elements[i].first));
                    }
                    ++i;
                    skip = true;
                }
            }
            if (!skip) {
                if (elements[i].second <= REGEX_CODE) {
                    STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(elements[i].first, m) << std::endl;);
                    expr_ref tmp(get_var_flat_size(elements[i]), m);
                    adds.push_back(tmp);
                }
                else {
                    expr_ref tmp(createMulOP(get_var_flat_size(elements[i]),
                                             get_flat_iter(elements[i])), m);
                    adds.push_back(tmp);
                }
            }

        }

        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(a.first, m) << " " << ((non_fresh_variables.contains(a.first)) ? " non_fresh_" : " not non_fresh_") << std::endl;);
        expr_ref addexpr(createAddOP(adds), m);
        if (optimizing)
            result.push_back(createEqualOP(get_var_size(a), addexpr));
        else
            result.push_back(createEqualOP(get_var_flat_size(a), addexpr));
        /* DO NOT care about empty flats or not*/

        /* handle const for non_fresh_variables*/
        if (non_fresh_variables.contains(a.first)) {
            expr* tmp = unroll_non_fresh_variable(
                    a, elements,
                    non_fresh_variables, optimizing);
            result.push_back(tmp);
        }

        return true;
    }

    bool theory_trau::is_reg_union(expr* n){
        expr* reg = nullptr;
        if (is_internal_regex_var(n, reg)){
            vector<std::pair<int, int>> charRange = collect_char_range(reg);
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
    expr* theory_trau::gen_constraint_non_fresh_var_const(
            expr_int a, /* const || regex */
            pair_expr_vector const& elements, /* const + non_fresh_ var */
            int_vector const& split,
            obj_map<expr, int> const& non_fresh_variables,
            bool optimizing,
            int pMax){
        
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
            lhs_length = get_var_size(a);
        else
            lhs_length = get_var_flat_size(a);

        if (totalLength > 0) /* only has const, does not have regex */ {
            strAnd.push_back(createEqualOP(lhs_length, m_autil.mk_int(totalLength)));
        }
        expr_ref_vector addElements(m);

        addElements.reset();
        unsigned splitPos = 0;

        zstring content;
        if (a.second <= REGEX_CODE)
            content = parse_regex_content(a.first);

        for (unsigned i = 0; i < elements.size(); ++i){
            if (elements[i].second >= 0) /* not const */ {
                addElements.push_back(createMulOP(get_var_flat_size(elements[i]),
                                                  get_flat_iter(elements[i])));
                splitPos++;
            }
            else { /* const */
                if (addElements.size() > 0){ /* create a sum for previous elements */
                    splitPos--;
                    expr* constraintFornon_fresh_Var = lengthConstraint_tonon_fresh_VarConstraint(
                            a, /* const or regex */
                            elements, /* have non_fresh_ var */
                            addElements,
                            i - 1,
                            split[splitPos],
                            non_fresh_variables,
                            optimizing,
                            pMax);
                    strAnd.push_back(constraintFornon_fresh_Var);
                    if (split[splitPos] == MINUSZERO) {
                        /* looping */
                        SASSERT(a.second <= REGEX_CODE);
                        strAnd.push_back(createEqualOP(m_autil.mk_int(0), createModOP(createAddOP(addElements), m_autil.mk_int(content.length()))));
                    }
                    else if (split[splitPos] < 0) {
                        /* looping */
                        SASSERT(a.second <= REGEX_CODE);
                        strAnd.push_back(createEqualOP(createModOP(createAddOP(addElements), m_autil.mk_int(content.length())),
                                                             m_autil.mk_int(std::abs(split[splitPos]))));
                    }
                    else {
                        strAnd.push_back(createEqualOP(createAddOP(addElements), m_autil.mk_int(split[splitPos])));
                    }
                    splitPos++;
                    addElements.reset();

                }
                zstring value;
                if (u.str.is_string(elements[i].first, value) && elements[i].second % p_bound.get_int64() == -1 && i < elements.size() - 1) {
                    if (p_bound.get_int64() == 1 || value.length() == 1) {
                        strAnd.push_back(createEqualOP(get_var_flat_size(elements[i]), m_autil.mk_int(split[splitPos])));
                        splitPos++;
                    }
                    else {
                        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(elements[i].first, m) << " " << elements[i].second << mk_pp(elements[i + 1].first, m) << " " << elements[i + 1].second <<  std::endl;);
                        SASSERT(elements[i + 1].second % p_bound.get_int64() == 0);
                        strAnd.push_back(createEqualOP(createAddOP(get_var_flat_size(elements[i]), get_var_flat_size(elements[i + 1])),
                                m_autil.mk_int(split[splitPos] + split[splitPos + 1])));
                        i++;
                        splitPos += 2;
                    }
                }
                else {
                    if (split[splitPos] == MINUSZERO) {
                        /* looping at 0 */
                        SASSERT(elements[i].second <= REGEX_CODE);
                        SASSERT(a.second <= REGEX_CODE);
                        strAnd.push_back(createEqualOP(
                                m_autil.mk_int(0),
                                createModOP(get_var_flat_size(elements[i]), m_autil.mk_int(content.length()))));
                        splitPos++;
                    }
                    else if (split[splitPos] < 0) {
                        /* looping */
                        SASSERT(elements[i].second <= REGEX_CODE);
                        SASSERT(a.second <= REGEX_CODE);
                        strAnd.push_back(createEqualOP(
                                createModOP(get_var_flat_size(elements[i]), m_autil.mk_int(content.length())),
                                m_autil.mk_int(std::abs(split[splitPos++]))));
                    }
                    else {

                        if (is_regex_var(elements[i].first)){
                            expr_ref_vector tmp(m);
                            tmp.push_back(elements[i].first);
                            STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(elements[i].first, m) << std::endl;);
                            expr* constraintFornon_fresh_Var = lengthConstraint_tonon_fresh_VarConstraint(
                                    a, /* const or regex */
                                    elements, /* have non_fresh_ var */
                                    tmp,
                                    i,
                                    split[splitPos],
                                    non_fresh_variables,
                                    optimizing,
                                    pMax);
                            strAnd.push_back(constraintFornon_fresh_Var);
                        }
                        strAnd.push_back(createEqualOP(
                                get_var_flat_size(elements[i]),
                                m_autil.mk_int(split[splitPos++])));
                    }
                }
            }
        }

        if (addElements.size() > 0) {
            splitPos--;
            expr* constraintFornon_fresh_Var = lengthConstraint_tonon_fresh_VarConstraint(
                    a, /* const or regex */
                    elements, /* have non_fresh_ var */
                    addElements,
                    elements.size() - 1,
                    split[splitPos],
                    non_fresh_variables,
                    optimizing,
                    pMax);
            strAnd.push_back(constraintFornon_fresh_Var);

            /* create a sum for previous elements */
            if (split[splitPos] == MINUSZERO) {
                /* looping */
                SASSERT(a.second <= REGEX_CODE);
                strAnd.push_back(createEqualOP(
                        m_autil.mk_int(0),
                        createModOP(createAddOP(addElements), m_autil.mk_int(content.length()))));
            }
            else if (split[splitPos] < 0) {
                /* looping */
                SASSERT(a.second <= REGEX_CODE);
                strAnd.push_back(createEqualOP(
                        createModOP(createAddOP(addElements), m_autil.mk_int(content.length())),
                        m_autil.mk_int(std::abs(split[splitPos]))));
            }
            else {
                strAnd.push_back(createEqualOP(createAddOP(addElements), m_autil.mk_int(split[splitPos])));
            }
            splitPos++;
        }
        SASSERT(splitPos == split.size());
        return createAndOP(strAnd);
    }

    /*
	 *
	 */
    expr* theory_trau::lengthConstraint_tonon_fresh_VarConstraint(
            expr_int a, /* const || regex */
            pair_expr_vector const& elements,
            expr_ref_vector const& subElements,
            int currentPos,
            int subLength,
            obj_map<expr, int> const& non_fresh_variables,
            bool optimizing,
            int pMax){
        

        expr_ref_vector constraints(m);
        expr* reg = nullptr;
        for (int i = currentPos - subElements.size() + 1; i <= currentPos; ++i) {
            if (non_fresh_variables.contains(elements[i].first) || is_internal_regex_var(elements[i].first, reg)) {
                constraints.push_back(positional_non_fresh_var_in_array(
                        a, /* const or regex */
                        elements, /* have non_fresh_ var */
                        i,
                        subLength,
                        non_fresh_variables,
                        optimizing,
                        pMax));
            }
        }
        return createAndOP(constraints);

    }

    /*
	 *
	 */
    expr_ref theory_trau::positional_non_fresh_var_in_array(
            expr_int a, /* const or regex */
            pair_expr_vector const& elements, /* have non_fresh_ var */
            int var_pos,
            int var_length,
            obj_map<expr, int> const& non_fresh_variables,
            bool optimizing,
            int pMax){
        bool unrollMode = pMax == PMAX;

        
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(a.first, m) << " "  << mk_pp(elements[var_pos].first, m) << " var_length: "  << var_length << std::endl;);
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
        if (!is_regex_var(elements[var_pos].first))
            subLen = find_partsOfnon_fresh_variablesInAVector(var_pos, elements, partCnt);
        else {
            subLen = get_var_flat_size(elements[var_pos]);
        }
        expr* prefix_rhs = leng_prefix_rhs(elements[var_pos], unrollMode);
        expr* prefix_lhs = leng_prefix_lhs(a, elements, var_pos, optimizing, false);

        expr* arrayRhs = get_var_flat_array(elements[var_pos]);
        expr* arrayLhs = get_var_flat_array(a);
        if (var_length >= 0 && var_length != MINUSZERO) {
            /* sublen = var_length */
            /* at_0 = x && at_1 == y && ..*/
            int considerLength = var_length;
            expr* reg = nullptr;
            if (non_fresh_variables[elements[var_pos].first] >= 0 &&
                    !is_internal_regex_var(elements[var_pos].first, reg))
                considerLength = std::min(non_fresh_variables[elements[var_pos].first], considerLength);

            for (int k = 0; k < considerLength; ++k){
                expr* atRhs = createAddOP(m_autil.mk_int(k), prefix_rhs);
//                expr* regex = nullptr;
//                if (is_internal_regex_var(elements[var_pos].first, regex)) {
//                    if (u.re.is_plus(regex) || u.re.is_star(regex)) {
//                        atRhs = createModOP(atRhs, m_autil.mk_int(
//                                non_fresh_variables[elements[var_pos].first]));
//                    }
//                }
                resultParts.push_back(createEqualOP(
                        createSelectOP(arrayLhs, createAddOP(m_autil.mk_int(k), prefix_lhs)),
                        createSelectOP(arrayRhs, atRhs)));
            }
        }
        else {

            /* at_0 = x && at_1 == y && ..*/
            expr* len_non_fresh_Var = get_var_flat_size(elements[var_pos]);
            STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(len_non_fresh_Var, m) << std::endl;);
#if 0
            sprintf(strTmp, "(forall ((i Int)) (implies (and (< i %s) (>= i 0)) (= (select %s (+ i %s)) (select %s (mod (+ i %s) %ld)))))",
					subLen.c_str(),
					arrayRhs.c_str(),
					prefix_rhs.c_str(),
					arrayLhs.c_str(),
					prefix_lhs.c_str(),
					content.length());
			resultParts.push_back(strTmp);
#else
            if (!unrollMode){
                STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: content : " << content << std::endl;);
                for (int i = 0; i < (int)content.length(); ++i){
                    expr_ref_vector ors(m);
                    expr* at = createAddOP(m_autil.mk_int(i), prefix_lhs);
                    if (!u.str.is_string(a.first))
                        at = createModOP(at, m_autil.mk_int(content.length()));
                    expr* eq01 = createEqualOP(
                            createSelectOP(arrayRhs, m_autil.mk_int(i)),
                            createSelectOP(arrayLhs, at));
                    expr* less = createLessEqOP(len_non_fresh_Var, m_autil.mk_int(i - 1));
                    ors.push_back(eq01);
                    ors.push_back(less);
                    resultParts.push_back(createOrOP(ors));
                }
                resultParts.push_back(rewrite_implication(
                        createLessEqOP(len_non_fresh_Var, m_autil.mk_int(content.length() - 1)),
                        createEqualOP(get_flat_iter(elements[var_pos]), m_autil.mk_int(1))));
            }
            else {
                expr* lenConstraint = createLessEqOP(subLen, m_autil.mk_int(non_fresh_variables[elements[var_pos].first]));
                resultParts.push_back(lenConstraint);

                for (int i = 0; i < std::min(non_fresh_variables[elements[var_pos].first], std::min(connectingSize, 50)); ++i) {
                    expr_ref_vector ors(m);
                    expr* rhsSelect = createSelectOP(arrayRhs, createAddOP(m_autil.mk_int(i), prefix_rhs));
                    expr* at = createAddOP(m_autil.mk_int(i), prefix_lhs);

                    if (!u.str.is_string(a.first))
                        at = createModOP(at, m_autil.mk_int(content.length()));
                    expr* lhsSelect = createSelectOP(arrayLhs, at);
                    expr* eq01 = createEqualOP(
                            rhsSelect,
                            lhsSelect);
                    expr* less = createLessEqOP(len_non_fresh_Var, m_autil.mk_int(i - 1));
                    ors.push_back(eq01);
                    ors.push_back(less);
                    resultParts.push_back(createOrOP(ors));
                }
            }
#endif
        }

        expr_ref ret(createAndOP(resultParts), m);
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(ret.get(), m) << std::endl;);
        return ret;
    }

    /*
	 * Input: split a string
	 * Output: SMT
	 */
    expr_ref_vector theory_trau::gen_constraint_without_non_fresh_vars(
            expr_int a, /* const || regex */
            pair_expr_vector const& elements, /* no non_fresh_ var */
            int_vector const& split,
            bool optimizing){
        STRACE("str", tout << __LINE__ <<  " const|regex = const + ..." << std::endl;);
        
        int totalLength = 0;
        for (unsigned j = 0; j < split.size(); ++j)
            if (split[j] > 0 && split[j] != MINUSZERO)
                totalLength = totalLength + split[j];
            else {
                totalLength = -1;
                break;
            }

        expr_ref_vector ands(m);
        expr_ref len_lhs(m);
        if (optimizing)
            len_lhs = get_var_size(a);
        else
            len_lhs = get_var_flat_size(a);

        if (totalLength > 0) /* only has const, does not have regex */
            ands.push_back(createEqualOP(len_lhs, m_autil.mk_int(totalLength)));

        expr_ref_vector adds(m);

        /* simple case: check if size of all consts = 0 */
        bool sumConst_0 = true, met_var = false;
        unsigned splitPos = 0;
        for (unsigned i = 0; i < elements.size(); ++i) {
            zstring value;
            if (u.str.is_string(elements[i].first, value)) {
                if (value.length() == 1) {
                    sumConst_0 = false;
                    break;
                }
            }

            if (elements[i].second < 0) {
                if (met_var)
                    splitPos++;
                if (split[splitPos++] > 0){
                    sumConst_0 = false;
                    break;
                }
                adds.push_back(createMulOP(
                        get_var_flat_size(elements[i]),
                        get_flat_iter(elements[i])));
                met_var = false;
            }
            else
                met_var = true;
        }

        if (sumConst_0 == true) {
            STRACE("str", tout << __LINE__ <<  " const|regex = const + ...: short path" << std::endl;);
            ands.push_back(createEqualOP(m_autil.mk_int(0), createAddOP(adds)));
            return ands;
        }

        /* work as usual */
        STRACE("str", tout << __LINE__ <<  " const|regex = const + ...: work as usual" << std::endl;);
        adds.reset();
        splitPos = 0;
        zstring content;
        if (a.second <= REGEX_CODE)
            content = parse_regex_content(a.first);
        else
            u.str.is_string(a.first, content);

        for (unsigned i = 0; i < elements.size(); ++i){
            if (elements[i].second >= 0) /* not const */ {
                adds.push_back(createMulOP(get_var_flat_size(elements[i]),
                                           get_flat_iter(elements[i])));

                splitPos++;
            }
            else { /* const */
                STRACE("str", tout << __LINE__ <<  " const|regex = const + ...: work as usual " << mk_pp(elements[i].first, m) << std::endl;);
                if (adds.size() > 0){ /* create a sum for previous elements */
                    splitPos--;
                    if (split[splitPos] == MINUSZERO) {
                        /* looping */
                        SASSERT(a.second <= REGEX_CODE);
                        ands.push_back(createEqualOP(m_autil.mk_int(0), createModOP(createAddOP(adds), m_autil.mk_int(content.length()))));
                    }
                    else if (split[splitPos] < 0) {
                        /* looping */
                        SASSERT(a.second <= REGEX_CODE);
                        ands.push_back(createEqualOP(createModOP(createAddOP(adds), m_autil.mk_int(content.length())), m_autil.mk_int(std::abs(split[splitPos]))));
                    }
                    else {
                        ands.push_back(createEqualOP(createAddOP(adds), m_autil.mk_int(split[splitPos])));
                    }

                    adds.reset();
                    splitPos++;
                }

                STRACE("str", tout << __LINE__ <<  " const|regex = const + ...: work as usual" << std::endl;);
                if (elements[i].second % p_bound.get_int64() == -1 && i < elements.size() - 1 && elements[i].second > REGEX_CODE) {
                    zstring value;
                    u.str.is_string(elements[i].first, value);
                    if (p_bound.get_int64() == 1 || value.length() == 1) {
                        splitPos++;
                    }
                    else {
                        SASSERT(elements[i + 1].second % p_bound.get_int64() == 0);
                        i++;
                        splitPos += 2;
                    }
                }
                else {
                    STRACE("str", tout << __LINE__ <<  " const|regex = const + ...: work as usual" << std::endl;);
                    if (split[splitPos] == MINUSZERO) {
                        /* looping at 0 */
                        SASSERT(elements[i].second <= REGEX_CODE);
                        SASSERT(a.second <= REGEX_CODE);
                        ands.push_back(createEqualOP(
                                m_autil.mk_int(0),
                                createModOP(get_var_flat_size(elements[i]), m_autil.mk_int(content.length()))));
                        splitPos++;
                    }
                    else if (split[splitPos] < 0) {
                        /* looping */
                        SASSERT(elements[i].second <= REGEX_CODE);
                        SASSERT(a.second <= REGEX_CODE);
                        ands.push_back(createEqualOP(
                                createModOP(get_var_flat_size(elements[i]), m_autil.mk_int(content.length())),
                                m_autil.mk_int(std::abs(split[splitPos++]))));
                    }
                    else {
                        ands.push_back(createEqualOP(get_var_flat_size(elements[i]),
                                                             m_autil.mk_int(split[splitPos++])));
                    }
                }
            }
        }

        if (adds.size() > 0) {
            /* create a sum for previous elements */
            splitPos--;
            if (split[splitPos] == MINUSZERO) {
                /* looping */
                SASSERT(a.second <= REGEX_CODE);
                ands.push_back(createEqualOP(m_autil.mk_int(0), createModOP(createAddOP(adds), m_autil.mk_int(content.length()))));
            }
            else if (split[splitPos] < 0) {
                /* looping */
                SASSERT(a.second <= REGEX_CODE);
                ands.push_back(createEqualOP(
                        createModOP(createAddOP(adds), m_autil.mk_int(content.length())),
                        m_autil.mk_int(std::abs(split[splitPos]))));
            }
            else {
                ands.push_back(createEqualOP(createAddOP(adds), m_autil.mk_int(split[splitPos])));
            }
            splitPos++;
        }

        expr_ref tmp(createAndOP(ands), m);
        return ands;
    }

    /*
	 *
	 */
    expr* theory_trau::unroll_non_fresh_variable(
            expr_int a, /* non_fresh_ variable */
            pair_expr_vector const& elements, /* contain const */
            obj_map<expr, int> const& non_fresh_variables,
            bool optimizing,
            int pMax){
        
        STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " ***" << mk_pp(a.first, m) << std::endl;);
        /* (and ...) */

        expr_ref_vector ands(m);

        for (unsigned i = 0 ; i < elements.size(); ++i){
            STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " *** " << mk_pp(elements[i].first, m) << ", " << elements[i].second << " " << elements[i].second % p_bound.get_int64() << std::endl;);
            if (elements[i].second < 0){ /* const || regex */
                /* |lhs| = 1 vs |rhs| = 1*/
                if (elements.size() == 1 && p_bound.get_int64() > 1) {
                    ands.push_back(
                            handle_positional_subconst_in_array(
                                    a, elements,
                                    i,
                                    optimizing,
                                    pMax));
                }
                else if (elements[i].second <= REGEX_CODE) {
                    STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " ***"  << std::endl;);
                    expr_ref e(handle_positional_subconst_in_array(
                            a, elements,
                            i,
                            optimizing,
                            pMax), m);
                    ands.push_back(e);
                    STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " ***" << mk_pp(e.get(), m) << std::endl;);
                }
                    /* tail of string, head of elements*/
                else if (i == 0 && elements[i].second % p_bound.get_int64() == 0 && p_bound.get_int64() > 1) {
                    ands.push_back(handle_positional_subconst_in_array(
                            a, elements,
                            i,
                            optimizing,
                            pMax));
                }
                    /* head of string, tail of elements */
                else if (i == elements.size() - 1 && elements[i].second % p_bound.get_int64() == -1 && p_bound.get_int64() > 1)  {
                    ands.push_back(handle_positional_subconst_in_array(
                            a, elements,
                            i,
                            optimizing,
                            pMax));
                }
                    /* only care about first element */
                else if (elements[i].second % p_bound.get_int64() == -1)  {
                    zstring value;
                    u.str.is_string(elements[i].first, value);
                    ands.push_back(
                            handle_positional_const_in_array(
                                    a, elements,
                                    i, value, 0,
                                    value.length(),
                                    optimizing,
                                    pMax));
                }
            }
            else if (elements[i].second >= 0 && non_fresh_variables.contains(elements[i].first)){
                if (elements[i].second % p_bound.get_int64() == 1 && i > 0)
                    continue;
                int bound = std::max(non_fresh_variables[elements[i].first], non_fresh_variables[a.first]);
                if (bound >= connectingSize)
                    bound = std::min(non_fresh_variables[elements[i].first], non_fresh_variables[a.first]);
                ands.push_back(
                        handle_non_fresh_non_fresh_array(
                                a, elements, i,
                                std::min(non_fresh_variables[elements[i].first], non_fresh_variables[a.first]),
                                optimizing,
                                pMax));

            }
        }

        expr_ref ret(createAndOP(ands), m);
        return ret.get();
    }

    /*
	 * Generate constraints for the case
	 * X = T . "abc" . Y . Z
	 * constPos: position of const element
	 * return: (or (and length header = i && X_i = a && X_[i+1] = b && X_[i+2] = c))
	 */
    expr_ref theory_trau::handle_positional_subconst_in_array(
            expr_int a, // non_fresh_ var
            pair_expr_vector const& elements,
            int constPos,
            bool optimizing,
            int pMax) {
        
        STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " ***" << mk_pp(a.first, m) << std::endl;);
        SASSERT (elements[constPos].second < 0);
        bool unrollMode = pMax == PMAX;

        /* regex */
        zstring content;
        if (elements[constPos].second > REGEX_CODE)
            u.str.is_string(elements[constPos].first, content);
        else
            content = "";

        expr_ref startPos(leng_prefix_lhs(a, elements, constPos, optimizing, unrollMode), m);
        expr_ref flatArrayName(get_var_flat_array(a), m);

        expr_ref_vector possibleCases(m);
        if (elements[constPos].second <= REGEX_CODE && !u.re.is_union(elements[constPos].first)) {
            possibleCases.push_back(
                    handle_positional_regex_in_array(
                            a, elements,
                            constPos,
                            optimizing,
                            pMax));
        }
        else {
            STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " ***" << mk_pp(a.first, m) << std::endl;);
            vector<zstring> components = init_zstring_vector(content);
            if (u.re.is_union(elements[constPos].first)) {
                components.clear();
                collect_alternative_components(elements[constPos].first, components);
            }


            bool is_str_int = false;
            if (string_int_vars.find(a.first) != string_int_vars.end()){
                is_str_int = true;
            }

            for (const auto& v : components) {
                if (elements[constPos].second % p_bound.get_int64() == -1 || elements[constPos].second <= REGEX_CODE) {
                    STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " ***" << mk_pp(a.first, m) << std::endl;);
                    /* head of const */
                    expr_ref_vector oneCase(m);
                    if (components.size() != 1)
                        for (int i = 1; i <= std::min(LOCALSPLITMAX, (int)v.length()); ++i) {
                            expr_ref_vector locationConstraint(m);
                            /*length = i*/
                            locationConstraint.push_back(
                                    createLessEqOP(
                                            get_var_flat_size(elements[constPos]),
                                            m_autil.mk_int(i - 1)));
                            unrollMode ?
                            locationConstraint.push_back(
                                    createEqualOP(
                                            createSelectOP(flatArrayName, createAddOP(m_autil.mk_int(i - 1), startPos)),
                                            m_autil.mk_int(v[i - 1]))) /* arr value */
                                       :
                            locationConstraint.push_back(
                                    createEqualOP(
                                            createSelectOP(flatArrayName,
                                                                   createModOP(
                                                                           createAddOP(m_autil.mk_int(i - 1), startPos),
                                                                           m_autil.mk_int(pMax))),
                                            m_autil.mk_int(v[i - 1])));
                            oneCase.push_back(createOrOP(locationConstraint));
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
                                    createLessEqOP(get_var_flat_size(elements[constPos]),
                                                         m_autil.mk_int(i - 1)));
                            unrollMode ?
                            locationConstraint.push_back(
                                    createEqualOP(
                                            createSelectOP(flatArrayName, createAddOP(m_autil.mk_int(i - 1), startPos)),
                                            m_autil.mk_int(v[i - 1]))) /* direct value */
                                       :
                            locationConstraint.push_back(
                                    createEqualOP(
                                            createSelectOP(flatArrayName,
                                                                   createModOP(
                                                                           createAddOP(m_autil.mk_int(i - 1), startPos),
                                                                           m_autil.mk_int(pMax))),
                                            m_autil.mk_int(v[i - 1]))) /* direct value */;

                            oneCase.push_back(createOrOP(locationConstraint));
                        }
                    possibleCases.push_back(createAndOP(oneCase));
                }
                else {
                    for (int i = 0; i <= std::min(LOCALSPLITMAX, (int)v.length()); ++i) {
                        /* length = i */
                        expr_ref tmp(createEqualOP(get_var_flat_size(elements[constPos]),
                                                                m_autil.mk_int(v.length() - i)), m);
                        possibleCases.push_back(
                                handle_positional_const_in_array(
                                        a, elements,
                                        constPos, v, i, v.length(),
                                        optimizing,
                                        pMax,
                                        tmp));
                    }
                }
            }
        }

        expr_ref ret(createOrOP(possibleCases), m);
        return ret;
    }

    /*
	 * non_fresh_ = a + non_fresh_ + b
	 */
    expr* theory_trau::handle_non_fresh_non_fresh_array(
            expr_int a,
            pair_expr_vector const& elementNames,
            int pos,
            int bound,
            bool optimizing,
            int pMax){

        
        STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " ***: " << mk_pp(a.first, m) << std::endl;);
        bool unrollMode = pMax == PMAX;

        /* find the start position --> */
        expr_ref startLhs(leng_prefix_lhs(a, elementNames, pos, optimizing, unrollMode), m);
        expr_ref startRhs(leng_prefix_rhs(elementNames[pos], unrollMode), m);
        /* optimize length of generated string */
        expr* arrLhs = get_var_flat_array(a);
        expr* arrRhs = get_var_flat_array(elementNames[pos]);

        expr* lenA = get_var_flat_size(a);
        expr* lenB = get_var_flat_size(elementNames[pos]);

        expr* iterB = get_flat_iter(elementNames[pos]);

        expr_ref_vector andConstraints(m);
        expr* lenRhs = nullptr;
        /* combine two parts if it is possible */
        bool can_combine = false;
        if (elementNames[pos].second % p_bound.get_int64() == 0 &&
            pos < (int)elementNames.size() - 1 &&
                p_bound.get_int64() > 1 && elementNames[pos].second >= 0) {
            SASSERT(elementNames[pos + 1].second % p_bound.get_int64() == 1);
            SASSERT(p_bound.get_int64() == 2);
            lenRhs = get_var_size(elementNames[pos]);
            can_combine = true;
        }
        else {
            lenRhs = get_var_flat_size(elementNames[pos]);
            can_combine = false;
        }

        expr* lenLhs = nullptr;
        if (optimizing)
            lenLhs = get_var_size(a);
        else
            lenLhs = get_var_flat_size(a);


        STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " ***: " << mk_pp(a.first, m) << std::endl;);
        if (!unrollMode){
            for (int i = 1; i <= pMax; ++i){
                expr_ref_vector orConstraints(m);
                orConstraints.push_back(
                        createEqualOP(
                                createSelectOP(arrLhs,
                                                       createModOP(
                                                               createAddOP(m_autil.mk_int(i - 1), startLhs),
                                                               m_autil.mk_int(pMax))),

                                createSelectOP(arrRhs,
                                                       createModOP(
                                                               createAddOP(m_autil.mk_int(i - 1), startRhs),
                                                               m_autil.mk_int(pMax)))));

                orConstraints.push_back(createLessEqOP(lenRhs, m_autil.mk_int(i - 1)));
                andConstraints.push_back(createOrOP(orConstraints));
            }

            andConstraints.push_back(
                    rewrite_implication(
                            createLessOP(lenB, lenA),
                            createEqualOP(iterB, m_autil.mk_int(1))));
        }
        else {
            int consideredSize = bound;
            STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " ***: " << mk_pp(a.first, m) << "; size: " << consideredSize << std::endl;);
            STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " ***: " << mk_pp(a.first, m) << "; connectingSize size: " << connectingSize << std::endl;);
            if (!flat_enabled) {
                for (int i = 1; i <= consideredSize; ++i) {
                    expr_ref_vector orConstraints(m);
                    orConstraints.push_back(createEqualOP(
                            createSelectOP(arrLhs, createAddOP(m_autil.mk_int(i - 1), startLhs)),
                            createSelectOP(arrRhs, createAddOP(m_autil.mk_int(i - 1), startRhs))));
                    orConstraints.push_back(createLessEqOP(lenRhs, m_autil.mk_int(i - 1)));
                    andConstraints.push_back(createOrOP(orConstraints));
                }


                STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " ***: " << consideredSize << "; connectingSize size: " << connectingSize << std::endl;);
                if (consideredSize >= connectingSize) {
                    andConstraints.push_back(createLessEqOP(lenRhs, mk_int(connectingSize)));
                    andConstraints.push_back(createLessEqOP(lenLhs, mk_int(connectingSize)));
                }
            }
            else {
                if (optimizing) {
                    if (can_combine && elementNames.size() == p_bound.get_int64()) {
                        andConstraints.push_back(gen_constraint_var_var(a, elementNames[0], pMax, q_bound));
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
                        andConstraints.push_back(gen_constraint_flat_var(a, elementNames, pos, pMax, q_bound));
                    }
                    else
                        andConstraints.push_back(gen_constraint_flat_flat(a, elementNames, pos, pMax, q_bound));
                }

            }
        }
        return createAndOP(andConstraints);
    }

    /*
	 * Generate constraints for the case
	 * X = T . "abc"* . Y . Z
	 * regexPos: position of regex element
	 * return: forAll (i Int) and (i < |abc*|) (y[i + |T|] == a | b | c)
	 */
    expr_ref theory_trau::handle_positional_regex_in_array(
            expr_int a, // non_fresh_ var
            pair_expr_vector const& elements,
            int regexPos,
            bool optimizing,
            int pMax,
            expr *extraConstraint /* length = ? */
    ) {
        
        STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " ***" << mk_pp(a.first, m) << std::endl;);

        SASSERT (elements[regexPos].second <= REGEX_CODE);
        bool unrollMode = pMax == PMAX;

        expr_ref_vector locationConstraint(m);
        if (extraConstraint != nullptr)
            locationConstraint.push_back(extraConstraint);

        /* find the start position --> */
        expr* pre_lhs = leng_prefix_lhs(a, elements, regexPos, optimizing, unrollMode);

        /* optimize length of generated string */
        expr* lhs_array = get_var_flat_array(a);

        expr* regex_length = get_var_flat_size(elements[regexPos]);


#if 0
        char strTmp[5000];
        /* forall ((i Int)) (and (< i a.first.length()))*/
		sprintf(strTmp, "(forall ((i Int)) (implies (and (< i %s) (>= i 0)) (= (select %s (+ i %s)) (select %s (mod i %ld)))))",
				regex_length.c_str(),
				lhs_array.c_str(),
				pre_lhs.c_str(),
				rhs_array.c_str(),
				parse_regex_content(elements[regexPos].first).length());
		printf("%d %s\n", __LINE__, strTmp);
		return strTmp;

#else
        expr_ref_vector andConstraints(m);
        andConstraints.push_back(createLessEqOP(regex_length, m_autil.mk_int(connectingSize)));
        STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " ***" << mk_pp(a.first, m) << std::endl;);
        vector<std::pair<int, int>> charRange = collect_char_range(elements[regexPos].first);

        if (charRange[0].first != -1) {
            if (!unrollMode) {
                for (int i = 0; i < pMax; ++i) {
                    expr_ref_vector ors(m);
                    expr_ref_vector ors_range(m);
                    for (int j = 0; j < (int)charRange.size(); ++j) {
                        expr_ref_vector ands(m);
                        ands.push_back(createGreaterEqOP(
                                createSelectOP(lhs_array, createAddOP(m_autil.mk_int(i), pre_lhs)),
                                m_autil.mk_int(charRange[j].first)));
                        ands.push_back(createLessEqOP(
                                createSelectOP(lhs_array, createAddOP(m_autil.mk_int(i), pre_lhs)),
                                m_autil.mk_int(charRange[j].second)));
                        ors_range.push_back(createAndOP(ands));
                    }

                    ors.push_back(createOrOP(ors_range));
                    ors.push_back(createGreaterOP(m_autil.mk_int(i + 1), get_var_flat_size(elements[regexPos])));
                    andConstraints.push_back(createOrOP(ors));
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
                    for (int j = 0; j < (int)charRange.size(); ++j) {
                        expr_ref_vector ands(m);
                        ands.push_back(createGreaterEqOP(
                                createSelectOP(lhs_array, createAddOP(m_autil.mk_int(i), pre_lhs)),
                                m_autil.mk_int(charRange[j].first)));
                        ands.push_back(createLessEqOP(
                                createSelectOP(lhs_array, createAddOP(m_autil.mk_int(i), pre_lhs)),
                                m_autil.mk_int(charRange[j].second)));
                        ors_range.push_back(createAndOP(ands));
                    }
                    ors.push_back(createOrOP(ors_range));
                    ors.push_back(createGreaterOP(m_autil.mk_int(i + 1), get_var_flat_size(elements[regexPos])));
                    andConstraints.push_back(createOrOP(ors));
                }
            }
        }
        else {
            zstring strTmp = parse_regex_content(elements[regexPos].first);
            unsigned tmpNum = strTmp.length();
            if (strTmp.length() == 0) {
                expr_ref tmp(m.mk_true(), m);
                return tmp;
            }

            if (!unrollMode){
                for (int i = 0; i < pMax; ++i) {
                    expr_ref_vector ors(m);
                    ors.push_back(createEqualOP(createSelectOP(lhs_array, createAddOP(m_autil.mk_int(i), pre_lhs)),
                                                      mk_int(strTmp[i % tmpNum])));
                    ors.push_back(createGreaterOP(m_autil.mk_int(i + 1), get_var_flat_size(elements[regexPos])));
                    andConstraints.push_back(createOrOP(ors));
                }
            }
            else {
                STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " ***" << strTmp << std::endl;);
                for (int i = 0; i < std::min(connectingSize, 50); ++i) {
                    expr_ref_vector ors(m);
                    ors.push_back(createEqualOP(createSelectOP(lhs_array, createAddOP(m_autil.mk_int(i), pre_lhs)),
                            mk_int(strTmp[i % tmpNum])));
                    ors.push_back(createGreaterOP(m_autil.mk_int(i + 1), get_var_flat_size(elements[regexPos])));
                    andConstraints.push_back(createOrOP(ors));
                }
            }
        }

        expr_ref ret(createAndOP(andConstraints), m);
        return ret;
#endif
    };

    /*
	 * Generate constraints for the case
	 * X = T . "abc" . Y . Z
	 * constPos: position of const element
	 * return: (or (and length header = i && X_i = a && X_[i+1] = b && X_[i+2] = c))
	 */
    expr_ref theory_trau::handle_positional_const_in_array(
            expr_int a,
            pair_expr_vector const& elements,
            int constPos,
            zstring value, /* value of regex */
            int start, int finish,
            bool optimizing,
            int pMax,
            expr *extraConstraint /* length = ? */) {
        
        STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " ***"  << std::endl;);
        SASSERT (elements[constPos].second < 0);
        bool unrollMode = pMax == PMAX;
        expr_ref_vector locationConstraint(m);
        if (extraConstraint != nullptr)
            locationConstraint.push_back(extraConstraint);

        /* find the start position --> */
        expr_ref startPos(leng_prefix_lhs(a, elements, constPos, optimizing, unrollMode), m);

        /* optimize length of generated string */
        expr_ref tmp01(get_var_flat_array(a), m);
        expr_ref tmp02(get_var_flat_array(elements[constPos]), m);

        vector<zstring> components = init_zstring_vector(value);
        if (u.re.is_union(elements[constPos].first)) {
            components.clear();
            collect_alternative_components(elements[constPos].first, components);
        }

        expr_ref_vector orConstraints(m);
        bool is_str_int = false;
        if (string_int_vars.find(a.first) != string_int_vars.end())
            is_str_int = true;
        for (const auto &v : components) {
            if (components.size() != 1)
                for (int i = start; i < finish; ++i) {
                    unrollMode ?
                    locationConstraint.push_back(createEqualOP(
                            createSelectOP(tmp01,
                                                 createAddOP(m_autil.mk_int(i - start), startPos)),
                            createSelectOP(tmp02, m_autil.mk_int(i))))
                               :
                    locationConstraint.push_back(createEqualOP(
                            createSelectOP(tmp01,
                                                 createModOP(
                                                         createAddOP(m_autil.mk_int(i - start), startPos),
                                                         m_autil.mk_int(pMax))),
                            createSelectOP(tmp02, m_autil.mk_int(i))));
                }
            else
                for (int i = start; i < finish; ++i) {
                    if (is_str_int && (v[i] < '0' || v[i] > '9')) {
                        locationConstraint.reset();
                        break;
                    }
                    unrollMode ?
                    locationConstraint.push_back(createEqualOP(
                            createSelectOP(tmp01,
                                                 createAddOP(m_autil.mk_int(i - start), startPos)),
                            m_autil.mk_int(v[i]))) :
                    locationConstraint.push_back(createEqualOP(
                            createSelectOP(tmp01,
                                                 createModOP(
                                                         createAddOP(m_autil.mk_int(i - start), startPos),
                                                         m_autil.mk_int(pMax))),
                            m_autil.mk_int(v[i])));
                }
            orConstraints.push_back(createAndOP(locationConstraint));
        }

        expr_ref ret(createOrOP(orConstraints), m);
        STRACE("str", tout << __LINE__ << " return *** " << __FUNCTION__ << " ***" << mk_pp(ret.get(), m) << std::endl;);
        return ret;
    }

    /*
	 *
	 */
    expr* theory_trau::gen_constraint_non_fresh_var(
            expr_int a, /* const or regex */
            pair_expr_vector const& elements, /* have non_fresh_ var, do not have const */
            obj_map<expr, int> const& non_fresh_variables,
            bool optimizing,
            int pMax){
        
        STRACE("str", tout << __LINE__ << " const|regex = non_fresh_var + ..." << std::endl;);
        expr_ref arrayLhs(get_var_flat_array(a), m);
        expr_ref_vector resultParts(m);

        zstring content;
        if (a.second <= REGEX_CODE) {
            content = parse_regex_content(a.first);
        }
        else
            u.str.is_string(a.first, content);

        bool unrollMode = PMAX == pMax;
        for (unsigned i = 0; i < elements.size(); ++i){
            if (elements[i].second >= 0) /* not const */ {

                /* non_fresh_ variable */
                if (non_fresh_variables.contains(elements[i].first)) {
                    STRACE("str", tout << __LINE__ << " const|regex = non_fresh_var + ..." << std::endl;);
                    /* sublen = part_1 + part2 + .. */
                    int partCnt = 1;
                    expr_ref subLen(find_partsOfnon_fresh_variablesInAVector(i, elements, partCnt), m);

                    expr_ref prefix_rhs(leng_prefix_rhs(elements[i], unrollMode), m);
                    expr_ref prefix_lhs(leng_prefix_lhs(a, elements, i, optimizing, false), m);

                    if (a.second == REGEX_CODE) {
                        resultParts.push_back(gen_regex_non_fresh_variable(a, elements, non_fresh_variables, pMax, i, partCnt, subLen, prefix_rhs));
                    }
                    else {
                        expr_ref arrayRhs(get_var_flat_array(elements[i]), m);

                        if (p_bound.get_int64() == 1) {
                            resultParts.push_back(createEqualOP(subLen, m_autil.mk_int(content.length())));
                            for (unsigned k = 0; k < content.length(); ++k){
                                expr* at = createAddOP(m_autil.mk_int(k), prefix_lhs);

                                resultParts.push_back(createEqualOP(
                                        createSelectOP(arrayLhs, at),
                                        createSelectOP(arrayRhs, createAddOP(m_autil.mk_int(k), prefix_rhs))));
                            }
                        }
                        else {

                            STRACE("str", tout << __LINE__ << " const|regex = non_fresh_var + ...: " << content << " " << mk_pp(subLen, m) << std::endl;);
                            int localSplit = non_fresh_variables[elements[i].first];
                            expr_ref_vector ors(m); /* sublen = 0 || sublen = 1 || .. */
                            if (!unrollMode) {
                                ors.push_back(unroll_regex_non_fresh_variable(a, elements[i], pMax, partCnt, localSplit, subLen, prefix_lhs, prefix_rhs));
                            }
                            else {
                                if (content != zstring("uNkNoWn")) {
                                    ors.push_back(unroll_const_variable(a, /* const or regex */
                                                                        elements[i],
                                                                        pMax,
                                                                        localSplit,
                                                                        subLen,
                                                                        prefix_lhs,
                                                                        prefix_rhs));
                                }
                                else {
                                    ors.push_back(unroll_var_non_fresh_variable(a, elements, pMax, i, partCnt));
                                }
                            }

                            if (!is_str_int_var(elements[i].first))
                                ors.push_back(createLessEqOP(m_autil.mk_int(std::min(localSplit, (int)content.length()) + 1 ), subLen));
                            else {
                                // dont bound
                            }
                            resultParts.push_back(createOrOP(ors));
                        }
                    }
                    i += (partCnt - 1);
                }
            }
            else {
                // handling regex vs const && regex vs regex
                resultParts.push_back(gen_regex_regex(a, elements, non_fresh_variables, pMax, i));
            }
        }
        return createAndOP(resultParts);
    }

    expr* theory_trau::unroll_regex_non_fresh_variable(
            expr_int const& a, /* const or regex */
            expr_int const& b,
            int pMax,
            int part_cnt,
            int max_len,
            expr* sub_len,
            expr* prefix_lhs,
            expr* prefix_rhs){
        
        expr_ref_vector ors(m);
        expr_ref arrayLhs(get_var_flat_array(a), m);
        expr_ref arrayRhs(get_var_flat_array(b), m);

        zstring content;
        if (a.second <= REGEX_CODE) {
            content = parse_regex_content(a.first);
        }
        else
            u.str.is_string(a.first, content);

        STRACE("str", tout << __LINE__ << " const|regex = non_fresh_var + ..." << std::endl;);
        for (int j = 0; j <= std::min(max_len, (int)content.length()); j++){
            expr_ref_vector ands(m); /*at_0 = x && at_1 == y && ..*/
            ands.push_back(createEqualOP(sub_len, m_autil.mk_int(j)));
            for (int k = 0; k < j; ++k){
                ands.push_back(createEqualOP(
                        createSelectOP(arrayLhs, createAddOP(m_autil.mk_int(k), prefix_lhs)),
                        createSelectOP(arrayRhs, createModOP(createAddOP(m_autil.mk_int(k), prefix_rhs), m_autil.mk_int(pMax))
                        )));
            }
            ors.push_back(createAndOP(ands));
        }
        return createOrOP(ors);
    }

    expr* theory_trau::unroll_var_non_fresh_variable(
            expr_int a, /* const or regex */
            pair_expr_vector const& elements, /* have non_fresh_ var, do not have const */
            int pMax,
            int pos,
            int part_cnt){
        
        expr_ref_vector ands(m);
        ands.push_back(gen_constraint_flat_flat(a, elements, pos, pMax, q_bound));
        if (part_cnt == 2) {
            ands.push_back(gen_constraint_flat_flat(a, elements, pos + 1, pMax, q_bound));
        }
        return createAndOP(ands);
    }

    expr* theory_trau::unroll_const_variable(
            expr_int a, /* const or regex */
            expr_int b,
            int pMax,
            int max_len,
            expr* sub_len,
            expr* prefix_lhs,
            expr* prefix_rhs){
        
        zstring content;
        u.str.is_string(a.first, content);
        expr* unused = nullptr;
        expr_ref_vector ors(m);
        if (content.length() == 1 && not_contain(b.first, a.first, unused)){
            ors.push_back(createEqualOP(sub_len, m_autil.mk_int(0)));
            STRACE("str", tout << __LINE__ << " " << mk_pp(b.first, m) << " does not contain " << content << std::endl;);
        }
        else {
            ors.push_back(unroll_const_non_fresh_variable(a, /* const or regex */
                                                          b, /* have non_fresh_ var, do not have const */
                                                          pMax,
                                                          std::min(max_len, (int) content.length()),
                                                          sub_len,
                                                          prefix_lhs,
                                                          prefix_rhs));

            if (is_str_int_var(b.first)) {
                // must be 0
                ors.push_back(unroll_const_non_fresh_variable_str2int(a, /* const or regex */
                                                                      b,
                                                                      std::min(max_len, (int) content.length()),
                                                                      sub_len,
                                                                      prefix_lhs,
                                                                      prefix_rhs));
            }
        }
        return createOrOP(ors);
    }

    expr* theory_trau::unroll_const_non_fresh_variable_str2int(
            expr_int a, /* const or regex */
            expr_int b,
            int max_len,
            expr* sub_len,
            expr* prefix_lhs,
            expr* prefix_rhs){
        
        zstring content;
        u.str.is_string(a.first, content);
        expr_ref arrayLhs(get_var_flat_array(a), m);
        expr_ref arrayRhs(get_var_flat_array(b), m);
        expr_ref_vector ors(m);

        // must be 0
        for (int j = max_len + 1; j < (int) content.length(); ++j) {
            expr_ref_vector ands(m); /*at_0 = x && at_1 == y && ..*/
            ands.push_back(createEqualOP(sub_len, m_autil.mk_int(j)));

            // zero part: [0, j - bound)
            for (int k = 0; k < j - str_int_bound.get_int64(); ++k) {
                expr *at = createAddOP(m_autil.mk_int(k), prefix_lhs);
                rational atValue;
                expr *lhsExpr = nullptr;
                if (!m_autil.is_numeral(at, atValue))
                    lhsExpr = createSelectOP(arrayLhs, at);
                else {
                    if (content[atValue.get_int64()] != '0') {
                        STRACE("str", tout << __LINE__ << " break because of str-int: first part = 0" << std::endl;);
                        ands.reset();
                        break;
                    }
                    lhsExpr = mk_int(content[atValue.get_int64()]);
                }

                ands.push_back(createEqualOP(
                        lhsExpr,
                        createSelectOP(arrayRhs,
                                       createAddOP(m_autil.mk_int(k), prefix_rhs))));
                ands.push_back(createEqualOP(
                        lhsExpr,
                        mk_int('0')));
            }
            if (ands.size() == 0)
                break;

            // bounded part [j - bound, j)
            int start_pos = 0;
            if (j - str_int_bound.get_int64() > 0)
                start_pos = j - str_int_bound.get_int64();

            for (int k = start_pos; k < j; ++k) {
                expr *at = createAddOP(m_autil.mk_int(k), prefix_lhs);
                rational atValue;
                expr *lhsExpr = nullptr;
                if (!m_autil.is_numeral(at, atValue))
                    lhsExpr = createSelectOP(arrayLhs, at);
                else {
                    STRACE("str", tout << __LINE__
                                       << " " << atValue.get_int64() << " "
                                       << mk_pp(at, m)
                                       << std::endl;);
                    if (content[atValue.get_int64()] < '0' || content[atValue.get_int64()] > '9') {
                        STRACE("str", tout << __LINE__ << " break because of str-int: first part = 0" << std::endl;);
                        ands.reset();
                        break;
                    }
                    STRACE("str", tout << __LINE__ << " " << content << " " << atValue.get_int64() << std::endl;);
                    lhsExpr = mk_int(content[atValue.get_int64()]);
                }

                ands.push_back(createEqualOP(
                        lhsExpr,
                        createSelectOP(arrayRhs,
                                       createAddOP(m_autil.mk_int(k),
                                                   prefix_rhs))));
            }
            if (ands.size() > 0)
                ors.push_back(createAndOP(ands));
        }
        return createOrOP(ors);
    }

    expr* theory_trau::unroll_const_non_fresh_variable(
            expr_int a, /* const or regex */
            expr_int b,
            int pMax,
            int max_len,
            expr* sub_len,
            expr* prefix_lhs,
            expr* prefix_rhs){
        
        zstring content;
        u.str.is_string(a.first, content);

        expr_ref arrayLhs(get_var_flat_array(a), m);
        expr_ref arrayRhs(get_var_flat_array(b), m);
        expr_ref_vector ors(m);
        for (int j = 0; j <= std::min(max_len, (int) content.length()); j++) {
            expr_ref_vector ands(m); /*at_0 = x && at_1 == y && ..*/
            ands.push_back(createEqualOP(sub_len, m_autil.mk_int(j)));
            for (int k = 0; k < j; ++k) {
                expr *at = createAddOP(m_autil.mk_int(k), prefix_lhs);
                rational atValue;
                expr *lhsExpr = nullptr;
                if (!m_autil.is_numeral(at, atValue))
                    lhsExpr = createSelectOP(arrayLhs, at);
                else {
                    if (is_str_int_var(b.first) &&
                        (content[atValue.get_int64()] < '0' || content[atValue.get_int64()] > '9')) {
                        STRACE("str", tout << __LINE__ << " break because of str-int" << std::endl;);
                        ands.reset();
                        break;
                    }
                    lhsExpr = mk_int(content[atValue.get_int64()]);
                }

                ands.push_back(createEqualOP(
                        lhsExpr,
                        createSelectOP(arrayRhs, createAddOP(m_autil.mk_int(k),
                                                             prefix_rhs))));
            }
            if (ands.size() > 0)
                ors.push_back(createAndOP(ands));
        }
        return createOrOP(ors);
    }

    expr* theory_trau::gen_regex_non_fresh_variable(
            expr_int a, /* const or regex */
            pair_expr_vector const& elements, /* have non_fresh_ var, do not have const */
            obj_map<expr, int> const& non_fresh_variables,
            int pMax,
            int pos,
            int part_cnt,
            expr* sub_len,
            expr* prefix_rhs){
        
        zstring content;
        if (a.second <= REGEX_CODE) {
            content = parse_regex_content(a.first);
        }
        else
            u.str.is_string(a.first, content);

        bool unrollMode = PMAX == pMax;
        if (a.second == REGEX_CODE) {
            if (content.length() == 0)
                return m.mk_true();

            expr_ref_vector ret(m);
            STRACE("str", tout << __LINE__ << " const|regex = non_fresh_; content = " << content << std::endl;);
            expr_ref_vector conditions(m);
            if (part_cnt == 1) {
                STRACE("str", tout << __LINE__ << " const|regex = non_fresh_var partCnt = 1. NOT TESTED" << std::endl;);
                /* this part = regex */
                /* prefix mod lenth = 0 */
                if (content != zstring("uNkNoWn")) {
                    conditions.push_back(createEqualOP(m_autil.mk_int(0),
                                                       createModOP(prefix_rhs, m_autil.mk_int(
                                                               content.length()))));
                    conditions.push_back(createEqualOP(m_autil.mk_int(0), createModOP(sub_len,
                                                                                      m_autil.mk_int(
                                                                                              content.length()))));

                    expr_ref arrName(get_var_flat_array(elements[pos]), m);
                    expr_ref prefix(leng_prefix_rhs(elements[pos], unrollMode), m);

                    expr_ref_vector cases(m);
                    for (unsigned iter = 0; iter < connectingSize / content.length(); ++iter) {
                        expr_ref_vector subcase(m);
                        subcase.push_back(
                                createEqualOP(sub_len, m_autil.mk_int(iter * content.length())));
                        for (unsigned j = 0; j < iter * content.length(); ++j) {
                            subcase.push_back(createEqualOP(createSelectOP(arrName,
                                                                           createAddOP(
                                                                                   prefix,
                                                                                   m_autil.mk_int(
                                                                                           j))),
                                                            m_autil.mk_int(
                                                                    content[j % content.length()])));
                        }
                        cases.push_back(createAndOP(subcase));
                    }
                    conditions.push_back(createOrOP(cases));
                    ret.push_back(createAndOP(conditions));
                }
                else {
                    expr* to_assert = gen_constraint_flat_flat(a, elements, pos, pMax, q_bound);
                    ret.push_back(to_assert);
                }
            }
            else {
                STRACE("str", tout << __LINE__ << " const|regex = non_fresh_ var partCnt = 2." << std::endl;);
                SASSERT(part_cnt == 2);
                if (content != zstring("uNkNoWn")) {
                    /* this part = regex */
                    /* prefix mod length = 0 */
                    conditions.push_back(createEqualOP(m_autil.mk_int(0),
                                                       createModOP(prefix_rhs, m_autil.mk_int(
                                                               content.length()))));
                    conditions.push_back(createEqualOP(m_autil.mk_int(0), createModOP(sub_len,
                                                                                      m_autil.mk_int(
                                                                                              content.length()))));

                    expr_ref arrName(get_var_flat_array(elements[pos]), m);
                    for (unsigned iter = 0; iter < connectingSize / content.length(); ++iter) {
                        for (unsigned j = 0; j < content.length(); ++j)
                            conditions.push_back(createEqualOP(createSelectOP(arrName,
                                                                              m_autil.mk_int(j +
                                                                                             iter *
                                                                                             content.length())),
                                                               m_autil.mk_int(content[j])));
                    }
                    ret.push_back(createAndOP(conditions));
                }
                else {
                    expr* to_assert = gen_constraint_flat_flat(a, elements, pos, pMax, q_bound);
                    ret.push_back(to_assert);
                    to_assert = gen_constraint_flat_flat(a, elements, pos + 1, pMax, q_bound);
                    ret.push_back(to_assert);
                }
            }

            return createAndOP(ret);
        }

        SASSERT(false);
        return nullptr;
    }

    expr* theory_trau::gen_regex_regex(
            expr_int a, /* const or regex */
            pair_expr_vector const& elements, /* have non_fresh_ var, do not have const */
            obj_map<expr, int> const& non_fresh_variables,
            int pMax,
            int pos){
        // handling regex vs const && regex vs regex
        zstring val;
        expr *to_assert = nullptr;
        STRACE("str", tout << __LINE__
                           << mk_pp(a.first, m) << " "
                           << mk_pp(elements[pos].first, m) << " "<< std::endl;);
        if (u.str.is_string(elements[pos].first, val)) {
            to_assert = gen_constraint_flat_flat(a, elements, pos, pMax, rational(val.length()));
        }
        else
            to_assert = gen_constraint_flat_flat(a, elements, pos, pMax, q_bound);

        return to_assert;
    }

    /*
     * elements[pos] is a non_fresh_.
     * how many parts of that non_fresh_ variable are in the const | regex
     */
    expr* theory_trau::find_partsOfnon_fresh_variablesInAVector(
            int pos,
            pair_expr_vector const& elements,
            int &partCnt){
        partCnt = 1;
        
        expr_ref_vector addElements(m);
        addElements.push_back(createMulOP(get_var_flat_size(elements[pos]), get_flat_iter(elements[pos])));
        unsigned int j = pos + 1;
        for (j = pos + 1; j < elements.size(); ++j)
            if (elements[j].second > elements[j - 1].second &&
                elements[j].second > 0 &&
                elements[j].first == elements[j - 1].first &&
                elements[j].second % p_bound.get_int64() != 0 &&
                elements[j].second != REGEX_CODE) {
                partCnt++;
                addElements.push_back(createMulOP(get_var_flat_size(elements[j]),
                                                  get_flat_iter(elements[j])));
            }
            else
                break;

        /* sublen = part_1 + part2 + .. */
        return createAddOP(addElements);
    }

    /*
     * pre elements + pre fix of itself
     */
    expr* theory_trau::leng_prefix_lhs(expr_int a,
                                pair_expr_vector const& elements,
                                int pos,
                                bool optimizing,
                                bool unrollMode) {

        
        expr_ref_vector addElements(m);

        if (a.second > REGEX_CODE && !optimizing && unrollMode) {
            if (a.second % p_bound.get_int64() != -1)
                for (int i = a.second + 1; i < 0; ++i){ /* prefix of a - const */
                    addElements.push_back(
                            createMulOP(
                                    get_var_flat_size(std::make_pair(a.first, i)),
                                    get_flat_iter(std::make_pair(a.first, i))));
                    if (i % p_bound.get_int64() == -1)
                        break;
                }

            if (a.second % p_bound.get_int64() != 0)
                for (int i = a.second - 1; i >= 0; --i){ /* a is var */
                    addElements.push_back(
                            createMulOP(
                                    get_var_flat_size(std::make_pair(a.first, i)),
                                    get_flat_iter(std::make_pair(a.first, i))));
                    if (i % p_bound.get_int64() == 0)
                        break;
                }
        }

        expr* reg = nullptr;
        for (int i = pos - 1; i >= 0; --i) { /* pre-elements */
            zstring value;
            if (u.str.is_string(elements[i].first, value) && i > 0 && elements[i].second + 1 == elements[i - 1].second && (elements[i].second % p_bound.get_int64()) == 0) {
                addElements.push_back(mk_int(value.length()));
                i--;
            }
            else if (u.re.is_union(elements[i].first) || u.re.is_star(elements[i].first) ||
                u.re.is_plus(elements[i].first) || is_internal_regex_var(elements[i].first, reg)) {
                addElements.push_back(get_var_flat_size(elements[i]));
            }
            else if (i > 0 && elements[i].second - 1 == elements[i - 1].second && (elements[i].second % p_bound.get_int64()) == p_bound.get_int64() - 1) {
                addElements.push_back(mk_strlen(elements[i].first));
                i--;
            }
            else addElements.push_back(
                        createMulOP(
                                get_var_flat_size(elements[i]),
                                get_flat_iter(elements[i])));
        }
        return createAddOP(addElements);
    }

    /*
     *  pre fix of itself
     */
    expr* theory_trau::leng_prefix_rhs(
            expr_int a, /* var */
            bool unrollMode) {
        
        expr_ref_vector addElements(m);
        if (a.second > REGEX_CODE && unrollMode) {
            if (a.second % p_bound.get_int64() != -1)
                for (int i = a.second + 1; i < 0; ++i){ /* a is const */
                    addElements.push_back(createMulOP(get_var_flat_size(std::make_pair(a.first, i)),
                                                      get_flat_iter(std::make_pair(a.first, i))));
                    if (i % p_bound.get_int64() == -1)
                        break;
                }

            if (a.second % p_bound.get_int64() != 0)
                for (int i = a.second - 1; i >= 0; --i){ /* a is var */
                    addElements.push_back(createMulOP(get_var_flat_size(std::make_pair(a.first, i)),
                                                      get_flat_iter(std::make_pair(a.first, i))));
                    if (i % p_bound.get_int64() == 0)
                        break;
                }
        }
        else {
            // skip
        }

        return createAddOP(addElements);
    }

    /*
	 * Input: constA and a number of flats
	 * Output: all possible ways to split constA
	 */
    vector<int_vector > theory_trau::collect_splits(
            expr_int lhs,
            pair_expr_vector const& elements,
            bool optimizing){

        /* use alias instead of elements */
        vector<int_vector > allPossibleSplits;
        SASSERT(lhs.second < 0);

        zstring value;
        u.str.is_string(lhs.first, value);
        if (lhs.second <= REGEX_CODE) /* regex */ {
            expr* reg = nullptr;
            if (is_internal_regex_var(lhs.first, reg)) {
                if (!const_vs_regex(reg, elements)) {
                    return {};
                }
            }
            return {};
            NOT_IMPLEMENTED_YET();
//            int_vector curr;
//            zstring regexContent = parse_regex_content(lhs.first);
//            collectAllPossibleSplits_regex(0, regexContent, 10, alias, curr, allPossibleSplits);
        }
        else if (lhs.second % p_bound.get_int64() == 0) /* tail */ {
            if (optimizing){
                int_vector curr;
                collect_const_splits(0, value, 10, elements, curr, allPossibleSplits);
            }
            else for (unsigned i = 0; i <= value.length(); ++i) {
                    int_vector curr;
                    collect_const_splits(0, value.extract(i, value.length() - i), 10, elements, curr, allPossibleSplits);
                }
        }
        else if (lhs.second % p_bound.get_int64() == -1) /* head */ {
            if (p_bound.get_int64() == 1 || optimizing) {
                int_vector curr;
                collect_const_splits(0, value, 10, elements, curr, allPossibleSplits);
            }
            else for (unsigned i = 0; i <= value.length(); ++i) {
                    int_vector curr;

                    collect_const_splits(0, value.extract(0, i), 10, elements, curr, allPossibleSplits);

                }
        }
        else {
            SASSERT(false);
        }

        /* print test */
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(lhs.first, m) << std::endl;);
        for (unsigned int i = 0; i < allPossibleSplits.size(); ++i){
            for (unsigned int j = 0; j < allPossibleSplits[i].size(); ++j)
                STRACE("str", tout << allPossibleSplits[i][j] << " - ";);
            STRACE("str", tout << std::endl;);
        }

        return allPossibleSplits;
    }

//    void theory_trau::collectAllPossibleSplits_regex(
//            int pos,
//            std::string str, /* regex */
//            int pMax,
//            vector<std::pair<std::string, int> > elements,
//            int_vector currentSplit,
//            vector<int_vector > &allPossibleSplits) {
//
//        /* reach end */
//        if (currentSplit.size() == elements.size() &&
//            (pos == 0 || pos == MINUSZERO)) {
//
//            allPossibleSplits.push_back(currentSplit);
//            return;
//        }
//        else if (currentSplit.size() >= elements.size()) {
//            return;
//        }
//
//        unsigned int regexLen = str.length();
//        if (isRegexAll(str) || isRegexChar(str))
//            regexLen = 1;
//        /* special case for const: regex = .* const .* */
//        if (elements[currentSplit.size()].second == -1 && p_bound.get_int64() == 1) {
//            /* compare text, check whether the string can start from the location pos in text */
//            if (const_in_regex_at_pos(str, elements[currentSplit.size()].first, pos)) {
//                currentSplit.push_back(elements[currentSplit.size()].first.length());
//                collectAllPossibleSplits_regex((pos + elements[currentSplit.size() - 1].first.length()) % regexLen, str, pMax, elements, currentSplit, allPossibleSplits);
//                currentSplit.pop_back();
//            }
//        }
//
//            /* special case for const tail, when we know the length of const head */
//        else if (elements[currentSplit.size()]p_bound.get_int64() p_bound.get_int64() == 0 &&
//                 elements[currentSplit.size()].second < 0 &&
//                 elements[currentSplit.size()].second > REGEX_CODE &&
//                 currentSplit.size() > 0) /* tail, not the first */ {
//            assert (elements[currentSplit.size() - 1].second - 1 == elements[currentSplit.size()].second);
//            int length = elements[currentSplit.size()].first.length() - currentSplit[currentSplit.size() - 1]; /* this part gets all const string remaining */
//
//            currentSplit.push_back(length);
//            collectAllPossibleSplits_regex((pos + length) % regexLen, str, pMax, elements, currentSplit, allPossibleSplits);
//            currentSplit.pop_back();
//        }
//
//        else if (elements[currentSplit.size()].second % p_bound.get_int64() == 0 &&
//                 elements[currentSplit.size()].second < 0 &&
//                 elements[currentSplit.size()].second > REGEX_CODE &&
//                 currentSplit.size() == 0) /* tail, first */ {
//            /* find all possible start points */
//            int_vector tail = tail_in_regex_at_pos(str, elements[currentSplit.size()].first, pos);
//            for (unsigned i = 0 ; i < tail.size(); ++i) {
//                currentSplit.push_back(tail[i]);
//                collectAllPossibleSplits_regex((pos + tail[i]) % regexLen, str, pMax, elements, currentSplit, allPossibleSplits);
//                currentSplit.pop_back();
//            }
//        }
//
//        else if (elements[currentSplit.size()].second % p_bound.get_int64() == -1 &&
//                 elements[currentSplit.size()].second < 0 &&
//                 elements[currentSplit.size()].second > REGEX_CODE &&
//                 currentSplit.size() + 1 == elements.size() &&
//                 p_bound.get_int64() == 2) /* head, the last element */ {
//            /* find all possible start points */
//            int_vector head = head_in_regex_at_pos(str, elements[currentSplit.size()].first, pos);
//            for (unsigned i = 0 ; i < head.size(); ++i) {
//                currentSplit.push_back(head[i]);
//                collectAllPossibleSplits_regex((pos + head[i]) % regexLen, str, pMax, elements, currentSplit, allPossibleSplits);
//                currentSplit.pop_back();
//            }
//        }
//
//        else if (elements[currentSplit.size()].second % p_bound.get_int64() == -1 &&
//                 elements[currentSplit.size()].second < 0 &&
//                 elements[currentSplit.size()].second > REGEX_CODE &&
//                 currentSplit.size() + 1 < elements.size() &&
//                 p_bound.get_int64() == 2) /* head, not the last element */ {
//            /* check full string */
//            bool canProcess;
//            if (isUnionStr(str))
//                canProcess = true;
//            else
//                canProcess = const_in_regex_at_pos(str, elements[currentSplit.size()].first, pos);
//            if (elements[currentSplit.size() + 1].second == elements[currentSplit.size()].second - 1){
//                if (canProcess) {
//                    for (unsigned i = 1 ; i <= elements[currentSplit.size()].first.length(); ++i) { /* cannot be empty */
//                        currentSplit.push_back(i);
//                        currentSplit.push_back(elements[currentSplit.size()].first.length() - i);
//                        collectAllPossibleSplits_regex((pos + elements[currentSplit.size()].first.length()) % regexLen, str, pMax, elements, currentSplit, allPossibleSplits);
//                        currentSplit.pop_back();
//                        currentSplit.pop_back();
//                    }
//                }
//            }
//            else {
//                /* this const only has 1 part */
//                if (canProcess) {
//                    for (unsigned i = 1 ; i <= elements[currentSplit.size()].first.length(); ++i) { /* cannot be empty */
//                        currentSplit.push_back(i);
//                        collectAllPossibleSplits_regex((pos + i) % regexLen, str, pMax, elements, currentSplit, allPossibleSplits);
//                        currentSplit.pop_back();
//                    }
//                }
//            }
//        }
//
//        else if (elements[currentSplit.size()].second == REGEX_CODE) /* regex */ {
//            std::string content = parse_regex_content(elements[currentSplit.size()].first);
//            int contentLength = (int)content.length();
//
//            vector<std::string> components = {content};
//            if (isUnionStr(content)) {
//                components = collect_alternative_components(content);
//                for (const auto& s : components)
//                    contentLength = std::min(contentLength, (int)s.length());
//            }
//            int_vector regexPos = regex_in_regex_at_pos(str, elements[currentSplit.size()].first, pos);
//            /* loop ? */
//            bool loop = false;
//            if (regexPos.size() > 0 &&
//                regexPos[regexPos.size() - 1] * contentLength % regexLen == 0) {
//                loop = true;
//            }
//            __debugPrint(logFile, "%d loop = %d, regexPos size = %ld, contentLength = %d\n", __LINE__, loop ? 1 : 0, regexPos.size(), contentLength);
//
//            if (regexPos.size() == 0) {
//                currentSplit.push_back(0);
//                collectAllPossibleSplits_regex(pos, str, pMax, elements, currentSplit, allPossibleSplits);
//                currentSplit.pop_back();
//            }
//            else {
//                if (loop == true) /* assign value < 0 */
//                    for (unsigned i = 0 ; i < regexPos.size(); ++i) {
//                        /* because of loop, do not care about 0 iteration */
//                        int tmp = (contentLength * regexPos[i]) % regexLen;
//                        if (tmp == 0)
//                            currentSplit.push_back(MINUSZERO);
//                        else
//                            currentSplit.push_back(-tmp);
//                        collectAllPossibleSplits_regex((pos + contentLength * regexPos[i]) % regexLen, str, pMax, elements, currentSplit, allPossibleSplits);
//                        currentSplit.pop_back();
//                    }
//                else
//                    for (unsigned i = 0 ; i < regexPos.size(); ++i) { /* assign value >= 0 */
//                        int tmp = (pos + contentLength * regexPos[i]) % regexLen;
//                        currentSplit.push_back(contentLength * regexPos[i]);
//                        collectAllPossibleSplits_regex(tmp, str, pMax, elements, currentSplit, allPossibleSplits);
//                        currentSplit.pop_back();
//                    }
//            }
//        }
//
//        else {
//            for (unsigned i = 0; i < regexLen; ++i) { /* assign value < 0 because it can iterate many times */
//                int length = i;
//                if (length == 0)
//                    currentSplit.push_back(MINUSZERO);
//                else
//                    currentSplit.push_back(- length);
//                collectAllPossibleSplits_regex((pos + length) % regexLen, str, pMax, elements, currentSplit, allPossibleSplits);
//                currentSplit.pop_back();
//            }
//        }
//    }

    bool theory_trau::not_contain_check(expr* e, pair_expr_vector const& elements){
        zstring value;
        if (u.str.is_string(e, value)) {
            for (unsigned i = 0; i < elements.size(); ++i) {
                zstring subVar;
                if  (u.str.is_string(elements[i].first, subVar) &&
                        ((elements[i].second % p_bound.get_int64() == -1 && i + 1 < elements.size()) ||
                        subVar.length() == 1)) {
                    if (!value.contains(subVar)) {
                        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: skip quickly because of " << value << " not contain " << subVar << std::endl;);
                        return false;
                    }
                }
            }
        }

        for (unsigned i = 0; i < elements.size(); ++i) {
            zstring subVar;
            if  (u.str.is_string(elements[i].first, subVar) &&
                 ((elements[i].second % p_bound.get_int64() == -1 && i + 1 < elements.size()) ||
                  subVar.length() == 1)) {
                expr* real_haystack = nullptr;
                if (not_contain(e, elements[i].first, real_haystack)) {
                    STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: skip quickly because of " << mk_pp(e, m) << " not contain " << subVar << std::endl;);
                    return false;
                }
            }
        }
        return true;
    }

    bool theory_trau::const_vs_regex(expr* reg, pair_expr_vector const& elements){
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(reg, m) << std::endl;);
        zstring tmp;
        for (unsigned i = 0; i < elements.size(); ++i)
            if (u.str.is_string(elements[i].first, tmp) &&
                ((tmp.length() == 1) || (i < elements.size() - 1 && elements[i].second % p_bound.get_int64() == -1))) {
                if (!match_regex(reg, tmp))
                    return false;
            }
        return true;
    }

    bool theory_trau::length_base_split(expr* e, pair_expr_vector const& elements){
        expr_ref b(e, m);
        for (const auto& n : elements){
            expr_ref a(n.first, m);
            str::expr_pair p = std::make_pair(a, b);
            if (length_relation.contains(p)){
                STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " " << mk_pp(e, m) << " cannot contain because of length based split" << mk_pp(n.first, m)<< std::endl;);
                return false;
            }
        }
        return true;
    }

    bool theory_trau::const_vs_str_int(expr* e, pair_expr_vector const& elements, expr* &extra_assert){
        if (string_int_vars.contains(e)){
            for (unsigned i = 0; i < elements.size(); ++i) {
                zstring val;
                if (u.str.is_string(elements[i].first, val)) {
                    for (unsigned j = 0; j < val.length(); ++j)
                        if ((val[j] < '0' || val[j] > '9') &&
                            (val.length() == 1 ||
                             (j == 0 && elements[i].second % p_bound.get_int64() == -1) ||
                             (j == val.length() - 1 && elements[i].second % p_bound.get_int64() == 0))) {

                            expr* i2s = find_i2s(e);
                            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(i2s, m)
                                               << std::endl;);
                            if (i2s != nullptr) {
                                extra_assert = createEqualOP(i2s, mk_int(-1));
                                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(e, m)
                                                   << " cannot contain because of str-int" << mk_pp(elements[i].first, m)
                                                   << " " << mk_pp(extra_assert, m)
                                                   << std::endl;);
                            }
                            else {
                                extra_assert = createEqualOP(u.str.mk_stoi(e), mk_int(-1));
                            }

                            return false;
                        }
                }
            }
        }
        return true;
    }

    expr* theory_trau::find_i2s(expr* e){
        expr_ref_vector eqs(m);
        collect_eq_nodes(e, eqs);
        expr* a0 = nullptr;
        for (const auto& s : eqs)
            if (u.str.is_itos(s, a0)) {
                return a0;
            }

        return nullptr;
    }

    /*
	 * textLeft: length of string
	 * nMax: number of flats
	 *
	 * Pre-Condition: 1st flat and n-th flat must be greater than 0
	 * Output: of the form 1 * 1 + 1 * 0 + 1 * 0 + 1 * 0 + 1 * 0 + 1 * 0 + 1 * 0 + 1 * 0 + 1 * 3 + 2 * 3 = 10
	 */
    void theory_trau::collect_const_splits(
            int pos,
            zstring str, /* const */
            int pMax,
            pair_expr_vector const& elements,
            int_vector currentSplit,
            vector<int_vector > &allPossibleSplits
    ) {

        /* reach end */
        if (currentSplit.size() == elements.size()){
            if (pos == (int)str.length() &&
                    feasible_const_split(str, elements, currentSplit, p_bound.get_int64())) {
                allPossibleSplits.push_back(currentSplit);
            }
            else {
            }
            return;
        }

        unsigned textLeft = str.length() - pos;
        zstring value("");
        u.str.is_string(elements[currentSplit.size()].first, value);
        /* special case for const: leng = leng */
        if (p_bound.get_int64() == 1 || value.length() == 1) {
            if (value.length() <= textLeft) {
                zstring constValue = str.extract(pos, value.length());

                if (constValue == value ) {
                    currentSplit.push_back(value.length());
                    collect_const_splits(pos + value.length(), str, pMax, elements, currentSplit, allPossibleSplits);
                    currentSplit.pop_back();
                }
            }
        }

        /* const head */
        else if (elements[currentSplit.size()].second % p_bound.get_int64() == -1 &&
                elements[currentSplit.size()].second < 0 &&
                elements[currentSplit.size()].second > REGEX_CODE &&
                p_bound.get_int64() == 2) {
            STRACE("str", tout << __LINE__ << " checking str: " << value << std::endl;);
            if (value.length() <= textLeft) {
                string_set values;
                values.insert(value);

                for (const auto& v : values) {
                    zstring constValue = str.extract(pos, v.length());
                    if (constValue == v) {
                        if (values.size() > 1) {
                            STRACE("str", tout << __LINE__ << " passed value: " << value << std::endl;);
                        }
                        currentSplit.push_back(v.length());
                        collect_const_splits(pos + v.length(), str, pMax, elements, currentSplit, allPossibleSplits);
                        currentSplit.pop_back();

//                        for (int i = 0; i < std::min(7, (int)v.length()); ++i) {
//                            currentSplit.push_back(i);
//                            collect_const_splits(pos + i, str, pMax, elements, currentSplit, allPossibleSplits);
//                            currentSplit.pop_back();
//                        }
                    }
                }
            }
        }

        /* special case for const tail, when we know the length of const head */
        else if (currentSplit.size() > 0 &&
                 elements[currentSplit.size()].second % p_bound.get_int64() == 0 &&
                 elements[currentSplit.size()].second < 0 &&
                 elements[currentSplit.size()].second > REGEX_CODE &&
                p_bound.get_int64() == 2) /* const */ {
            SASSERT (elements[currentSplit.size() - 1].second % p_bound.get_int64() == -1);
            string_set values;
            values.insert(value);
            for (const auto& v : values) {
                zstring constValue = str.extract(pos - currentSplit[currentSplit.size() - 1], v.length());
                unsigned length = (unsigned)v.length() - currentSplit[currentSplit.size() - 1]; /* this part gets all const string remaining */

                if (constValue == v) {
                    if (length <= textLeft) {
                        currentSplit.push_back(length);
                        collect_const_splits(pos + length, str, pMax, elements, currentSplit, allPossibleSplits);
                        currentSplit.pop_back();
                    }
                }
            }
        }

        /* head is const part 2*/
        else if (currentSplit.size() == 0 &&
                 elements[0].second % p_bound.get_int64() == 0 &&
                 elements[0].second < 0 &&
                 elements[0].second > REGEX_CODE &&
                p_bound.get_int64() == 2) /* const */ {
            string_set values;
            if (isUnionStr(value)){
                values = get_regex_components(value);
            }
            else
                values.insert(value);
            for (const auto& v : values)
                for (unsigned i = 0; i < std::min(value.length(), str.length()); ++i) {

                    zstring tmp00 = v.extract(v.length() - i, i);
                    zstring tmp01 = str.extract(0, i);
                    if (tmp00 == tmp01){
                        if (v.length() > 1)
                            STRACE("str", tout << __LINE__ << " passed value: " << v << std::endl;);
                        currentSplit.push_back(tmp00.length());
                        collect_const_splits(pos + tmp00.length(), str, pMax, elements, currentSplit, allPossibleSplits);
                        currentSplit.pop_back();
                    }
                }
        }

        else {
            SASSERT(!(elements[currentSplit.size()].second < 0 && elements[currentSplit.size()].second > REGEX_CODE));

            std::string regexContent = "";
            expr* re = nullptr;
            is_internal_regex_var(elements[currentSplit.size()].first, re);
            if (currentSplit.size() + 1 == elements.size() && elements[currentSplit.size()].second >= 0) {
                // end by vars
                currentSplit.push_back(textLeft);
                collect_const_splits(pos + textLeft, str, pMax, elements, currentSplit, allPossibleSplits);
                currentSplit.pop_back();
            }
            else if (currentSplit.size() + 1 <= elements.size() && elements[currentSplit.size()].second >= 0 && elements[currentSplit.size() + 1].second >= 0) {
                // next element is also a var
                currentSplit.push_back(0);
                collect_const_splits(pos, str, pMax, elements, currentSplit, allPossibleSplits);
                currentSplit.pop_back();
            }
            else {
                for (unsigned i = 0; i <= textLeft; ++i) {
                    unsigned length = i;
                    if (elements[currentSplit.size()].second <= REGEX_CODE) /* regex */ {
                        STRACE("str", tout << __LINE__ << " regex: " << mk_pp(elements[currentSplit.size()].first, m) << " " <<  elements[currentSplit.size()].second << std::endl;);
                        SASSERT(re);
                        zstring regexValue = str.extract(pos, length);
                        bool matchRes = match_regex(re, regexValue);
                        if (matchRes) {
                            currentSplit.push_back(length);
                            collect_const_splits(pos + length, str, pMax, elements, currentSplit,
                                                           allPossibleSplits);
                            currentSplit.pop_back();
                        }
                    } else {
                        currentSplit.push_back(length);
                        collect_const_splits(pos + length, str, pMax, elements, currentSplit,
                                                       allPossibleSplits);
                        currentSplit.pop_back();
                    }
                }
            }
        }
    }

    /*
     * (a)|(b | c) --> {a, b, c}
     */
    theory_trau::string_set theory_trau::get_regex_components(zstring s){
        if (s.length() == 1) {
            string_set ret;
            ret.insert(s);
            return ret;
        }
        vector<zstring> components = collect_alternative_components(s);
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " *** " << std::endl;);
        if (components.size() > 0) {
            if (components.size() == 1) {
                string_set ret;
                ret.insert(components[0]);
                return ret;
            }
            string_set ret;
            for (unsigned i = 0 ; i < components.size(); ++i) {
                remove_parentheses(components[i]);
                string_set tmp = get_regex_components(components[i]);
                for (const auto& s : tmp)
                    ret.insert(s);
            }
            return ret;
        }
        else
        SASSERT(false);
        return {};
    }

    /*
     * (a) --> a
     */
    void theory_trau::remove_parentheses(zstring &s){
        while (s[0] == '(' && find_correspond_right_parentheses(0, s) == (int)s.length() - 1 && s.length() > 2)
            s = s.extract(1, s.length() - 2);
    }
    /*
	 * (a|b|c)*_xxx --> range <a, c>
	 */
    vector<std::pair<int, int>> theory_trau::collect_char_range(expr* a){
        vector<bool> chars;
        for (int i = 0; i <= 256; ++i)
            chars.push_back(false);
        collect_char_range(a, chars);
        vector<std::pair<int, int>> ret;
        if (chars[255]) {
            ret.push_back(std::make_pair(-1, -1));
            return ret;
        }
        else {
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

    void theory_trau::collect_char_range(expr* a, vector<bool> &chars){
        if (chars[255])
            return;
        expr* arg0 = nullptr;
        expr* arg1 = nullptr;
        if (u.re.is_plus(a, arg0) || u.re.is_star(a, arg0)){
            collect_char_range(arg0, chars);
        }
        else if (u.re.is_to_re(a, arg0)){
            zstring value;
            u.str.is_string(arg0, value);
            if (value.length() != 1) {
                STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " ***: give up because " << mk_pp(a, m) << " " << value << "; len " << value.length() << std::endl;);
                chars[255] = true;
            }
            else
                chars[value[0]] = true;
        }
        else if (u.re.is_union(a, arg0, arg1)){
            collect_char_range(arg0, chars);
            collect_char_range(arg1, chars);
        }
        else if (u.re.is_range(a, arg0, arg1)) {
            zstring start;
            zstring finish;
            u.str.is_string(arg0, start);
            u.str.is_string(arg1, finish);

            SASSERT(start.length() == 1);
            SASSERT(finish.length() == 1);
            zstring ret;
            for (unsigned i = start[0]; i <= finish[0]; ++i){
                chars[i] = true;
            }
        }
        else {
            expr* reg = nullptr;
            if (is_internal_regex_var(a, reg)){
                collect_char_range(reg, chars);
            }
            else {
                STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " ***: " << mk_pp(a, m) << std::endl;);
                expr* tmp = is_regex_plus_breakdown(a);
                if (tmp != nullptr)
                    collect_char_range(tmp, chars);
                else {
                    NOT_IMPLEMENTED_YET();
                    if (u.re.is_concat(a, arg0, arg1)) {
                        vector<bool> char_lhs;
                        vector<bool> char_rhs;
                        collect_char_range(arg0, char_lhs);
                        collect_char_range(arg1, char_rhs);
                    }
                }
            }
        }
    }

    bool theory_trau::feasible_const_split(
            zstring str,
            pair_expr_vector const &elements,
            int_vector const &currentSplit,
            int bound){
        /* check feasible const split */
        int pos = 0;
        for (unsigned i = 0; i < currentSplit.size(); ++i) {
            if (elements[i].second <= REGEX_CODE) {
            }

            else if (elements[i].second < 0) { /* const */
                zstring value;
                u.str.is_string(elements[i].first, value);
                if (currentSplit[i] > (int)value.length()) {
                }
                SASSERT ((int)value.length() >= currentSplit[i]);

                zstring lhs = str.extract(pos, currentSplit[i]);
                zstring rhs = "";
                if (elements[i].second % p_bound.get_int64() == -1) /* head */ {
                    rhs = value.extract(0, currentSplit[i]);

                    if (i + 1 < elements.size()) {
                        if (p_bound.get_int64() == 1 || value.length() == 1) {
                            SASSERT (currentSplit[i] == (int)value.length()); /* const length must be equal to length of const */
                        }
                        else {
                            SASSERT (elements[i + 1].second % p_bound.get_int64() == 0);
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
    int theory_trau::choose_split_type(
            pair_expr_vector const& elements,
            obj_map<expr, int> const& non_fresh_variables,
            expr* lhs){

        bool havingConst = false;
        bool havingnon_fresh_Var = false;
        expr* reg = nullptr;
        if (lhs != nullptr) {
            is_internal_regex_var(lhs, reg);
        }
        /* check if containing const */
        for (unsigned i = 0 ; i < elements.size(); ++i)
            if (elements[i].second < 0) {
                bool skip = false;
                if (reg != nullptr){
                    zstring val;
                    expr* regTmp = nullptr;
                    if (u.str.is_string(elements[i].first, val)){
                        if (match_regex(reg, val)){
                            skip = true;
                        }
                    }
                    else if (is_internal_regex_var(elements[i].first, regTmp)){
                        if (match_regex(reg, regTmp)){
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
        for (unsigned i = 0 ; i < elements.size(); ++i)
            if (non_fresh_variables.contains(elements[i].first) || elements[i].second <= REGEX_CODE) {
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

    expr* theory_trau::get_var_size(expr_int const& a){
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
    std::string theory_trau::gen_flat_iter(expr_int const& a){

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

    expr* theory_trau::get_flat_iter(expr_int const& a){
        if (u.str.is_string(a.first)){
            return mk_int(1);
        }
        else if (a.second <= REGEX_CODE) {
            return iter_map[a.first][std::abs(a.second - REGEX_CODE)];
        }
        else {
            return mk_int(1);
            return iter_map[a.first][a.second];
        }
    }

    /*
     * Given a flat,
     * generate its size constraint
     */
    std::string theory_trau::gen_flat_size(expr_int const& a){
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(a.first, m) << "," << a.second << std::endl;);
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

    expr* theory_trau::get_var_flat_size(expr_int const& a){
        zstring val;
        if (!u.str.is_string(a.first, val)) {
            if (a.second <= REGEX_CODE)
                return mk_strlen(a.first);
            else
                return length_map[a.first][std::abs(a.second)];
        }
        else {
            if (val.length() == 1)
                return mk_int(1);
            else
                return length_map[a.first][std::abs(a.second) - 1];
        }
    }

    /*
	 * Given a flat,
	 * generate its array name
	 */
    zstring theory_trau::gen_flat_arr(expr_int const& a){
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
        return zstring(result.c_str());
    }

    expr* theory_trau::get_var_flat_array(expr_int const& a){
        return get_var_flat_array(a.first);
    }

    expr* theory_trau::get_var_flat_array(expr* e){
        ensure_enode(e);
        if (array_map.contains(e))
            return array_map[e];
        expr_ref_vector eqs(m);
        collect_eq_nodes(e, eqs);
        for (unsigned i = 0; i < eqs.size(); ++i){
            if (array_map.contains(eqs[i].get())) {
                STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(e, m) << " == " << mk_pp(eqs[i].get(), m) << std::endl;);
                return array_map[eqs[i].get()];
            }
        }
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(e, m) << " " << mk_pp(e, m) << std::endl;);
        return nullptr;
    }

    expr* theory_trau::get_bound_str_int_control_var(){
        return str_int_bound_expr;
    }

    expr* theory_trau::get_bound_p_control_var(){
        return p_bound_expr;
    }

    expr* theory_trau::get_bound_q_control_var(){
        return q_bound_expr;
    }

    app* theory_trau::createITEOP(expr* c, expr* t, expr* e){
        context & ctx   = get_context();
        if (t == e)
            return to_app(t);
        app* tmp = m.mk_ite(c, t, e);
        ctx.internalize(tmp, false);
        return tmp;
    }

    /*
     *
     */
    app* theory_trau::createEqualOP(expr* x, expr* y){
        context & ctx = get_context();
        if (x == y)
            return m.mk_true();
        app* tmp = ctx.mk_eq_atom(x, y);
        ctx.internalize(tmp, false);
        return tmp;
    }

    /*
     *
     */
    app* theory_trau::createMulOP(expr *x, expr *y){
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
    app* theory_trau::createModOP(expr* x, expr* y){
        app* tmp = m_autil.mk_mod(x, y);
        return tmp;
    }


    /*
     *
     */
    app* theory_trau::createMinusOP(expr* x, expr* y){
        rational tmpValue0, tmpValue1;
        if (m_autil.is_numeral(x, tmpValue0) && m_autil.is_numeral(y, tmpValue1))
            return m_autil.mk_int(tmpValue0 - tmpValue1);

        expr* mul = createMulOP(mk_int(-1), y);
        context & ctx   = get_context();
        app* tmp = m_autil.mk_add(x, mul);
        ctx.internalize(tmp, false);
        return tmp;
    }

    /*
     *
     */
    app* theory_trau::createAddOP(expr* x, expr* y){
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
    app* theory_trau::createAddOP(expr_ref_vector adds){

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
    app* theory_trau::createLessOP(expr* x, expr* y){
        if (!m_autil.is_numeral(y)) {
            if (m_autil.is_numeral(x)) {
                rational tmp;
                get_arith_value(x, tmp);
                tmp = tmp + 1;
                return m_autil.mk_ge(y, mk_int(tmp));
            }
            else
                return m_autil.mk_ge(y, createAddOP(x, mk_int(1)));
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
    app* theory_trau::createLessEqOP(expr* x, expr* y){
        rational val_y;
        if (!m_autil.is_numeral(y, val_y))
            return m_autil.mk_ge(y, x);
        else {
            rational val_x;
            if (m_autil.is_numeral(x, val_x)){
                if (val_x <= val_y)
                    return m.mk_true();
                else
                    return m.mk_false();
            }
            else
                return m_autil.mk_le(x, y);
        }
    }

    /*
     *
     */
    app* theory_trau::createGreaterOP(expr* x, expr* y){
        if (!m_autil.is_numeral(y)) {
            if (m_autil.is_numeral(x)) {
                rational tmp;
                get_arith_value(x, tmp);
                tmp = tmp - 1;
                return m_autil.mk_le(y, mk_int(tmp));
            }
            else
                return m_autil.mk_le(createAddOP(y, mk_int(1)), x);
        }
        else {
            rational tmp;
            get_arith_value(y, tmp);
            tmp = tmp + 1;
            return m_autil.mk_ge(x, createAddOP(y, mk_int(tmp)));
        }
    }

    /*
     *
     */
    app* theory_trau::createGreaterEqOP(expr* x, expr* y){
        if (!m_autil.is_numeral(y))
            return m_autil.mk_le(y, x);
        else
            return m_autil.mk_ge(x, y);
    }

    /*
     *
     */
    app* theory_trau::createAndOP(expr_ref_vector ands){
        
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
    app* theory_trau::createOrOP(expr_ref_vector ors){
        
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
    app* theory_trau::createSelectOP(expr* x, expr* y){
        ptr_vector<expr> sel_args;
        sel_args.push_back(x);
        sel_args.push_back(y);
        context & ctx   = get_context();
        app* tmp = m_arrayUtil.mk_select(sel_args.size(), sel_args.c_ptr());
        ctx.internalize(tmp, false);
        ctx.mark_as_relevant(tmp);
        return tmp;
    }



    int theory_trau::optimized_lhs(
            int i, int startPos, int j,
            int_vector const& left_arr,
            int_vector const& right_arr,
            vector<std::pair<std::string, int>> const& lhs_elements,
            vector<std::pair<std::string, int>> const& rhs_elements){
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

    int theory_trau::optimized_rhs(
            int i, int startPos, int j,
            int_vector const& left_arr,
            int_vector const& right_arr,
            vector<std::pair<std::string, int>> const& lhs_elements,
            vector<std::pair<std::string, int>> const& rhs_elements){
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
    void theory_trau::setup_0_0_general(){
        int_vector tmpLeft;
        int_vector tmpRight;

        if (!arrangements.contains(std::make_pair(0, 0)) || arrangements[std::make_pair(0, 0)].size() == 0) {
            /* left = right */
            tmpLeft.push_back(0);
            tmpRight.push_back(0);
            vector<Arrangment> tmp;
            tmp.push_back(Arrangment(tmpLeft, tmpRight));
            arrangements.insert(std::make_pair(0, 0), tmp);
        }
    }

    /*
     * 2nd base case [0] = (sum rhs...)
     */
    void theory_trau::setup_0_n_general(int lhs, int rhs){

        /* left always has SUMFLAT */
        int_vector tmpLeft;
        tmpLeft.push_back(SUMFLAT);

        /* right has i number of 0 */
        int_vector tmpRight;
        tmpRight.push_back(0);

        for (int i = 1 ; i < rhs; ++i){
            tmpRight.push_back(0);

            vector<Arrangment> tmp04;
            tmp04.push_back(Arrangment(tmpLeft, tmpRight));

            /* update */
            /* add directly without checking */
            if (!arrangements.contains(std::make_pair(0, i)) || arrangements[std::make_pair(0, i)].size() == 0) {
                arrangements.insert(std::make_pair(0, i), tmp04);
            }
        }
    }

    /*
     * 2nd base case (sum lhs...) = [0]
     */
    void theory_trau::setup_n_0_general(int lhs, int rhs){

        /* right always has SUMFLAT */
        int_vector tmpRight;
        tmpRight.push_back(SUMFLAT);

        /* left has i number of 0 */
        int_vector tmpLeft;
        tmpLeft.push_back(0);

        for (int i = 1; i < lhs; ++i) {
            tmpLeft.push_back(0);

            vector<Arrangment> tmp04;
            tmp04.push_back(Arrangment(tmpLeft, tmpRight));

            /* add directly without checking */
            if (!arrangements.contains(std::make_pair(i, 0)) || arrangements[std::make_pair(i, 0)].size() == 0) {
                arrangements.insert(std::make_pair(i, 0), tmp04);
            }
        }
    }

    /*
     * general case
     */
    void theory_trau::setup_n_n_general(
            int lhs,
            int rhs){

        for (int i = 0 ; i < lhs; ++i)
            for (int j = 0; j < rhs; ++j)
                if (!arrangements.contains(std::make_pair(i,j))){
                    /* 2.0 [i] = empty */
                    vector<Arrangment> tmp01_ext = arrangements[std::make_pair(i - 1, j)];
                    for (unsigned int t = 0 ; t < tmp01_ext.size(); ++t) {
                        tmp01_ext[t].add_left(EMPTYFLAT);
                    }

                    /* 2.1 [j] = empty */
                    vector<Arrangment> tmp02_ext = arrangements[std::make_pair(i, j - 1)];
                    for (unsigned int t = 0 ; t < tmp02_ext.size(); ++t) {
                        tmp02_ext[t].add_right(EMPTYFLAT);
                    }

                    /* 3.1 [i] = sum(k...j) */
                    vector<Arrangment> tmp03;

                    {
                        /* [i] = sum (0..j) */
                        int_vector tmpLeft;
                        for (int k = 0; k < i; ++k)
                            tmpLeft.push_back(EMPTYFLAT);
                        tmpLeft.push_back(SUMFLAT);

                        int_vector tmpRight;
                        for (int k = 0 ; k <= j; ++k)
                            tmpRight.push_back(i);

                        SASSERT ((int)tmpLeft.size() == i + 1);
                        SASSERT ((int)tmpRight.size() == j + 1);
                        tmp03.push_back(Arrangment(tmpLeft, tmpRight));
                    }

                    /* [i] = sum (k..j) */
                    for (int k = 1; k < j; ++k) {
                        vector<Arrangment> tmp03_ext = arrangements[std::make_pair(i - 1, k - 1)];
                        for (unsigned int t = 0; t < tmp03_ext.size(); ++t) {

                            tmp03_ext[t].add_left(SUMFLAT);
                            for (int tt = k; tt <= j; ++tt)
                                tmp03_ext[t].add_right(i);


                            SASSERT ((int)tmp03_ext[t].left_arr.size() == i + 1);
                            SASSERT ((int)tmp03_ext[t].right_arr.size() == j + 1);
                        }

                        tmp03.append(tmp03_ext);
                    }

                    /* 3.2 right = sum(...left) */
                    vector<Arrangment> tmp04;

                    /* sum (k..i)  = [j] */
                    for (int k = 1; k < i; ++k) {
                        vector<Arrangment> tmp04_ext = arrangements[std::make_pair(k - 1, j - 1)];
                        for (unsigned int t = 0; t < tmp04_ext.size(); ++t) {
                            tmp04_ext[t].add_right(SUMFLAT);
                            for (int tt = k; tt <= i; ++tt)
                                tmp04_ext[t].add_left(j);

                            SASSERT ((int)tmp04_ext[t].left_arr.size() == i + 1);
                            SASSERT ((int)tmp04_ext[t].right_arr.size() == j + 1);
                        }

                        tmp04.append(tmp04_ext);
                    }

                    {
                        /* sum (0..i)  = [j] */
                        int_vector tmpLeft;
                        for (int k = 0 ; k <= i; ++k)
                            tmpLeft.push_back(j);

                        int_vector tmpRight;
                        for (int k = 0; k < j; ++k)
                            tmpRight.push_back(EMPTYFLAT);
                        tmpRight.push_back(SUMFLAT);

                        SASSERT ((int)tmpLeft.size() == i + 1);
                        SASSERT ((int)tmpRight.size() == j + 1);
                        tmp04.push_back(Arrangment(tmpLeft, tmpRight));
                    }

                    /* fourth case: left = right */
                    vector<Arrangment> tmp05 = arrangements[std::make_pair(i - 1, j - 1)];
                    for (unsigned int k = 0; k < tmp05.size(); ++k) {
                        tmp05[k].add_right(i);
                        tmp05[k].add_left(j);
                    }

                    /* update */
                    /* add directly */
                    vector<Arrangment> possibleCases;
                    possibleCases.append(tmp03);
                    possibleCases.append(tmp04);
                    possibleCases.append(tmp05);
                    arrangements.insert(std::make_pair(i, j), possibleCases);
                }
    }

    vector<std::pair<std::string, int>> theory_trau::vectorExpr2vectorStr(pair_expr_vector const& v){
        vector<std::pair<std::string, int>> ret;
        for (unsigned i = 0; i < v.size(); ++i)
            ret.push_back(std::make_pair(expr2str(v[i].first), v[i].second));
        return ret;
    }

    std::string theory_trau::expr2str(expr* node){
        std::stringstream ss;
        
        ss << mk_pp(node, m);
        return ss.str();
    }

    theory_trau::pair_expr_vector theory_trau::create_equality(expr* node, bool unfold){
        if (is_app(node)) {
            app *ap = to_app(node);
            if (u.str.is_concat(ap) && unfold){
                ptr_vector<expr> list;
                get_nodes_in_concat(node, list);
                return create_equality(list);
            }

        }
        ptr_vector<expr> list;
        list.push_back(node);
        return create_equality_final(list, unfold);
    }

    theory_trau::pair_expr_vector theory_trau::create_equality(ptr_vector<expr> const& list, bool unfold){
        ptr_vector<expr> l;
        expr* reg;
        for (unsigned i = 0; i < list.size(); ++i)
            if (!is_internal_regex_var(list[i], reg)){
                l.push_back(list[i]);
            }
            else {
                expr_ref_vector eqs(m);
                collect_eq_nodes(list[i], eqs);
                for (unsigned j = 0; j < eqs.size(); ++j) {
                    if (is_internal_regex_var(eqs[j].get(), reg)) {
                        l.push_back(eqs[j].get()); 
                        break;
                    }
                }
            }
        return create_equality_final(l);
    }

    /*
     * Input: x . y
     * Output: flat . flat . flat . flat . flat . flat
     */
    theory_trau::pair_expr_vector theory_trau::create_equality_final(ptr_vector<expr> const& list, bool unfold){
        pair_expr_vector elements;
        expr* reg = nullptr;
        for (unsigned k = 0; k < list.size(); ++k) {
            STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(list[k], m) << std::endl;);
            expr* l_k = list[k];
            zstring content;
            if (!curr_var_pieces_counter.contains(l_k))
                curr_var_pieces_counter.insert(l_k, 0);

            bool found = var_pieces_counter.contains(l_k);
            if (u.str.is_string(l_k, content)) {
                if (content.length() > 1) /* const string */ {
                    for (int j = curr_var_pieces_counter[l_k]; j < curr_var_pieces_counter[l_k] + p_bound.get_int64(); ++j) { /* split variables into p_bound.get_int64() parts */
                        elements.push_back(std::make_pair(list[k], -(j + 1)));
                    }
                    if (!found || (curr_var_pieces_counter[l_k] + p_bound.get_int64() > var_pieces_counter[l_k] )){
                        create_internal_int_vars(l_k);
                        if (!found)
                            var_pieces_counter.insert(l_k, 0);
                        var_pieces_counter[l_k] += p_bound.get_int64();
                    }
                    else {
                        reuse_internal_int_vars(l_k);
                    }
                    curr_var_pieces_counter[l_k] += p_bound.get_int64();
                }
                else if (content.length() == 1)
                    elements.push_back(std::make_pair(list[k], -1));
            }
            else if (is_internal_regex_var(l_k, reg)){
                STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(l_k, m) << std::endl;);
                if (!found || (curr_var_pieces_counter[l_k] + 1 > var_pieces_counter[l_k])){
                    create_internal_int_vars(l_k);
                    if (!found)
                        var_pieces_counter.insert(l_k, 0);
                    var_pieces_counter[l_k] += 1;
                }
                else {
                    reuse_internal_int_vars(l_k);
                }
                elements.push_back(std::make_pair(l_k, REGEX_CODE - curr_var_pieces_counter[l_k]));
                curr_var_pieces_counter[l_k] += 1;
            }
            else {
                STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(l_k, m) << "; bound = " << p_bound.get_int64() << std::endl;);
                for (int j = curr_var_pieces_counter[l_k]; j < curr_var_pieces_counter[l_k] + p_bound.get_int64(); ++j) { /* split variables into p_bound.get_int64() parts */
                    elements.push_back(std::make_pair(list[k], j));
                }

                if (!found || (curr_var_pieces_counter[l_k] + p_bound.get_int64() > var_pieces_counter[l_k] )) {
                    create_internal_int_vars(l_k);
                    if (!found)
                        var_pieces_counter.insert(l_k, 0);
                    var_pieces_counter[l_k] += p_bound.get_int64();
                }
                else {
                    STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << curr_var_pieces_counter[l_k] << " " << p_bound.get_int64() << std::endl;);
                    reuse_internal_int_vars(l_k);
                }
                curr_var_pieces_counter[l_k] += p_bound.get_int64();
            }
        }
        return elements;
    }

    void theory_trau::create_internal_int_vars(expr* v){
        if (!var_pieces_counter.contains(v))
            var_pieces_counter.insert(v, 0);
        int start = var_pieces_counter[v];
        int end = var_pieces_counter[v] + p_bound.get_int64();

        if (!length_map.contains(v)){
            ptr_vector<expr> tmp;
            length_map.insert(v, tmp);
        }

        if (!iter_map.contains(v)){
            ptr_vector<expr> tmp;
            iter_map.insert(v, tmp);
        }
        expr* regex = nullptr;
        if (u.str.is_string(v)){
            start ++;
            end ++;
        }
        else {
            if (is_internal_regex_var(v, regex)) {
                STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " " << mk_pp(v, m) << std::endl;);
                if (u.re.is_union(regex)) {
                    start = REGEX_CODE - start;

                    std::string flatSize = gen_flat_size(std::make_pair(v, start));

                    expr_ref v1(mk_int_var(flatSize), m);
                    length_map[v].push_back(v1);
                    vector<zstring> tmp;
                    collect_alternative_components(regex, tmp);
                    expr_ref_vector lenConstraints(m);
                    int_set sizes;
                    for (unsigned i = 0; i < tmp.size(); ++i) {
                        sizes.insert(tmp[i].length());
                    }
                    for (const auto& num : sizes)
                        lenConstraints.push_back(createEqualOP(v1, mk_int(num)));

                    expr_ref ors(createOrOP(lenConstraints), m);
                    assert_axiom(ors.get());
                    implied_facts.push_back(ors);
                    return;
                } else if (u.re.is_star(regex) || u.re.is_plus(regex)) {
                    start = REGEX_CODE - start;

                    std::string flatIter = gen_flat_iter(std::make_pair(v, start));

                    expr_ref v1(mk_strlen(v), m);
                    expr_ref v2(mk_int_var(flatIter), m);
                    length_map[v].push_back(v1.get());
                    iter_map[v].push_back(v2.get());
                    zstring tmp = parse_regex_content(regex);
                    expr_ref_vector constraints(m);


                    if (u.re.is_star(v)) {
                        constraints.push_back(createGreaterEqOP(v1, mk_int(0)));
                        constraints.push_back(createGreaterEqOP(v2, mk_int(0)));
                    } else {
                        constraints.push_back(createGreaterEqOP(v1, mk_int(1)));
                        constraints.push_back(createGreaterEqOP(v2, mk_int(1)));
                    }

                    if (tmp.length() == 0)
                        constraints.push_back(createEqualOP(v1, mk_int(0)));
                    else if (tmp.length() != 1 && tmp.encode().compare("uNkNoWn") != 0)
                        constraints.push_back(
                                createEqualOP(v1, createMulOP(mk_int(tmp.length()), v2)));

                    expr_ref ands(createAndOP(constraints), m);

                    assert_axiom(ands.get());
                    implied_facts.push_back(ands);
                    return;
                }
            }
        }

        expr_ref_vector adds(m);
        for (int i = start; i < end; ++i) {
            std::string flatSize = gen_flat_size(std::make_pair(v, i));
            std::string flatIter = gen_flat_iter(std::make_pair(v, i));

            expr_ref v1(mk_int_var(flatSize), m);
            expr_ref lenConstraint(createGreaterEqOP(v1, m_autil.mk_int(0)), m);
            assert_axiom(lenConstraint.get());
            implied_facts.push_back(lenConstraint);
            length_map[v].push_back(v1);

            expr_ref v2(m);
            if (u.str.is_string(v))
                v2 = mk_int(1);
            else {
                v2 = mk_int_var(flatIter);
//                assert_axiom(createGreaterEqOP(v2, m_autil.mk_int(0)));
                expr_ref iteConstraint(createEqualOP(v2, m_autil.mk_int(1)), m);
                assert_axiom(iteConstraint.get());
                implied_facts.push_back(iteConstraint);
                iter_map[v].push_back(v2);
            }
            adds.push_back(v1);
//            adds.push_back(createMulOP(v1, v2));
        }

        zstring val;
        if (u.str.is_string(v, val)){
            expr_ref sumConstraint(createEqualOP(createAddOP(adds), mk_int(val.length())), m);
            assert_axiom(sumConstraint.get());
            implied_facts.push_back(sumConstraint);
        }
        else {
            expr_ref sumConstraint(createEqualOP(createAddOP(adds), u.str.mk_length(v)), m);
            assert_axiom(sumConstraint.get());
            implied_facts.push_back(sumConstraint);

            if (string_int_vars.find(v) != string_int_vars.end()){
                setup_str_int_len(v, start);
            }
        }
    }

    void theory_trau::setup_str_int_len(expr* e, int start){
        STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " " << mk_pp(e, m)
                           << std::endl;);
        expr* part1 = get_var_flat_size(std::make_pair(e, start));
        expr* part2 = get_var_flat_size(std::make_pair(e, start + 1));
        expr* len = mk_strlen(e);

        // len <= bound --> part 1 = 0
        expr* premise = createLessEqOP(len, mk_int(str_int_bound));
        expr* conclusion = createEqualOP(part1, mk_int(0));
        expr_ref to_assert(rewrite_implication(premise, conclusion), m);
//        assert_axiom(to_assert);
//        implied_facts.push_back(to_assert);

        // len >= bound --> part 2 = bound
        rational bound_1 = str_int_bound + rational(1);
        premise = createGreaterEqOP(len, mk_int(bound_1));
        conclusion = createEqualOP(part2, mk_int(str_int_bound));
        to_assert = rewrite_implication(premise, conclusion);
        assert_axiom(to_assert);
        implied_facts.push_back(to_assert);
    }

    void theory_trau::reuse_internal_int_vars(expr* v){
        if (!curr_var_pieces_counter.contains(v))
            curr_var_pieces_counter.insert(v, 0);
        int start = curr_var_pieces_counter[v];
        int end = curr_var_pieces_counter[v] + p_bound.get_int64();
        STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << " ***: " << mk_pp(v, m) << " " << start << " " << end << std::endl;);
        if (u.str.is_string(v)){
            start ++;
            end ++;
        }
        else {
            expr* regex = nullptr;
            if (is_internal_regex_var(v, regex)) {
                STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " " << mk_pp(v, m) << std::endl;);
                if (u.re.is_union(regex)) {
                    start = REGEX_CODE - start;

                    expr_ref v1(get_var_flat_size(std::make_pair(v, start)), m);
                    vector<zstring> tmp_strs;
                    collect_alternative_components(regex, tmp_strs);
                    expr_ref_vector lenConstraints(m);
                    int_set sizes;
                    for (unsigned i = 0; i < tmp_strs.size(); ++i) {
                        sizes.insert(tmp_strs[i].length());
                    }

                    for (const auto& num : sizes)
                        lenConstraints.push_back(createEqualOP(v1, mk_int(num)));

                    expr_ref ors(createOrOP(lenConstraints), m);
                    assert_axiom(ors.get());
                    implied_facts.push_back(ors);
                    return;
                } else if (u.re.is_star(regex) || u.re.is_plus(regex)) {
                    start = REGEX_CODE - start;

                    zstring tmp = parse_regex_content(regex);
                    STRACE("str", tout << __LINE__ << " *** " << __FUNCTION__ << " " << tmp << std::endl;);
                    expr_ref_vector constraints(m);

                    expr_ref v1(get_var_flat_size(std::make_pair(v, start)), m);
                    expr_ref v2(get_flat_iter(std::make_pair(v, start)), m);
                    if (u.re.is_star(v)) {
                        constraints.push_back(createGreaterEqOP(v1, mk_int(0)));
                        constraints.push_back(createGreaterEqOP(v2, mk_int(0)));
                    } else {
                        constraints.push_back(createGreaterEqOP(v1, mk_int(1)));
                        constraints.push_back(createGreaterEqOP(v2, mk_int(1)));
                    }

                    if (tmp.length() == 0)
                        constraints.push_back(createEqualOP(v1, mk_int(0)));
                    else if (tmp.length() != 1 && tmp.encode().compare("uNkNoWn") != 0)
                        constraints.push_back(
                                createEqualOP(v1, createMulOP(mk_int(tmp.length()), v2)));

                    expr_ref ands(createAndOP(constraints), m);

                    assert_axiom(ands.get());
                    implied_facts.push_back(ands);
                    return;
                }
            }
        }

        expr_ref_vector adds(m);
        for (int i = start; i < end; ++i) {
            expr_ref v1(get_var_flat_size(std::make_pair(v, i)), m);
            expr_ref lenConstraint(createGreaterEqOP(v1, m_autil.mk_int(0)), m);
            assert_axiom(lenConstraint.get());
            implied_facts.push_back(lenConstraint);
            expr_ref v2(m);
            if (u.str.is_string(v))
                v2 = mk_int(1);
            else {
                v2 = iter_map[v][i];
                expr_ref iteConstraint(createEqualOP(v2, m_autil.mk_int(1)), m);
                assert_axiom(iteConstraint.get());
                implied_facts.push_back(iteConstraint);
            }
            adds.push_back(v1);
        }

        zstring val;
        if (u.str.is_string(v, val)){
            expr_ref sumConstraint(createEqualOP(createAddOP(adds), mk_int(val.length())), m);
            assert_axiom(sumConstraint.get());
            implied_facts.push_back(sumConstraint);
        }
        else {
            expr_ref sumConstraint(createEqualOP(createAddOP(adds), u.str.mk_length(v)), m);
            assert_axiom(sumConstraint.get());
            implied_facts.push_back(sumConstraint);
            if (string_int_vars.find(v) != string_int_vars.end()){
                setup_str_int_len(v, start);
            }
        }
    }

    /*
     *generateConstraint02
     */
    unsigned theory_trau::findMaxP(ptr_vector<expr> const& v){
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
    bool theory_trau::check_var_after_optimizing(
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
    void theory_trau::optimize_equality(
            expr* lhs,
            expr* rhs,
            ptr_vector<expr> &new_lhs,
            ptr_vector<expr> &new_rhs){
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
    bool theory_trau::propagate_equality(
            expr* lhs,
            expr* rhs,
            expr_ref_vector &to_assert){
        
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " \n" << mk_pp(lhs, m) << "\n" << mk_pp(rhs, m) <<std::endl;);
        /* cut prefix */
        ptr_vector<expr> lhs_nodes;
        get_nodes_in_concat(lhs, lhs_nodes);

        ptr_vector<expr> rhs_nodes;
        get_nodes_in_concat(rhs, rhs_nodes);

        expr_ref_vector and_lhs(m);
        expr_ref_vector and_rhs(m);

        /* cut prefix */
        int prefix = -1;
        if (!propagate_equality_left_2_right(lhs, rhs, prefix, and_lhs, to_assert))
            return false;

        /* cut suffix */
        int suffix = -1;
        if (!propagate_equality_right_2_left(lhs, rhs, suffix, and_rhs, to_assert))
            return false;

        // reach the end of equality
        if (prefix == (int)std::min(lhs_nodes.size(), rhs_nodes.size()) - 1 || suffix == (int)std::min(lhs_nodes.size(), rhs_nodes.size()) - 1)
            return true;

        and_lhs.append(and_rhs);

        if (lhs_nodes.size() == rhs_nodes.size()) {
            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " prefix " << prefix << ", suffix " << suffix << ", len " << lhs_nodes.size() << std::endl;);
            // only 1 var left
            if (prefix + 1 == (int)lhs_nodes.size() - suffix - 2)
                if (!are_equal_exprs(lhs_nodes[prefix + 1], rhs_nodes[prefix + 1])) {
                    expr* tmp = rewrite_implication(createAndOP(and_lhs), createEqualOP(lhs_nodes[prefix + 1], rhs_nodes[prefix + 1]));
                    if (!to_assert.contains(tmp))
                        to_assert.push_back(tmp);
                }
        }
//        else if (prefix >= 0 && prefix == (int)lhs_nodes.size() - 2 && prefix <= (int)rhs_nodes.size() - 3){
//            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " prefix " << prefix << ", suffix " << suffix << ", len " << lhs_nodes.size() << std::endl;);
//            // only 1 var left
//            expr* concatTmp = create_concat_from_vector(rhs_nodes, prefix);
//            if (!are_equal_exprs(lhs_nodes[prefix + 1], concatTmp)) {
//                expr* tmp = rewrite_implication(createAndOP(and_lhs), createEqualOP(lhs_nodes[prefix + 1], concatTmp));
//                if (!to_assert.contains(tmp))
//                    to_assert.push_back(tmp);
//            }
//        }
//        else if (prefix >= 0 && prefix <= (int)lhs_nodes.size() - 3 && prefix == (int)rhs_nodes.size() - 2){
//            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " prefix " << prefix << ", suffix " << suffix << ", len " << lhs_nodes.size() << std::endl;);
//            // only 1 var left
//            expr* concatTmp = create_concat_from_vector(lhs_nodes, prefix);
//            if (!are_equal_exprs(rhs_nodes[prefix + 1], concatTmp)) {
//                expr* tmp = rewrite_implication(createAndOP(and_lhs), createEqualOP(rhs_nodes[prefix + 1], concatTmp));
//                if (!to_assert.contains(tmp))
//                    to_assert.push_back(tmp);
//            }
//        }
        return true;
    }

    bool theory_trau::propagate_equality_right_2_left(
            expr* lhs,
            expr* rhs,
            int &suffix,
            expr_ref_vector &and_rhs,
            expr_ref_vector &to_assert){

        
        ptr_vector<expr> lhs_nodes;
        get_nodes_in_concat(lhs, lhs_nodes);

        ptr_vector<expr> rhs_nodes;
        get_nodes_in_concat(rhs, rhs_nodes);

        zstring l_value, r_value;
        rational len_tmp;
        for (int i = 0; i < (int)std::min(lhs_nodes.size(), rhs_nodes.size()); ++i) {
            int at = i + 1;
            if (are_equal_exprs(lhs_nodes[lhs_nodes.size() - at], rhs_nodes[rhs_nodes.size() - at])) {
                if (lhs_nodes[lhs_nodes.size() - at] != rhs_nodes[rhs_nodes.size() - at])
                    and_rhs.push_back(
                            createEqualOP(lhs_nodes[lhs_nodes.size() - at], rhs_nodes[rhs_nodes.size() - at]));
                suffix = i;
            } else if (u.str.is_string(lhs_nodes[lhs_nodes.size() - at], l_value) &&
                       u.str.is_string(rhs_nodes[rhs_nodes.size() - at], r_value)) {
                if (!l_value.suffixof(r_value) && !r_value.suffixof(l_value)) {
                    // thing goes wrong
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " goes wrong "
                                       << mk_pp(lhs_nodes[lhs_nodes.size() - at], m) << " == "
                                       << mk_pp(rhs_nodes[rhs_nodes.size() - at], m) << std::endl;);
                    negate_context(and_rhs);
                    return false;
                }

                if (l_value == r_value)
                    suffix = i;
                else
                    break;
            } else if (have_same_len(lhs_nodes[lhs_nodes.size() - at], rhs_nodes[rhs_nodes.size() - at])) {
                rational lenValue;
                get_len_value(lhs_nodes[lhs_nodes.size() - at], lenValue);
                if (!u.str.is_string(lhs_nodes[lhs_nodes.size() - at]))
                    and_rhs.push_back(createEqualOP(mk_strlen(lhs_nodes[lhs_nodes.size() - at]), mk_int(lenValue)));
                if (!u.str.is_string(rhs_nodes[rhs_nodes.size() - at]))
                    and_rhs.push_back(createEqualOP(mk_strlen(rhs_nodes[rhs_nodes.size() - at]), mk_int(lenValue)));
                suffix = i;
                expr *tmp = rewrite_implication(createAndOP(and_rhs), createEqualOP(lhs_nodes[lhs_nodes.size() - at],
                                                                                    rhs_nodes[rhs_nodes.size() - at]));
                if (!to_assert.contains(tmp))
                    to_assert.push_back(tmp);
            } else if (u.str.is_string(lhs_nodes[lhs_nodes.size() - at], l_value) &&
                       get_len_value(rhs_nodes[rhs_nodes.size() - at], len_tmp) && len_tmp.get_int64() > 0) {
                if (l_value.length() == len_tmp.get_int64()) {
                    SASSERT(false);
                } else {
                    if (l_value.length() > len_tmp.get_int64()) {
                        expr *const_str = mk_string(
                                l_value.extract(l_value.length() - len_tmp.get_int64(), len_tmp.get_int64()));
                        if (!are_equal_exprs(rhs_nodes[rhs_nodes.size() - at], const_str)) {
                            and_rhs.push_back(
                                    createEqualOP(mk_strlen(rhs_nodes[rhs_nodes.size() - at]), mk_int(len_tmp)));
                            expr *tmp_assert = rewrite_implication(
                                    createAndOP(and_rhs),
                                    createEqualOP(rhs_nodes[rhs_nodes.size() - at], const_str));
                            to_assert.push_back(tmp_assert);
                            return true;
                        } else
                            break;
                    } else
                        break;
                }
            } else if (u.str.is_string(rhs_nodes[rhs_nodes.size() - at], l_value) &&
                       get_len_value(lhs_nodes[lhs_nodes.size() - at], len_tmp) && len_tmp.get_int64() > 0) {
                if (l_value.length() == len_tmp.get_int64()) {
                    SASSERT(false);
                } else {
                    if (l_value.length() > len_tmp.get_int64()) {
                        expr *const_str = mk_string(
                                l_value.extract(l_value.length() - len_tmp.get_int64(), len_tmp.get_int64()));
                        if (are_equal_exprs(lhs_nodes[lhs_nodes.size() - at], const_str)) {
                            and_rhs.push_back(
                                    createEqualOP(mk_strlen(lhs_nodes[lhs_nodes.size() - at]), mk_int(len_tmp)));
                            expr *tmp_assert = rewrite_implication(
                                    createAndOP(and_rhs),
                                    createEqualOP(lhs_nodes[lhs_nodes.size() - at], const_str));
                            to_assert.push_back(tmp_assert);
                            return true;
                        } else
                            break;
                    } else
                        break;
                }
            } else
                break;
        }
        return true;
    }

    bool theory_trau::propagate_equality_left_2_right(
            expr* lhs,
            expr* rhs,
            int &prefix,
            expr_ref_vector &and_lhs,
            expr_ref_vector &to_assert){
        
        ptr_vector<expr> lhs_nodes;
        get_nodes_in_concat(lhs, lhs_nodes);

        ptr_vector<expr> rhs_nodes;
        get_nodes_in_concat(rhs, rhs_nodes);

        zstring l_value, r_value;
        rational len_tmp;
        for (int i = 0; i < (int)std::min(lhs_nodes.size(), rhs_nodes.size()); ++i)
            if (are_equal_exprs(lhs_nodes[i], rhs_nodes[i])) {
                if (lhs_nodes[i] != rhs_nodes[i]) {
                    and_lhs.push_back(createEqualOP(lhs_nodes[i], rhs_nodes[i]));
                }
                prefix = i;
            }
            else if (u.str.is_string(lhs_nodes[i], l_value) && u.str.is_string(rhs_nodes[i], r_value)) {
                if (!l_value.prefixof(r_value) && !r_value.prefixof(l_value)) {
                    // thing goes wrong
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " goes wrong " << mk_pp(lhs_nodes[i], m) << " == " << mk_pp(rhs_nodes[i], m) << std::endl;);
                    negate_context(and_lhs);
                    return false;
                }

                if (l_value == r_value)
                    prefix = i;
                else
                    break;
            }
            else if (have_same_len(lhs_nodes[i], rhs_nodes[i])){
                rational lenValue;
                get_len_value(lhs_nodes[i], lenValue);
                if (!u.str.is_string(lhs_nodes[i]))
                    and_lhs.push_back(createEqualOP(mk_strlen(lhs_nodes[i]), mk_int(lenValue)));
                if (!u.str.is_string(rhs_nodes[i]))
                    and_lhs.push_back(createEqualOP(mk_strlen(rhs_nodes[i]), mk_int(lenValue)));
                prefix = i;
                expr* tmp = rewrite_implication(createAndOP(and_lhs), createEqualOP(lhs_nodes[i], rhs_nodes[i]));
                if (!to_assert.contains(tmp))
                    to_assert.push_back(tmp);
            }
            else if (u.str.is_string(lhs_nodes[i], l_value) && get_len_value(rhs_nodes[i], len_tmp) && len_tmp.get_int64() > 0){
                if (l_value.length() == len_tmp.get_int64()){
                    SASSERT(false);
                }
                else {
                    if (l_value.length() > len_tmp.get_int64()){
                        expr* const_str = mk_string(l_value.extract(0, len_tmp.get_int64()));
                        if (!are_equal_exprs(rhs_nodes[i], const_str)) {
                            and_lhs.push_back(createEqualOP(mk_strlen(rhs_nodes[i]), mk_int(len_tmp)));
                            expr *tmp_assert = rewrite_implication(
                                    createAndOP(and_lhs),
                                    createEqualOP(rhs_nodes[i], const_str));
                            to_assert.push_back(tmp_assert);
                            return true;
                        }
                        else
                            break;
                    }
                    else
                        break;
                }
            }
            else if (u.str.is_string(rhs_nodes[i], l_value) && get_len_value(lhs_nodes[i], len_tmp) && len_tmp.get_int64() > 0){
                if (l_value.length() == len_tmp.get_int64()){
                    SASSERT(false);
                }
                else {
                    if (l_value.length() > len_tmp.get_int64()){
                        expr* const_str = mk_string(l_value.extract(0, len_tmp.get_int64()));
                        if (!are_equal_exprs(lhs_nodes[i], const_str)) {
                            and_lhs.push_back(createEqualOP(mk_strlen(lhs_nodes[i]), mk_int(len_tmp)));
                            expr *tmp_assert = rewrite_implication(
                                    createAndOP(and_lhs),
                                    createEqualOP(lhs_nodes[i], const_str));
                            to_assert.push_back(tmp_assert);
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

        return true;
    }

    expr* theory_trau::create_concat_from_vector(ptr_vector<expr> const& v){
        if (v.size() == 0)
            return mk_string("");
        else if (v.size() == 1)
            return v[0];

        expr* ret = v[v.size() - 1];
        for (int i = v.size() - 2; i >= 0; --i) {
            ret = mk_concat(v[i], ret);
        }

        ensure_enode(ret);
        return ret;
    }

    expr* theory_trau::create_concat_from_vector(ptr_vector<expr> const& v, int from_pos){
        if (v.size() == 0)
            return mk_string("");
        else if (v.size() == 1)
            return v[0];

        expr* ret = v[v.size() - 1];
        for (int i = v.size() - 2; i > from_pos; --i) {
            ret = mk_concat(v[i], ret);
        }
        ensure_enode(ret);
        return ret;
    }

    bool theory_trau::have_same_len(expr* lhs, expr* rhs){
        
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
    void theory_trau::optimize_equality(
            expr* lhs,
            ptr_vector<expr> const& rhs,
            ptr_vector<expr> &new_lhs,
            ptr_vector<expr> &new_rhs){
        /* cut prefix */
        ptr_vector<expr> lhsVec;
        get_nodes_in_concat(lhs, lhsVec);

        ptr_vector<expr> rhsVec;
        for (unsigned i = 0; i < rhs.size(); ++i)
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

    obj_map<expr, int> theory_trau::collect_non_fresh_vars(){
        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << std::endl;);
        clock_t t = clock();

        obj_hashtable<expr> eqc_roots = get_eqc_roots();
        obj_map<expr, int> tmp_result;
        obj_map<expr, int> occurrences = count_occurrences_from_root();
        expr_set ineq_vars = collect_non_ineq_vars();
        expr_set needles = collect_needles();
        for (const auto& nn : eqc_roots) {
            expr_ref_vector eqs(m);
            expr *value = collect_eq_nodes(nn, eqs);
            if (value == nullptr) {
                bool imp = false;
                int maxLen = 0;
                for (const auto& eq : eqs) {
                    int len = -1;
                    if (is_non_fresh_occurrence(eq, occurrences, ineq_vars, needles, len)) {
                        STRACE("str", tout << __LINE__ << "\t " << mk_pp(eq, m) << ": " << len << std::endl;);
                        imp = true;
                        maxLen = (maxLen == -1 || len == -1) ? -1 : (maxLen < len ? len : maxLen);
                    }
                }

                if (imp)
                    for (const auto& eq : eqs) {
                        STRACE("str",tout << __LINE__ << "\t \t" << mk_pp(nn, m) << " == " << mk_pp(eq, m) << std::endl;);
                        tmp_result.insert(eq, maxLen);
                    }
            }
        }

        collect_non_fresh_vars_str_int(tmp_result);

        for (const auto& nn : tmp_result)
            STRACE("str", tout << "\t "<< mk_pp(nn.m_key, m) << ": " << nn.m_value << std::endl;);

        STRACE("str", tout << __LINE__ <<  " time: " << __FUNCTION__ << ":  " << ((float)(clock() - t))/CLOCKS_PER_SEC << std::endl;);
        return tmp_result;
    }

    theory_trau::expr_set theory_trau::collect_non_ineq_vars(){
        expr_set ret;
        for (const auto& we : m_wi_expr_memo){
            bool eq_const = false;
            expr* const_value = get_eqc_value(we.second.get(), eq_const);
            if (eq_const) {
                zstring value;
                u.str.is_string(const_value, value);
                if (is_trivial_inequality(we.first.get(), value)) {
                    continue;
                }
            }

            const_value = get_eqc_value(we.first.get(), eq_const);
            if (eq_const) {
                zstring value;
                u.str.is_string(const_value, value);
                if (is_trivial_inequality(we.second.get(), value)) {
                    continue;
                }
            }

            expr_ref_vector eq_lhs(m);
            collect_eq_nodes(we.first, eq_lhs);
            for (const auto& n : eq_lhs)
                ret.insert(n);

            expr_ref_vector eq_rhs(m);
            collect_eq_nodes(we.second, eq_rhs);
            for (const auto& n : eq_rhs)
                ret.insert(n);
        }
        return ret;
    }

    theory_trau::expr_set theory_trau::collect_needles(){
        expr_set ret;
        for (const auto& we : m_wi_expr_memo){
            expr* needle = nullptr;
            if (is_contain_equality(we.second, needle)){
                bool has_eq = false;
                get_eqc_value(needle, has_eq);
                if (!has_eq)
                    ret.insert(needle);
            }

            if (is_contain_equality(we.first, needle)){
                bool has_eq = false;
                get_eqc_value(needle, has_eq);
                if (!has_eq)
                    ret.insert(needle);
            }
        }
        return ret;
    }

    void theory_trau::collect_non_fresh_vars_str_int(obj_map<expr, int> &vars){
        TRACE("str", tout << __LINE__ << " " << __FUNCTION__ << std::endl;);
        flat_enabled = false;
        if (string_int_conversion_terms.size() > 0) {
            string_int_vars.reset();
            int_string_vars.reset();
            
            expr_ref_vector guessed_eqs(m), guessed_diseqs(m);
            fetch_guessed_str_int_with_scopes(guessed_eqs, guessed_diseqs);
            expr* a0 = nullptr;
            for (const auto &e : guessed_eqs) {
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(e, m)<< std::endl;);
                app* a = to_app(e);
                if (u.str.is_stoi(a->get_arg(0), a0)){
                    add_non_fresh_var(a0, vars, str_int_bound.get_int64());
                    update_string_int_vars(a0, string_int_vars);
                    update_string_int_vars(a->get_arg(1), int_string_vars);
                }
                else if (u.str.is_itos(a->get_arg(0), a0)){
                    add_non_fresh_var(a->get_arg(1), vars, str_int_bound.get_int64());
                    update_string_int_vars(a->get_arg(1), string_int_vars);
                    update_string_int_vars(a0, int_string_vars);
                }
                else if (u.str.is_stoi(a->get_arg(1), a0)){
                    add_non_fresh_var(a0, vars, str_int_bound.get_int64());
                    update_string_int_vars(a0, string_int_vars);
                    update_string_int_vars(a->get_arg(0), int_string_vars);
                }
                else if (u.str.is_itos(a->get_arg(1), a0)){
                    add_non_fresh_var(a->get_arg(0), vars, str_int_bound.get_int64());
                    update_string_int_vars(a->get_arg(0), string_int_vars);
                    update_string_int_vars(a0, int_string_vars);
                }
            }

            for (const auto &e : guessed_diseqs) {
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(e, m)<< std::endl;);

                app* a = to_app(to_app(e)->get_arg(0));
                if (u.str.is_stoi(a->get_arg(0), a0)){
                    add_non_fresh_var(a0, vars, str_int_bound.get_int64());
                    update_string_int_vars(a0, string_int_vars);
                    update_string_int_vars(a->get_arg(1), int_string_vars);
                }
                else if (u.str.is_itos(a->get_arg(0), a0)){
                    add_non_fresh_var(a->get_arg(1), vars, str_int_bound.get_int64());
                    update_string_int_vars(a->get_arg(1), string_int_vars);
                    update_string_int_vars(a0, int_string_vars);
                }
                else if (u.str.is_stoi(a->get_arg(1), a0)){
                    add_non_fresh_var(a0, vars, str_int_bound.get_int64());
                    update_string_int_vars(a0, string_int_vars);
                    update_string_int_vars(a->get_arg(0), int_string_vars);
                }
                else if (u.str.is_itos(a->get_arg(1), a0)){
                    add_non_fresh_var(a->get_arg(0), vars, str_int_bound.get_int64());
                    update_string_int_vars(a->get_arg(0), string_int_vars);
                    update_string_int_vars(a0, int_string_vars);
                }
            }
        }

        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << vars.size() << std::endl;);
        if (vars.size() > 0)
            flat_enabled = true;
    }

    void theory_trau::add_non_fresh_var(expr* const &e, obj_map<expr, int> &vars, int len){
        if (vars.contains(e)){
            if (!(vars[e] == -1 || vars[e] > len))
                vars[e] = len;
        }
        else{
            vars.insert(e, len);
        }

    }

    void theory_trau::update_string_int_vars(expr* v, obj_hashtable<expr> &s){
        rational len_val;
        if (!(u.str.is_string_term(v) && get_len_value(v, len_val) && len_val == rational(0))) {
            expr_ref_vector eqs(m);
            collect_eq_nodes(v, eqs);
            for (const auto &n : eqs) {
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << mk_pp(v, m) << " = "
                                   << mk_pp(n, m) << std::endl;);
                s.insert(n);
            }
        }
        else {
            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << mk_pp(v, m)
                               << std::endl;);
        }
    }

    bool theory_trau::is_str_int_var(expr* e){
        return string_int_vars.contains(e);
    }

    void theory_trau::refine_important_vars(
            obj_map<expr, int> &non_fresh_vars,
            expr_ref_vector &fresh_vars,
            obj_map<expr, ptr_vector<expr>> const& eq_combination) {
        obj_map<expr, int> tmp_ret;
        
        context& ctx = get_context();
        fresh_vars.reset();
        for (const auto& nn : non_fresh_vars)
            STRACE("str", tout << __LINE__ << "\t "<< mk_pp(nn.m_key, m) << ": " << nn.m_value << std::endl;);

        obj_map<expr, int> str_int_vars;
        collect_non_fresh_vars_str_int(str_int_vars);

        for (const auto& nn : non_fresh_vars) {
            if (!tmp_ret.contains(nn.m_key)) {
                rational len_val;
                if (get_len_value(nn.m_key, len_val) && len_val == rational(0))
                    continue;
                if (is_non_fresh_recheck(nn.m_key, nn.m_value, eq_combination) || str_int_vars.contains(nn.m_key)) {
                    expr_ref_vector eqs(m);
                    collect_eq_nodes(nn.m_key, eqs);
                    for (unsigned i = 0; i < eqs.size(); ++i) {
                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(nn.m_key, m) << " --> " << mk_pp(eqs[i].get(), m) << std::endl;);
                        tmp_ret.insert(eqs[i].get(), nn.m_value);
                    }
                }
            }
        }

        for (const auto& nn : non_fresh_vars)
            if (!tmp_ret.contains(nn.m_key)){
                expr_ref_vector eqs(m);
                collect_eq_nodes(nn.m_key, eqs);
                for (unsigned i = 0; i < eqs.size(); ++i)
                    if (!fresh_vars.contains(eqs[i].get())){
                        fresh_vars.push_back(eqs[i].get());
                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " not important " << mk_pp(eqs[i].get(), m) << std::endl;);
                    }
            }

        obj_map<expr, int> occurrences = count_occurrences_from_combination(eq_combination, non_fresh_vars);

        pair_expr_vector non_fresh_varsTmp;
        for (const auto& v : tmp_ret)
            if (!fresh_vars.contains(v.m_key) || str_int_vars.contains(v.m_key)) {
                if (v.m_value == -1) {
                    expr* rootTmp = ctx.get_enode(v.m_key)->get_root()->get_owner();
                    if (!more_than_two_occurrences(rootTmp, occurrences) &&
                            !more_than_two_occurrences(v.m_key, occurrences) &&
                            ((eq_combination.contains(rootTmp) && eq_combination[rootTmp].size() <= 20) || !eq_combination.contains(rootTmp)) &&
                            !is_contain_equality(v.m_key) &&
                            !str_int_vars.contains(v.m_key) &&
                            !belong_to_var_var_inequality(v.m_key) &&
                            !is_internal_regex_var(v.m_key)) {
                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " remove " << mk_pp(v.m_key, m) << std::endl;);
                        expr_ref_vector eqs(m);
                        collect_eq_nodes(v.m_key, eqs);
                        for (unsigned i = 0; i < eqs.size(); ++i)
                            if (!fresh_vars.contains(eqs[i].get())){
                                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " not important " << mk_pp(eqs[i].get(), m) << std::endl;);
                                fresh_vars.push_back(eqs[i].get());
                            }
                    } else
                        non_fresh_varsTmp.insert(std::make_pair(v.m_key, v.m_value));
                } else {
                    non_fresh_varsTmp.insert(std::make_pair(v.m_key, v.m_value));
                }
            }

        non_fresh_vars.reset();
        for (const auto& v : non_fresh_varsTmp)
            if (!fresh_vars.contains(v.first) || str_int_vars.contains(v.first))
                non_fresh_vars.insert(v.first, v.second);

        for (const auto& v : eq_combination)
            if (v.get_value().size() >= 6) {
                expr_ref_vector eqs(m);
                collect_eq_nodes(v.m_key, eqs);
                for (unsigned i = 0; i < eqs.size(); ++i)
                    non_fresh_vars.insert(eqs[i].get(), -1);
            }

        TRACE("str", tout << __LINE__ << __FUNCTION__ << std::endl;);
        for (const auto& nn : non_fresh_vars)
            STRACE("str", tout << "\t "<< mk_pp(nn.m_key, m) << ": " << nn.m_value << std::endl;);
    }

    bool theory_trau::more_than_two_occurrences(expr* n, obj_map<expr, int> const& occurrences){
        expr_ref_vector eqs(m);
        collect_eq_nodes(n, eqs);
        for (const auto& nn : eqs)
            if (occurrences.contains(nn) && occurrences[nn] >= 2)
                return true;

        return false;
    }
    bool theory_trau::is_non_fresh_occurrence(expr *nn, obj_map<expr, int> const &occurrences, expr_set const& ineq_vars, expr_set const& needles, int &len){
        len = -1;
        // not equal to any concat/const
        expr_ref_vector eqs(m);
        expr *value = collect_eq_nodes(nn, eqs);
        if (value != nullptr)
            return false;
        if (check_union_membership(nn, len))
            return true;
        if (collect_not_contains(nn, ineq_vars, needles))
            return true;
        vector<zstring> max_diseq_strs;
        if (ineq_vars.contains(nn))
            max_diseq_strs = collect_all_inequalities(nn);
        if (max_diseq_strs.size() > 0)
            len = max_diseq_strs[0].length();

        if (len > 0 && max_diseq_strs[0] == "__var__"){
            len = -1;
            return true;
        }

        if (len > 0) {
            clock_t t = clock();
            zstring const_part = "";
            for (const auto& n : eqs) {
                if (u.str.is_concat(n)) {
                    ptr_vector<expr> nodes;
                    get_nodes_in_concat(n, nodes);
                    zstring all_consts = "";
                    for (const auto& m : nodes) {
                        zstring valueStr;
                        bool has_eqc_value = false;
                        expr *constValue = get_eqc_value(m, has_eqc_value);
                        if (has_eqc_value) {
                            u.str.is_string(constValue, valueStr);
                            all_consts = all_consts + valueStr;
                        }
                    }

                    if (all_consts.length() > const_part.length()) {
                        const_part = all_consts;
                    }
                }
            }

            bool allEqual = true;
            for (const auto& s : max_diseq_strs) {
                if (const_part != s) {
                    allEqual = false;
                }
            }
            STRACE("str", tout << __LINE__ <<  " time: " << __FUNCTION__ << ":  " << ((float)(clock() - t))/CLOCKS_PER_SEC << std::endl;);
            if ((len > (int)const_part.length() || (len == (int)const_part.length() && allEqual)))
                return true;
        }

        len = -1;
        for (const auto& eq : eqs)
            if (u.str.is_concat(eq))
                return false;
        // now we know it is a leaf node
        // --> check if their parents are fresh
        if (occurrences.contains(nn))
            if (occurrences[nn] >= 2) {
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": " << mk_pp(nn, m) << " == " << len << std::endl;);
                return true;
            }
        return false;
    }

    obj_map<expr, int> theory_trau::count_occurrences_from_root(){
        obj_map<expr, int> ret;
        for (const auto& n : concat_astNode_map){
            expr* arg0 = n.get_key1();
            expr* arg1 = n.get_key2();
            if (arg0 == arg1)
                ret.insert(arg0, 2);
            else {
                if (ret.contains(arg0) && (!is_internal_var(arg0) || is_replace_var(arg0)))
                    ret[arg0]++;
                else
                    ret.insert(arg0, 1);

                if (ret.contains(arg1) && (!is_internal_var(arg1) || is_replace_var(arg1)))
                    ret[arg1]++;
                else
                    ret.insert(arg1, 1);
            }
        }
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << std::endl;);
        for (const auto& p : ret)
            if (p.m_value >= 2)
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << mk_pp(p.m_key, m) << std::endl;);

        return ret;
    }

    bool theory_trau::is_replace_var(expr* x){
        if (u.str.is_concat(x) || u.str.is_at(x) || u.str.is_extract(x) || u.str.is_replace(x) || u.str.is_itos(x))
            return false;
        std::string s = expr2str(x);
        if (s.find("replace1!") == 0 || s.find("replace2!") == 0)
            return true;
        else
            return false;
    }

    obj_map<expr, int> theory_trau::count_occurrences_from_combination(
            obj_map<expr, ptr_vector<expr>> const &eq_combination,
            obj_map<expr, int> const &non_fresh_vars) {
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << std::endl;);
        obj_map<expr, int> ret;

        for (const auto& v : eq_combination){
            // inside one variable
            obj_map<expr, expr*> occurrenceLocation;
            if (!(v.get_value().size() >= 2 || u.str.is_string(v.m_key) || (v.get_value().size() == 1 &&
                    is_non_fresh(v.m_key, non_fresh_vars))))
                continue;
            for (const auto& e : v.get_value())
                if (u.str.is_concat(e)){
                    ptr_vector<expr> nodes;
                    get_nodes_in_concat(e, nodes);
                    for (const auto& nn : nodes)
                        if (!u.str.is_string(nn)){
                            if (ret.contains(nn)){
                                if (!occurrenceLocation.contains(nn)) {
                                    ret[nn]++;
                                    if (ret[nn] >= 2){
                                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " var: " << mk_pp(nn, m) <<  " @ " << mk_pp(e, m) << std::endl;);
                                    }
                                }
                                else {
                                    // compare two equalities
                                    if (check_var_after_optimizing(e, occurrenceLocation[nn], nn)){
                                        ret[nn]++;
                                        if (ret[nn] >= 2){
                                            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " var: " << mk_pp(nn, m) <<  " @ " << mk_pp(occurrenceLocation[nn], m) << " and @ " << mk_pp(e, m) << std::endl;);
                                        }
                                    }
                                }

                            }

                            else {
                                ret.insert(nn, 1);
                                occurrenceLocation.insert(nn, e);
                            }
                        }
                }
        }
        return ret;
    }

    bool theory_trau::check_union_membership(expr *nn, int &len){
        for (const auto& we : membership_memo)
            if (we.first.get() == nn){
                if (u.re.is_star(we.second.get()) || u.re.is_star(we.second.get())) {
                    len = q_bound.get_int64();
                    return true;
                }
                else {
                    STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " " << mk_pp(we.second, m) << std::endl;);
                    expr_ref_vector components = collect_alternative_components(we.second);
                    STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " " << components.size() << std::endl;);
                    int max_len_tmp = 0;
                    if (components.size() > 0) {
                        for (const auto &s : components) {
                            STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " " << mk_pp(s, m) << std::endl;);
                            if(!u.re.is_to_re(s)) {
                                len = -1;
                                return true;
                            }
                            zstring value;
                            u.str.is_string(to_app(s)->get_arg(0), value);
                            max_len_tmp = std::max((int) value.length(), max_len_tmp);
                        }
                        len = max_len_tmp;
                        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " " << mk_pp(nn, m) << " len: " << len << std::endl;);
                        return true;
                    }
                }
            }
        return false;
    }

    bool theory_trau::belong_to_var_var_inequality(expr* nn){
        
        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " " << mk_pp(nn, m) << std::endl;);
        expr_ref_vector eqNodeSet(m);
        collect_eq_nodes(nn, eqNodeSet);
        for (const auto& we : m_wi_expr_memo){
            if (eqNodeSet.contains(we.first.get())){
                if (is_var_var_inequality(we.first.get(), we.second.get())){
                    return true;
                }
            }
            else if (eqNodeSet.contains(we.second.get())){
                if (is_var_var_inequality(we.first.get(), we.second.get())){
                    return true;
                }
            }
        }
        return false;
    }

    vector<zstring> theory_trau::collect_all_inequalities(expr* nn){
        clock_t t = clock();
        int diffLen = 0;
        vector<zstring> maxDiffStrs;
        expr_ref_vector eqs(m);
        collect_eq_nodes(nn, eqs);
        for (const auto& we : m_wi_expr_memo){
            if (eqs.contains(we.first.get())){
                bool eq_const;
                expr* const_value = get_eqc_value(we.second.get(), eq_const);
                if (eq_const) {
                    zstring value;
                    u.str.is_string(const_value, value);
                    STRACE("str", tout << __LINE__ << "\t " << mk_pp(we.first.get(), m) << " != \"" << value << "\"" << std::endl;);
                    if (!is_trivial_inequality(we.first.get(), value)) {
                        if (diffLen < (int) value.length()) {
                            diffLen = (int) value.length();
                            maxDiffStrs.clear();
                            maxDiffStrs.push_back(value);
                        } else if (diffLen == (int) value.length()) {
                            maxDiffStrs.push_back(value);
                        }
                    }
                }
                else if (is_var_var_inequality(we.first.get(), we.second.get())){
                    maxDiffStrs.clear();
                    maxDiffStrs.push_back("__var__");
                    return maxDiffStrs;
                }
            }
            else if (eqs.contains(we.second.get())){
                bool eq_const;
                expr* const_value = get_eqc_value(we.first.get(), eq_const);

                if (eq_const) {
                    zstring value;
                    u.str.is_string(const_value, value);
                    STRACE("str", tout << __LINE__ << "\t " << mk_pp(we.second.get(), m) << " != \"" << value << "\"" << std::endl;);
                    if (!is_trivial_inequality(we.second.get(), value)) {
                        if (diffLen < (int) value.length()) {
                            diffLen = (int) value.length();
                            maxDiffStrs.clear();
                            maxDiffStrs.push_back(value);
                        } else if (diffLen == (int) value.length()) {
                            maxDiffStrs.push_back(value);
                        }
                    }
                }
                else if (is_var_var_inequality(we.first.get(), we.second.get())){
                    maxDiffStrs.clear();
                    maxDiffStrs.push_back("__var__");
                    return maxDiffStrs;
                }
            }
        }
        STRACE("str", tout << __LINE__ <<  " time: " << __FUNCTION__ << ":  " << ((float)(clock() - t))/CLOCKS_PER_SEC << std::endl;);
        return maxDiffStrs;
    }

    bool theory_trau::is_var_var_inequality(expr* x, expr* y){
        expr_ref_vector eqx(m);
        expr* const_x = collect_eq_nodes(x, eqx);

        expr_ref_vector eqy(m);
        expr* const_y = collect_eq_nodes(y, eqy);

        if (const_x != nullptr || const_y != nullptr)
            return false;

        bool is_var_x = false;
        bool is_var_y = false;

        for (const auto& yy : eqy) {
            is_var_y = (!is_internal_var(yy)) || u.str.is_at(yy) || u.str.is_extract(yy) || u.str.is_replace(yy) || u.str.is_itos(yy);
            if (!is_var_y && !u.str.is_concat(yy)) {
                std::string tmp = expr2str(yy);
                is_var_y = (tmp.find("pre_prefix!") != std::string::npos) ||
                           (tmp.find("post_suffix!") != std::string::npos);
            }
            if (is_var_y)
                break;
        }

        if (is_var_y) {
            for (const auto& xx : eqx) {
                is_var_x = (!is_internal_var(xx)) || u.str.is_at(xx) || u.str.is_extract(xx) || u.str.is_replace(xx) || u.str.is_itos(xx);
                if (!is_var_x && !u.str.is_concat(xx)) {
                    std::string tmp = expr2str(xx);
                    is_var_x = (tmp.find("pre_prefix") != std::string::npos) ||
                               (tmp.find("post_suffix") != std::string::npos);
                }

                if (is_var_x)
                    break;
            }
        }

        if (is_var_x) {
            STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " " << mk_pp(x, m) << " != " << mk_pp(y, m)<< std::endl;);
            return true;
        }
        else
            return false;
    }

    expr* theory_trau::create_conjuct_all_inequalities(expr* nn){
        
        expr_ref_vector eqNodeSet(m);
        collect_eq_nodes(nn, eqNodeSet);
        expr_ref_vector ands(m);
        for (const auto& we : m_wi_expr_memo)
            if (eqNodeSet.contains(we.first.get()) || eqNodeSet.contains(we.second.get())){
                expr_ref tmp(mk_not(m, createEqualOP(we.first.get(), we.second.get())), m);
                ands.push_back(tmp.get());
            }
        return createAndOP(ands);
    }

    bool theory_trau::is_trivial_inequality(expr* n, zstring s){
        if (s.length() == 0)
            return true;

        for (unsigned i = 0; i < s.length(); ++i)
            if (sigma_domain.find(s[i]) == sigma_domain.end())
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

    bool theory_trau::collect_not_contains(expr* nn, expr_set const& ineq_vars, expr_set const& needles){
        if (ineq_vars.contains(nn))
            if (is_haystack(nn))
                return true;


        if (needles.contains(nn)) {
            bool has_const_eq = false;
            get_eqc_value(nn, has_const_eq);
            if (!has_const_eq) {
                if (is_needle(nn))
                    return true;
            }
        }
        return false;
    }

    bool theory_trau::is_haystack(expr* nn){
        for (const auto& we : m_wi_expr_memo){
            if (we.first.get() == nn){
                if (u.str.is_concat(we.second.get())){
                    expr* tmp = nullptr;
                    if (is_contain_equality(we.second.get(), tmp)){
                        zstring key;
                        if (u.str.is_string(tmp, key) && !is_trivial_contain(key)) {
                            expr* reg = nullptr;
                            if (is_internal_regex_var(nn, reg)) {
                                if (!match_regex(reg, key)){
                                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " does not match " << mk_pp(reg, m) << " " << key << std::endl;);
                                    continue;
                                }
                            }
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
                            expr* reg = nullptr;
                            if (is_internal_regex_var(nn, reg)) {
                                if (!match_regex(reg, key)){
                                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " does not match " << mk_pp(reg, m) << " " << key << std::endl;);
                                    continue;
                                }
                            }
                            return true;
                        }
                    }
                }
            }
        }
        return false;
    }

    bool theory_trau::is_needle(expr* nn){
        for (const auto& we : m_wi_expr_memo){
            if (u.str.is_concat(we.second.get())){
                expr* tmp = nullptr;
                if (is_contain_equality(we.second.get(), tmp)){
                    if (are_equal_exprs(tmp, nn))
                        return true;
                }
            }

            if (u.str.is_concat(we.first.get())){
                expr* tmp = nullptr;
                if (is_contain_equality(we.first.get(), tmp)){
                    if (are_equal_exprs(tmp, nn))
                        return true;
                }
            }
        }
        return false;
    }

    bool theory_trau::is_non_fresh_recheck(
            expr *nn,
            int len,
            obj_map<expr, ptr_vector<expr>> const& combinations){
        
        int diffLen = 0;
        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " " << mk_pp(nn, m) << " " << len << std::endl;);

        if (check_union_membership(nn, len))
            return true;

        vector<zstring> maxDiffStrs = collect_all_inequalities(nn);
        if (maxDiffStrs.size() > 0)
            diffLen = maxDiffStrs[0].length();

        if (diffLen > 0 && maxDiffStrs[0] == "__var__"){
            diffLen = -1;
        }

        if (diffLen > 0) {
            context& ctx = get_context();
            vector<zstring> constParts;
            int constPartLen = 0;
            if (combinations.contains(ctx.get_enode(nn)->get_root()->get_owner())) {
                for (const auto& concat : combinations[ctx.get_enode(nn)->get_root()->get_owner()]) {
                    ptr_vector<expr> nodeList;
                    get_nodes_in_concat(concat, nodeList);
                    zstring constPartTmp = "";
                    for (unsigned j = 0; j < nodeList.size(); ++j) {
                        zstring valueStr;
                        bool has_eqc_value = false;
                        expr *constValue = get_eqc_value(nodeList[j], has_eqc_value);
                        if (has_eqc_value) {
                            u.str.is_string(constValue, valueStr);
                            constPartTmp = constPartTmp + valueStr;
                        }
                    }

                    if ((int)constPartTmp.length() > constPartLen) {
                        constParts.clear();
                        constParts.push_back(constPartTmp);
                        constPartLen = (int)constPartTmp.length();
                        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << " " << mk_pp(nn, m) << " " << constPartTmp << std::endl;);
                    }
                    else if ((int)constPartTmp.length() == constPartLen) {
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
                                for (unsigned i = 0; i < childrenVector.size(); ++i)
                                    adds.push_back(mk_strlen(childrenVector[i]));
                                expr_ref tmp(createGreaterEqOP(createAddOP(adds), mk_int(constPartLen + 1)), m);
//                                expr* causes = create_conjuct_all_inequalities(nn);

//                                expr_ref tmpAssert(createEqualOP(causes, tmp), m);
//                                assert_axiom(tmpAssert.get());
//                                uState.add_asserting_constraints(tmpAssert);
                            }
                            else {
                                expr_ref tmp(createGreaterEqOP(mk_strlen(nn), mk_int(constPartLen + 1)), m);
//                                expr* causes = create_conjuct_all_inequalities(nn);

//                                expr_ref tmpAssert(createEqualOP(causes, tmp), m);
//                                assert_axiom(tmpAssert.get());
//                                uState.add_asserting_constraints(tmpAssert);
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



    void theory_trau::print_all_assignments(){
        
        context& ctx = get_context();
        (void) ctx;
        TRACE("str", tout << __FUNCTION__ << ": at level " << ctx.get_scope_level() << std::endl;);

        expr_ref_vector assignments(m);
        ctx.get_assignments(assignments);
        for (expr_ref_vector::iterator it = assignments.begin(); it != assignments.end(); ++it)
            STRACE("str", tout << "Assigned value " << mk_pp(*it, m) << std::endl;);
    }

    void theory_trau::print_guessed_literals(){
        
        context& ctx = get_context();
        (void) ctx;
        TRACE("str", tout << __FUNCTION__ << ": at level " << ctx.get_scope_level() << std::endl;);

        expr_ref_vector assignments(m);
        for (expr_ref_vector::iterator it = assignments.begin(); it != assignments.end(); ++it)
            STRACE("str", tout << "Assigned value " << mk_pp(*it, m) << std::endl;);
    }

    obj_map<expr, ptr_vector<expr>> theory_trau::normalize_eq(
            expr_ref_vector &subNodes,
            obj_map<expr, int> &non_fresh_vars,
            bool &axiom_added){
        clock_t t = clock();

        context& ctx = get_context();
        (void) ctx;
        TRACE("str", tout << __FUNCTION__ << ": at level " << ctx.get_scope_level() << std::endl;);
        obj_map<expr, ptr_vector<expr>> combinations;
        expr_ref_vector eqc_roots(m);
        sort* string_sort = u.str.mk_string_sort();
        for (ptr_vector<enode>::const_iterator it = ctx.begin_enodes(); it != ctx.end_enodes(); ++it) {
            expr* owner = (*it)->get_root()->get_owner();
            if ((m.get_sort(owner)) == string_sort && !eqc_roots.contains(owner)) {
                eqc_roots.push_back(owner);
            }
        }
        for (const auto& node : eqc_roots){
            if (!combinations.contains(node)){
                TRACE("str", tout << __FUNCTION__ << ":  " << mk_pp(node, m) << std::endl;);
                expr_ref_vector parents(m);
                extend_object(ctx.get_enode(node)->get_root()->get_owner(), combinations, subNodes, parents, non_fresh_vars);
            }
        }
        STRACE("str", tout << __LINE__ <<  " time: " << __FUNCTION__ << ":  " << ((float)(clock() - t))/CLOCKS_PER_SEC << std::endl;);

        if (!review_disequalities_not_contain(combinations)){
            print_eq_combination(combinations);
            negate_context();
            axiom_added = true;
            return combinations;
        }
        return refine_eq_combination(non_fresh_vars, combinations, subNodes);
    }

    obj_map<expr, ptr_vector<expr>> theory_trau::refine_eq_combination(
            obj_map<expr, int> &non_fresh_vars,
            obj_map<expr, ptr_vector<expr>> const& combinations,
            expr_ref_vector const& subNodes){

        TRACE("str", tout << __LINE__ << " " << __FUNCTION__ <<  std::endl;);
        obj_map<expr, ptr_vector<expr>> ret;
        expr* reg = nullptr;
        for (const auto& c : combinations){
            ptr_vector<expr> c_second = refine_eq_set(c.m_key, c.get_value(), non_fresh_vars);
            if (c_second.size() == 0 && !u.str.is_string(c.m_key))
                continue;
            bool important = is_non_fresh(c.m_key, non_fresh_vars);
            if (!important) {
                // the var is too complicated
                if (c_second.size() > 20) {
                    non_fresh_vars.insert(c.m_key, -1);
                    ret.insert(c.m_key, c_second);
                }
                else if (!subNodes.contains(c.m_key) || u.str.is_string(c.m_key) || is_internal_regex_var(c.m_key, reg)) {
                    if (u.str.is_concat(c.m_key)) {
                        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << ": root concat node  " << mk_pp(c.m_key, m) << std::endl;);
                        // check if it is an important concat
                        bool importantConcat = false;
                        ptr_vector<expr> nodes;
                        get_all_nodes_in_concat(c.m_key, nodes);
                        for (const auto& v : non_fresh_vars)
                            if (nodes.contains(v.m_key)) {
                                importantConcat = true;
                                STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << ": important  " << mk_pp(v.m_key, m) << std::endl;);
                                break;
                            }

                        if (importantConcat) {
                            ret.insert(c.m_key, c_second);
                        }
                        else {
                            STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << ": remove " << mk_pp(c.m_key, m) << " " << mk_pp(c.m_key, m) << std::endl;);
                            // remove c.first from the list
                            ptr_vector<expr> tmp;
                            for (const auto& cc : c_second)
                                if (cc != c.m_key && !tmp.contains(cc)){
                                    tmp.push_back(cc);
                                }

                            if (tmp.size() >= 1) {
                                ret.insert(c.m_key, tmp);
                            }
                        }
                    }
                    else {
                        STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << ": root var node  " << mk_pp(c.m_key, m) << std::endl;);
                        ret.insert(c.m_key, c_second);
                    }

                }
                else
                    STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << ": remove " << mk_pp(c.m_key, m) << std::endl;);
            }
            else {
                STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << ": important node  " << mk_pp(c.m_key, m) << std::endl;);
                if (!subNodes.contains(c.m_key))
                    STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << ": root node  " << mk_pp(c.m_key, m) << std::endl;);

                ret.insert(c.m_key, c_second);
            }
        }
        return ret;
    }

    bool theory_trau::can_merge_combination(obj_map<expr, ptr_vector<expr>> const& combinations){
        TRACE("str", tout << __LINE__ << " " << __FUNCTION__ <<  std::endl;);
        
        expr_ref_vector implies(m);
        obj_map<expr, ptr_vector<expr>> ret;
        for (const auto& c : combinations){
            bool found = false;
            if (c.get_value().size() >= 2) {
                for (const auto &cc : ret) {
                    if (cc.get_value().size() >= 2) {
                        // check if they are the same
                        for (const auto &n : c.get_value())
                            if (!are_equal_exprs(c.m_key, cc.m_key) && concat_in_set(n, cc.get_value())) {
                                implies.push_back(createEqualOP(c.m_key, cc.m_key));
                                found = true;
                                break;
                            }
                        if (found)
                            break;
                    }
                }
                if (!found){
                    ret.insert(c.m_key, c.get_value());
                }
            }
        }
        if (implies.size() > 0){
//            expr_ref_vector guessed_eqs(m), guessed_diseqs(m);
//            fetch_guessed_exprs_with_scopes(guessed_eqs, guessed_diseqs);
//            assert_axiom(rewrite_implication(createAndOP(guessed_eqs), createAndOP(implies)));
            assert_axiom(createAndOP(implies));
            implied_facts.push_back(createAndOP(implies));
            return true;
        }
        else
            return false;
    }

    bool theory_trau::concat_in_set(expr* n, ptr_vector<expr> const& s){
        if (s.contains(n))
            return true;
        for (const auto& nn : s){
            if (are_equal_concat(n, nn)){
                return true;
            }
        }

        return false;
    }

    bool theory_trau::is_important_concat(expr* e, obj_map<expr, int> const& non_fresh_vars){
        ptr_vector<expr> nodes;
        get_all_nodes_in_concat(e, nodes);
        for (const auto& v : non_fresh_vars)
            if (nodes.contains(v.m_key)) {
                STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << ": important  " << mk_pp(v.m_key, m) << std::endl;);
                return true;
            }
        return false;
    }

    /*
     * size = 0 or size = 1 && trivial equal
     */
    bool theory_trau::is_trivial_combination(expr* v, ptr_vector<expr> const& eq, obj_map<expr, int> const& non_fresh_vars){
        if (eq.size() == 0)
            return true;

        if (is_non_fresh(v, non_fresh_vars)) {
            if (eq.size() == 1) {
                // if it is equal to itself only
                expr_ref_vector eqs(m);
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

    ptr_vector<expr> theory_trau::refine_eq_set(
            expr* var,
            ptr_vector<expr> s,
            obj_map<expr, int> const& non_fresh_vars,
            expr_ref_vector const& notnon_fresh_vars){
        TRACE("str", tout << __LINE__ << " " << __FUNCTION__ <<  std::endl;);
        
        refine_all_duplications(s);
        ptr_vector<expr> ret;
        for (const auto& n : s) {
            if (u.str.is_concat(n)) {
                ptr_vector<expr> childrenVector;
                get_all_nodes_in_concat(n, childrenVector);

                bool notAdd = false;

                if (are_equal_exprs(var, n)) {
                    // do not have const or important var
                    bool found = false;
                    ptr_vector<expr> v;
                    get_nodes_in_concat(n, v);
                    for (const auto& nn : v)
                        if (u.str.is_string(nn) || is_non_fresh(nn, non_fresh_vars)){
                            found = true;
                            break;
                        }
                    if (found)
                        notAdd = false;
                    else
                        notAdd = true;
                }
                // check if it contains a nonimportantVar
                if (!notAdd) {
                    for (const auto &notimp : notnon_fresh_vars)
                        if (childrenVector.contains(notimp)) {
                            notAdd = true;
                            if (!appear_in_eqs(ret, notimp)) {
                                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": add " << mk_pp(n, m) << " because of " << mk_pp(notimp, m) << std::endl;);
                                notAdd = false;
                                break;
                            }
                        }
                }

                if (!notAdd && !ret.contains(n))
                    ret.push_back(n);
            }
            else if (is_non_fresh(n, non_fresh_vars)  || u.str.is_string(n)) {
                if (!ret.contains(n))
                    ret.push_back(n);
            }
        }

        if (ret.size() == 1 && !is_non_fresh(var, non_fresh_vars)) {
            // check if none of variable is really important
            ptr_vector<expr> v;
            get_all_nodes_in_concat(*ret.begin(), v);
            bool shouldKeep = false;
            for (const auto& nn : v) {
                int tmp;
                if (is_non_fresh(nn, non_fresh_vars, tmp) && tmp == -1){
                    if (u.str.is_string(var)){
                        shouldKeep = true;
                        break;
                    }
                }
            }

            if (!shouldKeep)
                ret.reset();
        }
        return ret;
    }

    ptr_vector<expr> theory_trau::refine_eq_set(
            expr* var,
            ptr_vector<expr> s,
            obj_map<expr, int> const& non_fresh_vars){
        refine_all_duplications(s);
        ptr_vector<expr> ret;
        for (const auto& n : s) {
            if (u.str.is_concat(n)) {
                bool notAdd = false;

                if (are_equal_exprs(var, n)) {
                    // do not have const or important var
                    bool found = false;
                    ptr_vector<expr> v;
                    get_nodes_in_concat(n, v);
                    for (const auto& nn : v)
                        if (u.str.is_string(nn) || is_non_fresh(nn, non_fresh_vars)){
                            found = true;
                            break;
                        }
                    if (found)
                        notAdd = false;
                    else
                        notAdd = true;
                }

                if (!notAdd)
                    ret.push_back(n);
            }
            else if (is_non_fresh(n, non_fresh_vars)  || u.str.is_string(n)) {
                if (!ret.contains(n))
                    ret.push_back(n);
            }
        }

        if (ret.size() == 1 && !is_non_fresh(var, non_fresh_vars)) {
            // check if none of variable is really important
            ptr_vector<expr> v;
            get_all_nodes_in_concat(*ret.begin(), v);
            bool shouldKeep = false;
            for (const auto& nn : v) {
                int tmp;
                if (is_non_fresh(nn, non_fresh_vars, tmp) && tmp == -1){
                    if (u.str.is_string(var)){
                        shouldKeep = true;
                        break;
                    }
                }
            }

            if (!shouldKeep)
                ret.reset();
        }
        return ret;
    }

    void theory_trau::refine_all_duplications(ptr_vector<expr> &s) {
        if (s.size() == 1)
            return;
        ptr_vector<expr> v = s;
        int_set to_remove;
        s.reset();
        for (unsigned i = 0; i < v.size(); ++i)
            if (to_remove.find(i) == to_remove.end()) {
                bool eq = false;
                unsigned j = i + 1;
                for (j = i + 1; j < v.size(); ++j)
                    if (are_equal_concat(v[i], v[j])) {
                        STRACE("str",
                               tout << __LINE__ << " " << __FUNCTION__ << ": remove " << mk_pp(v[i], m)
                                    << " " << mk_pp(v[j], m) << std::endl;);
                        to_remove.insert(j);
                        eq = true;
                    }

                if (!eq)
                    s.push_back(v[i]);
                else {
                    ptr_vector <expr> nodes;
                    get_nodes_in_concat(v[i], nodes);
                    ptr_vector <expr> new_nodes;
                    for (const auto& n : nodes) {
                        bool has_value;
                        new_nodes.push_back(get_eqc_value(n, has_value));
                    }
                    s.push_back(create_concat_from_vector(new_nodes));
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": remove " << mk_pp(v[i], m) << std::endl;);
                }
            }
    }

    bool theory_trau::are_equal_concat(expr* lhs, expr* rhs){
        ptr_vector<expr> vLhs;
        get_nodes_in_concat(lhs, vLhs);

        ptr_vector<expr> vRhs;
        get_nodes_in_concat(rhs, vRhs);

        if (vLhs.size() == vRhs.size()) {
            for (unsigned i = 0; i < vLhs.size(); ++i)
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
    bool theory_trau::appear_in_eqs(ptr_vector<expr> const& s, expr* var){
        for (const auto& eq : s)
            if (u.str.is_concat(eq)) {
                ptr_vector<expr> nodes;
                get_all_nodes_in_concat(eq, nodes);
                if (nodes.contains(var))
                    return true;
            }
        return false;
    }

    ptr_vector<expr> theory_trau::refine_eq_set(
            ptr_vector<expr> const& s,
            obj_map<expr, int> const& non_fresh_vars){
        TRACE("str", tout << __LINE__ << " " << __FUNCTION__ <<  std::endl;);

        ptr_vector<expr> ret;
        expr *arg0 = nullptr;
        expr *arg1 = nullptr;
        for (const auto& n : s) {
            if (u.str.is_concat(n, arg0, arg1)) {
                expr_ref_vector eq0(m);
                collect_eq_nodes(arg0, eq0);
                bool imp0 = is_non_fresh(arg0, non_fresh_vars);

                expr_ref_vector eq1(m);
                collect_eq_nodes(arg1, eq1);
                bool imp1 = is_non_fresh(arg1, non_fresh_vars);
                STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << ": checking " << mk_pp(arg0, m) << " " << mk_pp(arg1, m) << std::endl;);
                bool notAdd = false;
                if (!imp0 && !u.str.is_concat(arg0) && !u.str.is_string(arg0)) {
                    expr *arg00 = nullptr;
                    expr *arg01 = nullptr;
                    for (expr_ref_vector::iterator i = s.begin(); i != s.end(); ++i) {
                        if (u.str.is_concat(*i, arg00, arg01) && (*i) != (n)) {
                            if (arg1 == arg01 && eq0.contains(arg00)) {
                                STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << ": eq with " << mk_pp(arg0, m) << " " << mk_pp(arg00, m) << std::endl;);
                                notAdd = true;
                                break;
                            }
                        }
                    }
                }

                if (!imp1 && !u.str.is_concat(arg1) && !u.str.is_string(arg1)){
                    expr *arg00 = nullptr;
                    expr *arg01 = nullptr;
                    for (expr_ref_vector::iterator i = s.begin(); i != s.end(); ++i) {
                        if (u.str.is_concat(*i, arg00, arg01) && (*i) != (n)) {
                            if (arg0 == arg00 && eq1.contains(arg01)) {
                                STRACE("str", tout << __LINE__ <<  " " << __FUNCTION__ << ": eq with " << mk_pp(arg1, m) << " " << mk_pp(arg01, m) << std::endl;);
                                notAdd = true;
                                break;
                            }
                        }
                    }
                }

                if (notAdd == false && !ret.contains(n))
                    ret.push_back(n);
            }
        }
        return ret;
    }

    bool theory_trau::is_non_fresh(expr *n, obj_map<expr, int> const &non_fresh_vars) {
        return non_fresh_vars.contains(n);
    }

    bool theory_trau::is_non_fresh(expr *n, obj_map<expr, int> const &non_fresh_vars, int &l) {
        if (non_fresh_vars.contains(n)){
            l = non_fresh_vars[n];
            return true;
        }
        else
            return false;
    }

    ptr_vector<expr> theory_trau::extend_object(
            expr* object,
            obj_map<expr, ptr_vector<expr>> &combinations,
            expr_ref_vector &subNodes,
            expr_ref_vector const& parents,
            obj_map<expr, int> const& non_fresh_vars){
        expr_ref_vector eqNodeSet(m);
        expr* constValue = collect_eq_nodes(object, eqNodeSet);

        for (const auto& o : eqNodeSet)
            if (combinations.contains(o))
                return combinations[o];

        if (parents.size() > 0) {
            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << std::endl;);
            for (const auto &p : parents)
                STRACE("str", tout << " \t--> " << mk_pp(p, m) ;);
            STRACE("str", tout << std::endl;);
        }
        context& ctx = get_context();
        TRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": " << mk_pp(object, m) << std::endl;);

        ptr_vector<expr> result = {};
        object = ctx.get_enode(object)->get_root()->get_owner();


        if (constValue != nullptr) {
            result.push_back(constValue);

            if (object != constValue) {
                expr_ref tmp(ctx.mk_eq_atom(object, constValue), m);
                ctx.internalize(tmp, false);
                object = constValue;
            }
        }

        obj_hashtable<expr> eqConcat;
        // refine concat: a . b = c . d && a = c && b = d
        expr_ref_vector refined_eqNodeSet(m);
        expr *arg0 = nullptr;
        expr *arg1 = nullptr;
        for (expr_ref_vector::iterator it = eqNodeSet.begin(); it != eqNodeSet.end(); ++it) {
            if (u.str.is_concat(*it, arg0, arg1) && *it != object) {
                // get lhs
                expr_ref_vector eqLhsSet(m);
                collect_eq_nodes(arg0, eqLhsSet);

                expr_ref_vector eqRhsSet(m);
                collect_eq_nodes(arg1, eqRhsSet);

                bool found = false;
                for (expr_ref_vector::iterator itor = refined_eqNodeSet.begin(); itor != refined_eqNodeSet.end(); ++itor) {
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
            if (u.str.is_concat(*it, arg0, arg1)) {
                add_subnodes(arg0, arg1, subNodes);

                STRACE("str", tout << __LINE__ << " " << mk_pp(arg0, m) << " . " << mk_pp(arg1, m) << std::endl;);
                ptr_vector<expr> eqLhs;
                if (!parents.contains(arg0)) {
                    expr_ref_vector lhsParents(m);
                    lhsParents.append(parents);
                    lhsParents.push_back(arg0);
                    eqLhs.append(extend_object(arg0, combinations, subNodes, lhsParents, non_fresh_vars));
                }
                else {
                    eqLhs.push_back(arg0);
                }

                // get rhs
                ptr_vector<expr> eqRhs;
                if (!parents.contains(arg1)) {
                    expr_ref_vector rhsParents(m);
                    rhsParents.append(parents);
                    rhsParents.push_back(arg1);
                    eqRhs.append(extend_object(arg1, combinations, subNodes, rhsParents, non_fresh_vars));
                }
                else {
                    eqRhs.push_back(arg1);
                }

                if (is_non_fresh(arg1, non_fresh_vars) && !has_empty_vars(arg1)) {
                    eqRhs.reset();
                    eqRhs.push_back(arg1);
                }

                if (is_non_fresh(arg0, non_fresh_vars) && !has_empty_vars(arg0)) {
                    eqLhs.reset();
                    eqLhs.push_back({arg0});
                }

                // to prevent the exponential growth
                if (eqLhs.size() > 20){
                    eqLhs.reset();
                    eqLhs.push_back(find_equivalent_variable(arg0));
                    STRACE("str", tout << __LINE__ << " too many eq combinations " << mk_pp(arg0, m) << std::endl;);
                }

                if (eqRhs.size() > 20){
                    eqRhs.reset();
                    eqRhs.push_back(find_equivalent_variable(arg1));
                    STRACE("str", tout << __LINE__ << " too many eq combinations " << mk_pp(arg1, m) << std::endl;);
                }
                for (const auto &l : eqLhs)
                    for (const auto &r : eqRhs) {
                        zstring val_lhs, val_rhs;
                        bool hasLhSValue = false, hasRhSValue = false;
                        expr* valueLhs = get_eqc_value(l, hasLhSValue);
                        expr* valueRhs = get_eqc_value(r, hasRhSValue);

                        if (hasLhSValue) {
                            u.str.is_string(valueLhs, val_lhs);
                        }
                        if (hasRhSValue) {
                            u.str.is_string(valueRhs, val_rhs);
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
                       for (unsigned i = 0; i < childrenVector.size(); ++i)
                           tout << mk_pp(childrenVector[i], m)  << " ";
                       tout << std::endl;
                   });

        // continuing refining
        for (const auto& nn : eqConcat)
            if (((!u.str.is_extract(nn)) &&
                 (!u.str.is_at(nn)) &&
                 (!u.str.is_replace(nn)) &&
                 (!u.str.is_itos(nn)) &&
                 (!u.str.is_nth_i(nn)) &&
                 (!u.str.is_nth_u(nn))) ||
                 u.str.is_concat(nn))
            {
                if (has_empty_vars(nn))
                    continue;
                STRACE("str", tout << __LINE__ << mk_pp(object, m) << " = " << mk_pp(nn, m) << std::endl;);
                expr_ref_vector tmp(m);
                get_const_regex_str_asts_in_node(nn, tmp);
                if (tmp.size() != 0 && !concat_in_set(nn, result)) {
                    if (!concat_in_set(nn, result))
                        result.push_back(nn);
                }
                else {
                    get_important_asts_in_node(nn, non_fresh_vars, tmp, true);
                    if (tmp.size() != 0 && !concat_in_set(nn, result)) {
                        if (!concat_in_set(nn, result))
                            result.push_back(nn);
                    }
                }
            }

        if (result.size() == 0) {
            expr* simp_concat = simplify_concat(object);
            if (!result.contains(simp_concat)) {
                result.push_back(simp_concat);
            }
        }
        else {
            // important var, it = itself, size = 1, it is root --> add another option if it is possible
            if ( result.size() == 1 &&
                    is_non_fresh(object, non_fresh_vars) &&
                    object == *result.begin() &&
                    u.str.is_concat(object)
                ){
                for (const auto& nn : eqNodeSet)
                    if (!u.str.is_concat(nn) && to_app(nn)->get_num_args() < 2) {
                        if (!concat_in_set(nn, result))
                            result.push_back(nn);
                    }
            }
        }

        combinations.insert(object, result);

        for (const auto& e: result)
            STRACE("str",
                   if (!u.str.is_concat(e))
                       tout << "\t\t" << mk_pp(e, m) << std::endl;
                   else {
                       ptr_vector<expr> childrenVector;
                       get_nodes_in_concat(e, childrenVector);
                       tout << "\t\t";
                       for (unsigned i = 0; i < childrenVector.size(); ++i)
                           tout << mk_pp(childrenVector[i], m)  << " ";
                       tout << std::endl;
                   });
        return result;
    }

    expr* theory_trau::create_concat_with_concat(expr* n1, expr* n2){
        ptr_vector <expr> tmp0;
        get_nodes_in_concat(n1, tmp0);
        ptr_vector <expr> tmp1;
        get_nodes_in_concat(n2, tmp1);
        zstring v1, v2;
        if (u.str.is_string(tmp0[tmp0.size() - 1], v1) && u.str.is_string(tmp1[0], v2)){
            tmp0.pop_back();
            tmp1.erase(tmp1.begin());
            tmp0.push_back(u.str.mk_string(v1 + v2));
        }
        tmp0.append(tmp1);
        return create_concat_from_vector(tmp0);
    }

    expr* theory_trau::create_concat_with_str(expr* n, zstring str){
        expr* ends = ends_with_str(n);
        if (ends != nullptr){
            ptr_vector<expr> l;
            get_nodes_in_concat(n, l);
            zstring v;
            u.str.is_string(ends, v);
            v = v + str;
            ends = u.str.mk_string(v);
            for (int i = (int)l.size() - 2; i >= 0; --i){
                ends = mk_concat(l[i], ends);
            }
            return ends;
        }
        else
            return mk_concat(n, u.str.mk_string(str));
    }

    expr* theory_trau::create_concat_with_str(zstring str, expr* n){
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
                tmp = mk_concat(l[i], tmp);
            }
            return mk_concat(starts, tmp);
        }
        else
            return mk_concat(u.str.mk_string(str), n);
    }

    expr* theory_trau::ends_with_str(expr* n){
        if (u.str.is_concat(n)){
            ptr_vector<expr> l;
            get_nodes_in_concat(n, l);
            if (u.str.is_string(l[l.size() - 1]))
                return l[l.size() - 1];
        }
        return nullptr;
    }

    expr* theory_trau::starts_with_str(expr* n){
        if (u.str.is_concat(n)){
            ptr_vector<expr> l;
            get_nodes_in_concat(n, l);
            if (u.str.is_string(l[0]))
                return l[0];
        }
        return nullptr;
    }

    void theory_trau::add_subnodes(expr* concatL, expr* concatR, expr_ref_vector &subNodes){
        rational vLen;
        if (get_len_value(concatL, vLen)) {
            if (vLen.get_int64() == 0)
                return;
        }

        if (get_len_value(concatR, vLen)) {
            if (vLen.get_int64() == 0)
                return;
        }

        subNodes.push_back(concatL);
        subNodes.push_back(concatR);
    }

    bool theory_trau::can_propagate() {
        return !m_basicstr_axiom_todo.empty() || !m_str_eq_todo.empty()
               || !m_concat_axiom_todo.empty() || !m_concat_eval_todo.empty()
               || !m_library_aware_axiom_todo.empty()
               || !m_delayed_axiom_setup_terms.empty()
               || !m_persisted_axiom_todo.empty()
               || (search_started && !m_delayed_assertions_todo.empty())
                ;
    }

    void theory_trau::propagate() {
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " @lvl " << m_scope_level <<  std::endl;);

        assert_cached_eq_state();

        if (uState.reassertEQ)
            assert_cached_diseq_state();

        context & ctx = get_context();
        while (can_propagate() && !ctx.inconsistent()) {
            while(!ctx.inconsistent()) {
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
            m_str_eq_todo.reset();

            for (auto const& el : m_concat_axiom_todo) {
                instantiate_concat_axiom(el);
            }
            m_concat_axiom_todo.reset();
            m_concat_eval_todo.reset();

            while(!ctx.inconsistent()) {
                // Special handling: terms can recursively set up other terms
                // (e.g. indexof can instantiate other indexof terms).
                // - Copy the list so it can potentially be modified during setup.
                // - Don't clear this list if new ones are added in the process;
                //   instead, set up all the new terms before proceeding.
                // TODO see if any other propagate() worklists need this kind of handling
                // TODO we really only need to check the new ones on each pass
                unsigned start_count = m_library_aware_axiom_todo.size();
                STRACE("str", tout << __LINE__ << " m_library_aware_axiom_todo: size " << start_count << std::endl;);
                obj_hashtable<enode> axioms_tmp = m_library_aware_axiom_todo;
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
                        STRACE("str", tout << "BUG: unhandled library-aware term " << mk_pp(e->get_owner(), m) << std::endl;);
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
    void theory_trau::instantiate_basic_string_axioms(enode * str) {
        context & ctx = get_context();
        

        {
            sort * a_sort = m.get_sort(str->get_owner());
            sort * str_sort = u.str.mk_string_sort();
            if (a_sort != str_sort) {
                STRACE("str", tout << "WARNING: not setting up string axioms on non-string term " << mk_pp(str->get_owner(), m) << std::endl;);
                return;
            }
        }

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
                // build RHS
                expr_ref zero(m);
                zero = m_autil.mk_numeral(rational(0), true);
                // build LHS >= RHS and assert
                app * lhs_ge_rhs = m_autil.mk_ge(len_str, zero);
                m_delayed_assertions_todo.push_back(lhs_ge_rhs);
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
                m_delayed_assertions_todo.push_back(createEqualOP(lhs, rhs));
            }

        }
    }


    /*
     * Instantiate an axiom of the following form:
     * Length(Concat(x, y)) = Length(x) + Length(y)
     */
    void theory_trau::instantiate_concat_axiom(enode * cat) {
        app * a_cat = cat->get_owner();
        SASSERT(u.str.is_concat(a_cat));

        

        // build LHS
        expr_ref len_xy(m);
        len_xy = mk_strlen(a_cat);

        // build RHS: start by extracting x and y from Concat(x, y)
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
//        assert_implication(m.mk_eq(len_x, mk_int(0)), createEqualOP(a_cat, a_y));
//
//        // len_y = 0 --> Concat(x, y) = x
//        assert_implication(m.mk_eq(len_y, mk_int(0)), createEqualOP(a_cat, a_x));
    }

    void theory_trau::instantiate_axiom_prefixof(enode * e) {
        context & ctx = get_context();
        

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
        expr_ref sub(m_autil.mk_sub(mk_strlen(expr->get_arg(1)), mk_strlen(expr->get_arg(0))), m);
        m_rewrite(sub);
        expr_ref topLevelCond(m_autil.mk_ge(sub, mk_int(0)), m);

        expr_ref finalAxiom(m.mk_ite(topLevelCond, then1, mk_not(m, expr)), m);
        assert_axiom(finalAxiom);
    }

    void theory_trau::instantiate_axiom_suffixof(enode * e) {
        context & ctx = get_context();
        

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
        expr_ref sub(m_autil.mk_sub(mk_strlen(expr->get_arg(1)), mk_strlen(expr->get_arg(0))), m);
        m_rewrite(sub);
        expr_ref topLevelCond(m_autil.mk_ge(sub, mk_int(0)), m);

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
    void theory_trau::instantiate_axiom_contains(enode * e) {
        context & ctx = get_context();
        

        app * ex = e->get_owner();
        if (axiomatized_terms.contains(ex)) {
            return;
        }
        axiomatized_terms.insert(ex);

        if (can_solve_contain_family(e))
            return;

        // quick path, because this is necessary due to rewriter behaviour
        // at minimum it should fix z3str/concat-006.smt2
        zstring haystackStr, needleStr;
        expr *arg0 = nullptr, *arg1 = nullptr, *arg2 = nullptr;
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
                for (unsigned i = 0; i < childrenVector.size(); ++i) {
                    zstring value;
                    if (u.str.is_string(childrenVector[i], value))
                        if (value.contains(needleStr)) {
                            assert_axiom(ex);
                            return;
                        }
                }
            }
            else if (u.str.is_extract(ex->get_arg(0), arg0, arg1, arg2)){
                // (str.contains (str.substr value1 0 (+ 1 (str.indexof value1 "J" 0))) "J")
                expr* arg2_arg0 = nullptr, *arg2_arg1 = nullptr, *arg2_arg2 = nullptr;
                // check the 2nd arg:
                if (u.str.is_index(arg1, arg2_arg0, arg2_arg1)){
                    // same var, same keyword
                    if (arg2_arg0 == arg0 && arg2_arg1 == ex->get_arg(1)){
                        // 3rd arg = 0 || contain = true
                        expr* e1 = createEqualOP(arg2, mk_int(0));
                        if (needleStr.length() > 0)
                            assert_implication(e1, mk_not(m, ex));
                        else
                            assert_axiom(ex);

                        expr* e2 = createGreaterEqOP(arg2, mk_int(1));
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
                    for (unsigned i = 0; i < arg2app->get_num_args(); ++i) {
                        if (u.str.is_index(arg2app->get_arg(i), arg2_arg0, arg2_arg1, arg2_arg2)){
                            indexOfApp = to_app(arg2app->get_arg(i));
                            STRACE("str", tout << __LINE__ << " " << mk_pp(arg2app->get_arg(i), m) << std::endl;);
                            if (arg2_arg0 == arg0){
                                zstring indexOfStr;
                                if (u.str.is_string(arg2_arg1, indexOfStr) && indexOfStr == needleStr) {
                                    if (arg2_arg2 == arg1){
                                        found_indexof = true;
                                    }
                                }
                            }
                            STRACE("str", tout << __LINE__ << " " << mk_pp(arg2app->get_arg(i), m) << std::endl;);
                        }
                        else {
                            rational val;
                            if (m_autil.is_numeral(arg2app->get_arg(i), val)) {
                                sum = sum + val.get_int64();
                            }
                            else if (m_autil.is_mul(arg2app->get_arg(i))) {
                                app* tmp = to_app(arg2app->get_arg(i));
                                int mul = 1;
                                for (unsigned j = 0; j < tmp->get_num_parameters(); ++j)
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
                        expr* e1 = createGreaterEqOP(indexOfApp, mk_int(0));
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
            std::pair<expr*, expr*> key = std::make_pair(str, substr);
            contain_pair_bool_map.insert(str, substr, ex);
            if (!contain_pair_idx_map.contains(str)) {
                contain_pair_idx_map.insert(str, str::expr_pair_set());
            }
            if (!contain_pair_idx_map.contains(substr)) {
                contain_pair_idx_map.insert(substr, str::expr_pair_set());
            }
            contain_pair_idx_map[str].insert(key);
            contain_pair_idx_map[substr].insert(key);
        }

        std::pair<app*, app*> value = std::make_pair<app*, app*>(mk_str_var("pre_contain"), mk_str_var("post_contain"));
        expr_ref haystack(ex->get_arg(0), m), needle(ex->get_arg(1), m);

        app* a = mk_contains(haystack, needle);
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
                    assert_axiom(createEqualOP(value.first, contain_split_map[keynode].first->get_owner()));
                }
            }
        }

        for (const auto& p : contain_pair_bool_map){
            if (u.str.is_extract(p.get_key1()) && p.get_key2() == needle.get()){
                app* substr = to_app(p.get_key1());
                rational ra;
                if (substr->get_arg(0) == haystack.get() &&
                    m_autil.is_numeral(substr->get_arg(1), ra) && ra.get_int64() == 0){
                    app *rootContain = mk_contains(p.get_key1(), needle.get());
                    enode* keynode = ensure_enode(rootContain);
                    SASSERT(contain_split_map.contains(keynode));
                    assert_axiom(createEqualOP(value.first, contain_split_map[keynode].first->get_owner()));
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
    void theory_trau::instantiate_axiom_charAt(enode * e) {
        context &ctx = get_context();
        
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
     * arg1 == 0 && 0 <= arg2 <= len arg0 --> return arg2
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
    void theory_trau::instantiate_axiom_indexof(enode * e) {
        context & ctx = get_context();
        

        app * ex = e->get_owner();
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

        if (can_solve_contain_family(e))
            return;

        TRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ":" << mk_pp(ex, m) << std::endl;);
        std::pair<app*, app*> value;
        expr_ref haystack(ex->get_arg(0), m), needle(ex->get_arg(1), m);
        app* a = mk_contains(haystack, needle);
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
                    assert_axiom(createEqualOP(value.first, contain_split_map[keynode].first->get_owner()));
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
                    app *rootContain = mk_contains(p.get_key1(), needle.get());
                    enode* keynode = ensure_enode(rootContain);
                    SASSERT(contain_split_map.contains(keynode));
                    assert_axiom(createEqualOP(value.first, contain_split_map[keynode].first->get_owner()));
                }
            }
        }

        expr_ref x1(value.first, m);
        expr_ref x2(value.second, m);
        expr_ref indexAst(mk_int_var("index"), m);

        expr_ref condAst(mk_contains(ex->get_arg(0), ex->get_arg(1)), m);
        SASSERT(condAst);

        if (index_tail.contains(ex)) {
            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " update index tail vs substring " << mk_pp(index_tail[ex].first, m) << std::endl;);
            assert_axiom(createEqualOP(x2.get(), index_tail[ex].second));
            expr* x1_arg1 = mk_concat(x1.get(), ex->get_arg(1));
            assert_axiom(createEqualOP(index_tail[ex].first, x1_arg1));
            length_relation.insert(std::make_pair(index_tail[ex].first, x1.get()));
            length_relation.insert(std::make_pair(index_tail[ex].first, ex->get_arg(1)));
        }
        else {
            index_tail.insert(ex, std::make_pair(mk_concat(x1.get(), ex->get_arg(1)), x2.get()));
        }

        if (index_head.contains(ex)) {
            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " update index head vs substring " << mk_pp(index_head[ex], m) << std::endl;);
            assert_axiom(createEqualOP(x1.get(), index_head[ex]));
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

        // expr->get_arg(1) == 0 --> x1 = ""
        if (!u.str.is_string(ex->get_arg(1))){
            thenItems.push_back(rewrite_implication(createEqualOP(mk_strlen(ex->get_arg(1)), mk_int(0)),
                                                    createEqualOP(mk_strlen(x1), mk_int(0))));
        }

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
            expr_ref curr_premise01(m_autil.mk_ge(mk_strlen(ex->get_arg(1)), mk_int(1)), m);
            expr_ref curr_premise02(m_autil.mk_ge(indexAst, mk_int(1)), m);
            expr_ref_vector curr_ands(m);
            curr_ands.push_back(curr_premise01);
            curr_ands.push_back(curr_premise02);

            expr_ref x3(mk_str_var("x3"), m);
            expr_ref x4(mk_str_var("x4"), m);
            expr_ref tmpLen(m_autil.mk_add(indexAst, mk_strlen(ex->get_arg(1)), mk_int(-1)), m);
            SASSERT(tmpLen);
            expr_ref_vector curr_conclusion(m);

            curr_conclusion.push_back(ctx.mk_eq_atom(ex->get_arg(0), mk_concat(x3, x4)));
            curr_conclusion.push_back(ctx.mk_eq_atom(mk_strlen(x3), tmpLen));
            curr_conclusion.push_back(mk_not(m, mk_contains(x3, ex->get_arg(1))));
            thenItems.push_back(rewrite_implication(createAndOP(curr_ands), createAndOP(curr_conclusion)));
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

        // | arg1 | = 0 --> indexOf = hd
        assert_implication(ctx.mk_eq_atom(mk_strlen(ex->get_arg(1)), mk_int(0)), ctx.mk_eq_atom(indexAst, mk_int(0)));

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
    void theory_trau::instantiate_axiom_indexof_extended(enode * _e) {
        context & ctx = get_context();
        

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

        {
            // arg1 == arg0 && arg2 == 0 --> e = 0
            expr_ref_vector ands(m);
            ands.push_back(createEqualOP(arg0, arg1));
            ands.push_back(createEqualOP(startIndex, mk_int(0)));
            assert_axiom(rewrite_implication(createAndOP(ands), createEqualOP(e, mk_int(0))));
        }
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


        // case 3: startIndex > len(H), return -1
        {
            //th_rewriter rw(m);
            //rw(premise);
            expr_ref premise(m_autil.mk_ge(m_autil.mk_add(startIndex, m_autil.mk_mul(minus_one, mk_strlen(arg0))), mk_int(1)), m);
            if (premise != m.mk_false()) {
                expr_ref conclusion(ctx.mk_eq_atom(e, minus_one), m);
                assert_implication(premise, conclusion);
            }
        }

        // case 4: 0 <= i < len(H),
        //      arg0 = hd . tl
        //      hd.len = startIndex
        //      tlindex = indexOf(tl, arg1, 0)
        //      if tlindex >= 0, then
        //          indexOf = tlindex + |hd|,
        //      else indexOf = -1
        {
            expr_ref premise1(m_autil.mk_ge(startIndex, zero), m);
            expr_ref premise2(m.mk_not(m_autil.mk_gt(m_autil.mk_add(startIndex, m_autil.mk_mul(minus_one, mk_strlen(arg0))), zero)), m);
            expr_ref _premise(m.mk_and(premise1, premise2), m);
            expr_ref premise(_premise);
            th_rewriter rw(m);
            rw(premise);

            expr_ref_vector conclusion_terms(m);
            conclusion_terms.push_back(ctx.mk_eq_atom(arg0, mk_concat(hd, tl)));
            conclusion_terms.push_back(ctx.mk_eq_atom(mk_strlen(hd), startIndex));

            // if tlindex >= 0 --> indexOf = tlindex + hd.len, else indexOf = -1
            expr* tlIndexOf = mk_indexof(tl, arg1);
            conclusion_terms.push_back(createITEOP(
                    createGreaterEqOP(tlIndexOf, mk_int(0)),
                    ctx.mk_eq_atom(e, createAddOP(tlIndexOf, mk_strlen(hd))),
                    ctx.mk_eq_atom(e, mk_int(-1))));

            expr_ref conclusion(mk_and(conclusion_terms), m);
            assert_implication(premise, conclusion);

            // | arg1 | = 0 --> indexOf = hd
            assert_implication(premise, rewrite_implication(ctx.mk_eq_atom(mk_strlen(arg1), mk_int(0)), ctx.mk_eq_atom(e, mk_strlen(hd))));
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
            expr_ref_vector conclusion(m);
            if (m_autil.is_numeral(startIndex))
                conclusion.push_back(m_autil.mk_ge(e, startIndex));
            else
                return;
            expr_ref containsAxiom(ctx.mk_eq_atom(premise, createAddOP(conclusion)), m);
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
    void theory_trau::instantiate_axiom_substr(enode * e) {
        context & ctx = get_context();
        
        expr* base = nullptr;
        expr* pos = nullptr;
        expr* len = nullptr;
        app * expr = e->get_owner();

        if (axiomatized_terms.contains(expr)) {
            return;
        }
        axiomatized_terms.insert(expr);

        TRACE("str", tout << __FUNCTION__ << ":" << mk_pp(expr, m) << std::endl;);

        VERIFY(u.str.is_extract(expr, base, pos, len));

        expr_ref zero(m_autil.mk_numeral(rational::zero(), true), m);
        expr_ref minusOne(m_autil.mk_numeral(rational::minus_one(), true), m);

        // quick path
        if (pos == mk_strlen(base)) {
            m_delayed_assertions_todo.push_back(createEqualOP(expr, mk_string("")));
            return;
        }
        else {
            rational len_ral;
            if (get_arith_value(len, len_ral) && len_ral.get_int64() == 1) {
                expr_ref at(mk_at(base, pos), m);
                m_delayed_assertions_todo.push_back(createEqualOP(expr, at));
                instantiate_axiom_charAt(ctx.get_enode(at.get()));
                return;
            }
        }

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
        expr_ref sub(m_autil.mk_sub(m_autil.mk_add(pos, len), mk_strlen(base)), m);
        m_rewrite(sub);

        expr_ref lenOutOfBounds(m_autil.mk_ge(sub, zero), m);
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
        premise_expr = createAndOP(premises);
        expr_ref case2(m.mk_implies(premise_expr, case2_conclusion), m);

        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ":" << mk_pp(expr, m) << std::endl;);
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
            m_delayed_assertions_todo.push_back(case1_rw);

            expr_ref case2_rw(case2, m);
            rw(case2_rw);
            assert_axiom(case2_rw);

            expr_ref case3_rw(case3, m);
            rw(case3_rw);
            assert_axiom(case3_rw);
        }
    }

    void theory_trau::sync_index_head(expr* pos, expr* base, expr* first_part, expr* second_part){
        context & ctx = get_context();
        
        STRACE("str",
               tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(pos, m) << " = " << mk_pp(first_part, m) << std::endl;);
        if (u.str.is_index(to_app(pos))){
            if (to_app(pos)->get_arg(0) == base){
                // index >= 0 --> substr0 == head of index
                if (index_head.contains(pos)) {
                    assert_axiom(ctx.mk_eq_atom(first_part, index_head[pos]));
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " update index head vs substring " << mk_pp(first_part, m) << " = " << mk_pp(index_head[pos], m) << std::endl;);
                }
                else {
                    index_head.insert(pos, first_part);
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " update index head vs substring " << mk_pp(first_part, m) << " = " << mk_pp(index_head[pos], m) << std::endl;);
                }
            }
        }
        else {
            expr* arg0 = nullptr;
            expr* arg1 = nullptr;
            if (m_autil.is_add(pos, arg0, arg1)){
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(pos, m) << " = " << mk_pp(first_part, m) << std::endl;);
                if (u.str.is_index(to_app(arg0))){
                    zstring value;
                    if (u.str.is_string(to_app(arg0)->get_arg(1), value)){
                        if (arg1 == mk_int(value.length())){
                            if (index_tail.contains(arg0)) {
                                if (second_part != index_tail[arg0].second)
                                    assert_axiom(ctx.mk_eq_atom(second_part, index_tail[arg0].second));
                                if (first_part != index_tail[arg0].first)
                                    assert_axiom(ctx.mk_eq_atom(first_part, index_tail[arg0].first));

                                expr* concat_0 = nullptr;
                                expr* concat_1 = nullptr;
                                if (u.str.is_concat(index_tail[arg0].first, concat_0, concat_1)) {
                                    length_relation.insert(std::make_pair(first_part, concat_0));
                                    length_relation.insert(std::make_pair(first_part, concat_1));
                                }
                                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " update index tail vs substring " << mk_pp(first_part, m) << " = " << mk_pp(index_tail[arg0].second, m) << std::endl;);
                            }
                            else {
                                index_tail.insert(arg0, std::make_pair(first_part, second_part));
                                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " update index tail vs substring " << mk_pp(first_part, m) << " = " << mk_pp(index_tail[arg0].second, m) << std::endl;);
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

                                expr* concat_0 = nullptr;
                                expr* concat_1 = nullptr;
                                if (u.str.is_concat(index_tail[arg1].first, concat_0, concat_1)) {
                                    length_relation.insert(std::make_pair(first_part, concat_0));
                                    length_relation.insert(std::make_pair(first_part, concat_1));
                                }
                                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " update index tail vs substring " << mk_pp(first_part, m) << " = " << mk_pp(index_tail[arg1].first, m) << std::endl;);
                            }
                            else {
                                index_tail.insert(arg1, std::make_pair(first_part, second_part));
                                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " update index tail vs substring " << mk_pp(first_part, m) << " = " << mk_pp(index_tail[arg1].first, m) << std::endl;);
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
    void theory_trau::instantiate_axiom_replace(enode * e) {
        context & ctx = get_context();
        

        app * expr = e->get_owner();

        if (axiomatized_terms.contains(expr)) {
            return;
        }
        axiomatized_terms.insert(expr);

        TRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ":" << mk_pp(expr, m) << std::endl;);
        if (can_solve_contain_family(e)){
            return;
        }
        std::pair<app*, app*> value;
        expr_ref haystack(expr->get_arg(0), m), needle(expr->get_arg(1), m);

        app* a = mk_contains(haystack, needle);
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
                    assert_axiom(createEqualOP(value.first, contain_split_map[keynode].first->get_owner()));
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
                    assert_axiom(createEqualOP(value.first, contain_split_map[keynode].first->get_owner()));
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

        // expr->get_arg(1) == 0 --> x1 = ""
        if (!u.str.is_string(expr->get_arg(1))){
            thenItems.push_back(rewrite_implication(createEqualOP(mk_strlen(expr->get_arg(1)), mk_int(0)),
                                                    createEqualOP(mk_strlen(x1), mk_int(0))));
        }

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

    bool theory_trau::can_solve_contain_family(enode * e){
        app *ex = e->get_owner();
        TRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ":" << mk_pp(ex, m) << std::endl;);
        expr_ref haystack(ex->get_arg(0), m), needle(ex->get_arg(1), m);
        if (haystack == needle) {
            if (u.str.is_replace(ex))
                m_delayed_assertions_todo.push_back(createEqualOP(ex, ex->get_arg(2)));
            else if (u.str.is_contains(ex)){
                m_delayed_assertions_todo.push_back(createEqualOP(ex, m.mk_true()));
            }
            else if (u.str.is_index(ex)){
                m_delayed_assertions_todo.push_back(createEqualOP(ex, mk_int(0)));
            }
            return true;
        }
        else if (needle == mk_string("")){
            if (u.str.is_replace(ex))
                m_delayed_assertions_todo.push_back(createEqualOP(ex, mk_concat(ex->get_arg(2), haystack)));
            else if (u.str.is_contains(ex)){
                m_delayed_assertions_todo.push_back(createEqualOP(ex, m.mk_true()));
            }
            else if (u.str.is_index(ex)){
                m_delayed_assertions_todo.push_back(createEqualOP(ex, mk_int(0)));
            }
            return true;
        }
        else if (u.str.is_concat(haystack)){
            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ":" << mk_pp(ex, m) << std::endl;);
            ptr_vector <expr> nodes;
            get_nodes_in_concat(haystack, nodes);

            unsigned pos = 0;
            for (pos = 0; pos < nodes.size(); ++pos)
                if (nodes[pos] != mk_string(""))
                    break;
            if (pos != nodes.size()) {
                zstring needle_str;
                zstring haystack_0_str;
                if (u.str.is_string(needle, needle_str) && u.str.is_string(nodes[pos], haystack_0_str) && haystack_0_str.contains(needle_str)) {
                    int at = haystack_0_str.indexof(needle_str, 0);
                    if (u.str.is_replace(ex)) {
                        zstring replacement;
                        expr* new_haystack_0_str = nullptr;
                        if (u.str.is_string(ex->get_arg(2), replacement)){
                            new_haystack_0_str = u.str.mk_string(haystack_0_str.replace(needle_str, replacement));
                            m_delayed_assertions_todo.push_back(createEqualOP(ex, mk_concat(new_haystack_0_str, create_concat_from_vector(nodes, pos))));
                        }
                        else {
                            zstring pre = haystack_0_str.extract(0, at);
                            zstring post = haystack_0_str.extract(at + needle_str.length(), haystack_0_str.length() - at - needle_str.length());

                            expr* tmp0 = mk_concat(mk_string(post), create_concat_from_vector(nodes, pos));
                            expr* tmp1 = mk_concat(ex->get_arg(2), tmp0);
                            expr* tmp2 = mk_concat(mk_string(pre), tmp1);
                            m_delayed_assertions_todo.push_back(createEqualOP(ex, tmp2));
                        }
                    }
                    else if (u.str.is_contains(ex)){
                        m_delayed_assertions_todo.push_back(createEqualOP(ex, m.mk_true()));
                    }
                    else if (u.str.is_index(ex)){
                        m_delayed_assertions_todo.push_back(createEqualOP(ex, mk_int(at)));
                    }
                    return true;
                }
                else if (needle == nodes[pos]){
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ":" << mk_pp(ex, m) << std::endl;);
                    if (u.str.is_replace(ex)) {
                        m_delayed_assertions_todo.push_back(createEqualOP(ex, mk_concat(ex->get_arg(2), create_concat_from_vector(nodes, pos))));
                    }
                    else if (u.str.is_contains(ex)){
                        m_delayed_assertions_todo.push_back(createEqualOP(ex, m.mk_true()));
                    }
                    else if (u.str.is_index(ex)){
                        m_delayed_assertions_todo.push_back(createEqualOP(ex, mk_int(0)));
                    }
                    return true;
                }
            }

            // reduce the contain family
            if (can_reduce_contain_family(e->get_owner()))
                return true;
        }


        return false;
    }

    app* theory_trau::mk_replace(expr* a, expr* b, expr* c) const { expr* es[3] = { a, b , c}; return m.mk_app(u.get_family_id(), OP_SEQ_REPLACE, 3, es); }
    app* theory_trau::mk_at(expr* a, expr* b) const { expr* es[2] = { a, b}; return m.mk_app(u.get_family_id(), OP_SEQ_AT, 2, es); }

    bool theory_trau::can_reduce_contain_family(expr* ex){
        app* a = to_app(ex);
        
        TRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ":" << mk_pp(ex, m) << std::endl;);
        expr_ref haystack(a->get_arg(0), m), needle(a->get_arg(1), m);
        ptr_vector <expr> nodes;
        get_nodes_in_concat(haystack, nodes);

        unsigned pos = 0;
        for (pos = 0; pos < nodes.size(); ++pos)
            if (nodes[pos] != mk_string(""))
                break;

        zstring needle_str;
        zstring haystack_0_str;
        if (u.str.is_string(needle, needle_str) && u.str.is_string(nodes[pos], haystack_0_str) && !haystack_0_str.contains(needle_str)) {
            expr* tmp = create_concat_from_vector(nodes, pos);
            if (u.str.is_replace(ex)) {
                expr_ref replace(mk_replace(tmp, needle.get(), a->get_arg(2)), m);
                m_delayed_assertions_todo.push_back(createEqualOP(ex, mk_concat(nodes[pos], replace)));
                instantiate_axiom_replace(get_context().get_enode(replace));
            }
            else if (u.str.is_contains(ex)){
                expr_ref contains(u.str.mk_contains(tmp, needle.get()), m);
                m_delayed_assertions_todo.push_back(createEqualOP(ex, contains));
                instantiate_axiom_contains(get_context().get_enode(contains));
            }
            else if (u.str.is_index(ex)){
                expr_ref index(u.str.mk_index(tmp, needle.get(), mk_int(0)), m);
                m_delayed_assertions_todo.push_back(createEqualOP(ex, index));
                instantiate_axiom_indexof(get_context().get_enode(index));
            }
            return true;
        }
        else {
            while (nodes.size() > 0 && nodes[nodes.size() - 1] == mk_string(""))
                nodes.pop_back();
            if (nodes.size() > 0) {
                expr *last = nodes[nodes.size() - 1];
                nodes.pop_back();

                if (u.str.is_string(needle, needle_str) && u.str.is_string(last, haystack_0_str) &&
                    !haystack_0_str.contains(needle_str)) {
                    expr *tmp = create_concat_from_vector(nodes);
                    if (u.str.is_replace(ex)) {
                        expr_ref replace(mk_replace(tmp, needle.get(), a->get_arg(2)), m);
                        m_delayed_assertions_todo.push_back(
                                createEqualOP(ex, mk_concat(replace, last)));
                        instantiate_axiom_replace(get_context().get_enode(replace));
                    } else if (u.str.is_contains(ex)) {
                        expr_ref contains(u.str.mk_contains(tmp, needle.get()), m);
                        m_delayed_assertions_todo.push_back(createEqualOP(ex, contains));
                        instantiate_axiom_contains(get_context().get_enode(contains));
                    } else if (u.str.is_index(ex)) {
                        expr_ref index(u.str.mk_index(tmp, needle.get(), mk_int(0)), m);
                        m_delayed_assertions_todo.push_back(
                                createEqualOP(ex, index));
                        instantiate_axiom_indexof(get_context().get_enode(index));
                    }
                    return true;
                }
            }

        }
        return false;
    }

    void theory_trau::instantiate_axiom_regexIn(enode * e) {
        context &ctx = get_context();
        

        app *ex = e->get_owner();
        if (axiomatized_terms.contains(ex)) {
            TRACE("str", tout << "already set up RegexIn axiom for " << mk_pp(ex, m) << std::endl;);
            return;
        }
        axiomatized_terms.insert(ex);

        TRACE("str", tout << __LINE__ << __FUNCTION__ << ":" << mk_pp(ex, m) << std::endl;);

        {
            zstring regexStr = get_std_regex_str(ex->get_arg(1));
            // skip Z3str's map check, because we already check if we set up axioms on this term
            regex_in_bool_map.insert(ex->get_arg(0), ex);
            if (!regex_in_var_reg_str_map.contains(ex->get_arg(0))) {
                regex_in_var_reg_str_map.insert(ex->get_arg(0), string_set());
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
                m_delayed_assertions_todo.push_back(rewrite_implication(ex, createGreaterEqOP(mk_strlen(ex->get_arg(0)), mk_int(1))));
            }

            expr_ref_vector regexElements = combine_const_str(parse_regex_components(remove_star_in_star(regex)));
            int boundLen = 100000;
            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ":" << regexElements.size() << std::endl;);
            expr_ref_vector ors(m);
            for (const auto& v : regexElements) {
                ensure_enode(v);
                int tmpLen = 0;
                ptr_vector <expr> elements;
                get_nodes_in_reg_concat(v, elements);
                expr* concat = nullptr;
                for (unsigned i  = 0; i < elements.size(); ++i) {
                    zstring tmpStr;
                    if (u.re.is_to_re(elements[i])) {
                        zstring value;
                        u.str.is_string(to_app(elements[i])->get_arg(0), value);
                        tmpLen += value.length();
                        concat = concat == nullptr ? to_app(elements[i])->get_arg(0) : mk_concat(concat, to_app(elements[i])->get_arg(0));
                    }
                    else if (u.re.is_plus(elements[i]) || u.re.is_union(elements[i])) {
                        vector<zstring> tmpVector;
                        collect_alternative_components(elements[i], tmpVector);
                        int_set lenElements;
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
                                expr* tmpExpr = createEqualOP(mk_strlen(tmp), mk_int(l));
                                orsTmp.push_back(tmpExpr);
                            }
                            if ((int)orsTmp.size() > 1) {
                                assert_axiom(createLessEqOP(mk_strlen(tmp), mk_int(maxLen)));
                            }
                            else if (orsTmp.size() == 1){
                                assert_axiom(createOrOP(orsTmp));
                            }
                        }
                        concat = concat == nullptr ? tmp : mk_concat(concat, tmp);
                    }
                    else if (u.re.is_star(elements[i])) {
                        expr* tmp = mk_str_var(expr2str(elements[i]));
                        expr* tmp_in_re = u.re.mk_in_re(tmp, elements[i]);
                        m_delayed_assertions_todo.push_back(tmp_in_re);
                        concat = concat == nullptr ? tmp : mk_concat(concat, tmp);
                    }
                    else if (u.re.is_full_char(elements[i])) {
                        expr* tmp = mk_str_var(expr2str(elements[i]));
                        assert_axiom(createEqualOP(mk_strlen(tmp), mk_int(1)));
                        concat = concat == nullptr ? tmp : mk_concat(concat, tmp);
                    }
                    else if (u.re.is_full_seq(elements[i])){
                        expr* tmp = mk_str_var(expr2str(elements[i]));
                        concat = concat == nullptr ? tmp : mk_concat(concat, tmp);
                    }
                    ensure_enode(concat);
                    ensure_enode(mk_strlen(concat));
                }

                boundLen = boundLen < tmpLen ? boundLen : tmpLen;
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ":" << mk_pp(str, m) << " " << mk_pp(concat, m) << std::endl;);
                ors.push_back(createEqualOP(str.get(), concat));
            }

            assert_implication(ex, createOrOP(ors));
            return;
        }

        // quick reference for the following code:
        //  - ex: top-level regex membership term
        //  - str: string term appearing in ex
        //  - regex: regex term appearing in ex
        //  ex ::= (str.in.re str regex)

        expr* a0 = nullptr;
        expr* a1 = nullptr;
        if (u.re.is_to_re(regex, a0)) {
            STRACE("str", tout << __LINE__ << " "  << __FUNCTION__ << ":" << mk_pp(ex, m) << std::endl;);

            expr_ref rxStr(a0, m);
            // want to assert 'expr IFF (str == rxStr)'
            expr_ref rhs(ctx.mk_eq_atom(str, rxStr), m);
            expr_ref finalAxiom(m.mk_iff(ex, rhs), m);
            SASSERT(finalAxiom);
            assert_axiom(finalAxiom);
        } else if (u.re.is_concat(regex, a0, a1)) {
            STRACE("str", tout << __LINE__ << " "  << __FUNCTION__ << ":" << mk_pp(ex, m) << std::endl;);
            expr_ref var1(mk_regex_rep_var(), m);
            expr_ref var2(mk_regex_rep_var(), m);
            expr_ref rhs(mk_concat(var1, var2), m);
            expr_ref rx1(a0, m);
            expr_ref rx2(a1, m);
            expr_ref var1InRegex1(mk_regexIn(var1, rx1), m);
            expr_ref var2InRegex2(mk_regexIn(var2, rx2), m);

            expr_ref_vector items(m);
            items.push_back(var1InRegex1);
            items.push_back(var2InRegex2);
            items.push_back(ctx.mk_eq_atom(ex, ctx.mk_eq_atom(str, rhs)));

            expr_ref finalAxiom(mk_and(items), m);
            SASSERT(finalAxiom);
            assert_axiom(finalAxiom);
        } else if (u.re.is_union(regex, a0, a1)) {
            STRACE("str", tout << __LINE__ << " "  << __FUNCTION__ << ":" << mk_pp(ex, m) << std::endl;);

            expr_ref var1(mk_regex_rep_var(), m);
            expr_ref var2(mk_regex_rep_var(), m);
            expr_ref orVar(m.mk_or(ctx.mk_eq_atom(str, var1), ctx.mk_eq_atom(str, var2)), m);
            expr_ref regex1(a0, m);
            expr_ref regex2(a1, m);
            expr_ref var1InRegex1(mk_regexIn(var1, regex1), m);
            expr_ref var2InRegex2(mk_regexIn(var2, regex2), m);
            expr_ref_vector items(m);
            items.push_back(var1InRegex1);
            items.push_back(var2InRegex2);
            items.push_back(ctx.mk_eq_atom(ex, orVar));
            assert_axiom(mk_and(items));

        } else if (u.re.is_star(regex, a0)) {
            // slightly more complex due to the unrolling step.
            expr_ref regex1(a0, m);
            expr_ref unrollCount(mk_unroll_bound_var(), m);
            expr_ref unrollFunc(mk_unroll(regex1, unrollCount), m);
            expr_ref_vector items(m);
            items.push_back(ctx.mk_eq_atom(ex, ctx.mk_eq_atom(str, unrollFunc)));
            items.push_back(ctx.mk_eq_atom(ctx.mk_eq_atom(unrollCount, mk_int(0)), ctx.mk_eq_atom(unrollFunc, mk_string(""))));
            expr_ref finalAxiom(mk_and(items), m);
            SASSERT(finalAxiom);
            assert_axiom(finalAxiom);
        } else if (u.re.is_range(regex, a0, a1)) {
            // (re.range "A" "Z") unfolds to (re.union "A" "B" ... "Z");
            // we rewrite to expr IFF (str = "A" or str = "B" or ... or str = "Z")
            expr_ref lo(a0, m);
            expr_ref hi(a1, m);
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
            NOT_IMPLEMENTED_YET();
        }
    }

    expr* theory_trau::is_regex_plus_breakdown(expr* e){
        expr* arg0 = nullptr, * arg1 = nullptr;
        if (u.re.is_concat(to_app(e), arg0, arg1)){
            expr* arg10 = nullptr, * arg00 = nullptr;
            if (u.re.is_star(to_app(arg1), arg10)){
                if (arg10 == arg0)
                    return arg1;
            }

            if (u.re.is_star(to_app(arg0), arg00)){
                if (arg00 == arg1)
                    return arg0;
            }
        }
        return nullptr;
    }

    void theory_trau::instantiate_axiom_str_to_int(enode * e) {
        context & ctx = get_context();
        

        app * ex = e->get_owner();
        if (axiomatized_terms.contains(ex)) {
            TRACE("str", tout << "already set up str.to-int axiom for " << mk_pp(ex, m) << std::endl;);
            return;
        }
        axiomatized_terms.insert(ex);

        TRACE("str", tout << "instantiate str.to-int axiom for " << mk_pp(ex, m) << std::endl;);

        // let expr = (str.to-int S)
        // axiom 1: expr >= -1
        // axiom 2: S = "" --> expr = -1

        {
            expr_ref axiom1(m_autil.mk_ge(ex, m_autil.mk_numeral(rational::minus_one(), true)), m);
            assert_axiom(axiom1);

            assert_axiom(rewrite_implication(createEqualOP(to_app(ex)->get_arg(0), mk_string("")), createEqualOP(ex, mk_int(-1))));
        }


        expr_ref s2i(mk_int_var("s2i"), m);
        assert_axiom(ctx.mk_eq_atom(s2i, ex));
        quickpath_str2int(s2i.get(), ex, false);
        quickpath_int2str(s2i.get(), to_app(ex)->get_arg(0), false);
    }

    void theory_trau::instantiate_axiom_int_to_str(enode * e) {
        context & ctx = get_context();
        

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
        quickpath_int2str(to_app(ex)->get_arg(0), i2s, false);
    }

    app * theory_trau::mk_strlen(expr * e) {
        app* tmp = u.str.mk_length(e);
        ensure_enode(tmp);
        return tmp;
    }

    expr * theory_trau::mk_string(zstring const& str) {
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

    expr * theory_trau::mk_string(const char * str) {
        symbol sym(str);
        return u.str.mk_string(sym);
    }

    app * theory_trau::mk_fresh_const(char const* name, sort* s) {
        string_buffer<64> buffer;
        buffer << name;
        buffer << "!tmp";
        buffer << m_fresh_id;
        m_fresh_id++;
        return u.mk_skolem(symbol(buffer.c_str()), 0, nullptr, s);
    }

    app * theory_trau::mk_str_var(std::string name) {
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

        return a;
    }

    expr * theory_trau::mk_concat(expr * n1, expr * n2) {
        context &ctx = get_context();
        
        ENSURE(n1 != nullptr);
        ENSURE(n2 != nullptr);
        bool n1HasEqcValue = false;
        bool n2HasEqcValue = false;
        n1 = get_eqc_value(n1, n1HasEqcValue);
        n2 = get_eqc_value(n2, n2HasEqcValue);
        if (n1HasEqcValue && n2HasEqcValue) {
            return mk_concat_const_str(n1, n2);
        } else if (n1HasEqcValue && !n2HasEqcValue) {
            zstring n1_str;
            u.str.is_string(n1, n1_str);
            if (n1_str.empty()) {
                return n2;
            }
            expr *n2_arg0 = nullptr, *n2_arg1 = nullptr;
            if (u.str.is_concat(to_app(n2), n2_arg0, n2_arg1)) {
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
            expr *n1_arg0 = nullptr, *n1_arg1 = nullptr;
            if (u.str.is_concat(to_app(n1), n1_arg0, n1_arg1)) {
                if (u.str.is_string(n1_arg1)) {
                    n1 = n1_arg0;
                    n2 = mk_concat_const_str(n1_arg1, n2); // n2 will be a constant
                }
            }
        } else {
            expr *n1_arg0 = nullptr, *n1_arg1 = nullptr, *n2_arg0 = nullptr, *n2_arg1 = nullptr;
            if (u.str.is_concat(to_app(n1), n1_arg0, n1_arg1) && u.str.is_concat(to_app(n2), n2_arg0, n2_arg1)) {
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
                expr_ref conclusion00(createEqualOP(concatAst, n2), m);
                assert_implication(premise00, conclusion00);

                // | n2 | = 0 --> concat = n1
                expr_ref premise01(ctx.mk_eq_atom(mk_int(0), mk_strlen(n2)), m);
                expr_ref conclusion01(createEqualOP(concatAst, n1), m);
                assert_implication(premise01, conclusion01);
            }
        }
        return concatAst;
    }

    app * theory_trau::mk_int(int n) {
        return m_autil.mk_numeral(rational(n), true);
    }

    app * theory_trau::mk_int(rational & q) {
        return m_autil.mk_numeral(q, true);
    }

    app * theory_trau::mk_contains(expr * haystack, expr * needle) {
        rational len;

        if (haystack == needle || (get_len_value(needle, len) && len.get_int64() == 0))
            return m.mk_true();

        app * contains = u.str.mk_contains(haystack, needle); // TODO double-check semantics/argument order
        m_trail.push_back(contains);
        // immediately force internalization so that axiom setup does not fail
        get_context().internalize(contains, false);
        set_up_axioms(contains);
        if (!u.str.is_string(needle)) {
            assert_axiom(rewrite_implication(createEqualOP(mk_strlen(needle), mk_int(0)), createEqualOP(contains, m.mk_true())));
        }
        return contains;
    }

    // note, this invokes "special-case" handling for the start index being 0
    app * theory_trau::mk_indexof(expr * haystack, expr * needle) {
        app * indexof = u.str.mk_index(haystack, needle, mk_int(0));
        m_trail.push_back(indexof);
        // immediately force internalization so that axiom setup does not fail
        get_context().internalize(indexof, false);
        set_up_axioms(indexof);
        return indexof;
    }

    app * theory_trau::mk_int_var(std::string name) {
        context & ctx = get_context();
        

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

        return a;
    }

    app * theory_trau::mk_regex_rep_var() {
        context & ctx = get_context();

        sort * string_sort = u.str.mk_string_sort();
        app * a = mk_fresh_const("regex", string_sort);
        m_trail.push_back(a);

        ctx.internalize(a, false);
        SASSERT(ctx.get_enode(a) != NULL);
        SASSERT(ctx.e_internalized(a));
        mk_var(ctx.get_enode(a));
        m_basicstr_axiom_todo.push_back(ctx.get_enode(a));
        STRACE("str", tout << "add " << mk_pp(a, m) << " to m_basicstr_axiom_todo" << std::endl;);

        variable_set.insert(a);
        //internal_variable_set.insert(a);
        regex_variable_set.insert(a);

        return a;
    }

    expr * theory_trau::mk_regexIn(expr * str, expr * regexp) {
        app * regexIn = u.re.mk_in_re(str, regexp);
        // immediately force internalization so that axiom setup does not fail
        get_context().internalize(regexIn, false);
        set_up_axioms(regexIn);
        return regexIn;
    }

    app * theory_trau::mk_unroll(expr * n, expr * bound) {
        context & ctx = get_context();
        

        expr * args[2] = {n, bound};
        app * unrollFunc = m.mk_app(get_id(), _OP_RE_UNROLL, 0, nullptr, 2, args);
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

    app * theory_trau::mk_unroll_bound_var() {
        return mk_int_var("unroll");
    }

    app * theory_trau::mk_str_to_re(expr * n){
        expr * args[1] = {n};
        app * a = m.mk_app(get_id(), _OP_STRING_TO_REGEXP, 0, nullptr, 1, args);
        return a;
    }

    app * theory_trau::mk_arr_var(zstring name) {
        context & ctx = get_context();
        STRACE("str", tout << __FUNCTION__ << ":" << name << std::endl;);
        sort * int_sort = m.mk_sort(m_autil.get_family_id(), INT_SORT);
        sort * arr_sort = m_arrayUtil.mk_array_sort(int_sort, int_sort);
        app * a = mk_fresh_const(name.encode().c_str(), arr_sort);
        ctx.internalize(a, false);
        ctx.mark_as_relevant(a);
        // I'm assuming that this combination will do the correct thing in the integer theory.

        m_trail.push_back(a);

        return a;
    }

    void theory_trau::get_nodes_in_concat(expr * node, ptr_vector<expr> & nodeList) {
        app * a_node = to_app(node);
        expr * leftArg = nullptr, * rightArg = nullptr;
        if (!u.str.is_concat(a_node, leftArg, rightArg)) {
            nodeList.push_back(node);
            return;
        } else {
            get_nodes_in_concat(leftArg, nodeList);
            get_nodes_in_concat(rightArg, nodeList);
        }
    }

    void theory_trau::get_nodes_in_reg_concat(expr * node, ptr_vector<expr> & nodeList) {
        app * a_node = to_app(node);
        expr * leftArg = nullptr, * rightArg = nullptr;
        if (!u.re.is_concat(a_node, leftArg, rightArg)) {
            nodeList.push_back(node);
            return;
        } else {
            get_nodes_in_reg_concat(leftArg, nodeList);
            get_nodes_in_reg_concat(rightArg, nodeList);
        }
    }

    void theory_trau::get_all_nodes_in_concat(expr * node, ptr_vector<expr> & nodeList) {
        app * a_node = to_app(node);
        expr * leftArg = nullptr, * rightArg = nullptr;
        if (!u.str.is_concat(a_node, leftArg, rightArg)) {
            nodeList.push_back(node);
            return;
        } else {
            nodeList.push_back(node);
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
    expr * theory_trau::mk_concat_const_str(expr * n1, expr * n2) {
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

    expr * theory_trau::get_eqc_value(expr * n, bool & hasEqcValue) {
        return z3str2_get_eqc_value(n, hasEqcValue);
    }


    // Simulate the behaviour of get_eqc_value() from Z3str2.
    // We only check m_find for a string constant.

    expr * theory_trau::z3str2_get_eqc_value(expr * n , bool & hasEqcValue) {
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

    expr * theory_trau::get_eqc_next(expr * n) {
        theory_var v = get_var(n);
        if (v != null_theory_var) {
            theory_var r = m_find.next(v);
            return get_ast(r);
        }
        return n;
    }

    theory_var theory_trau::get_var(expr * n) const {
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

    app * theory_trau::get_ast(theory_var v) {
        return get_enode(v)->get_owner();
    }

    static zstring str2RegexStr(zstring str) {
        zstring res("");
        unsigned len = str.length();
        for (unsigned i = 0; i < len; i++) {
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

    zstring theory_trau::get_std_regex_str(expr * regex) {
        app *a_regex = to_app(regex);
        expr *reg1Ast = nullptr, *reg2Ast = nullptr;
        if (u.re.is_to_re(a_regex, reg1Ast)) {
            zstring regAstVal;
            u.str.is_string(reg1Ast, regAstVal);
            zstring regStr = str2RegexStr(regAstVal);
            return regStr;
        } else if (u.re.is_concat(a_regex, reg1Ast, reg2Ast)) {
            zstring reg1Str = get_std_regex_str(reg1Ast);
            zstring reg2Str = get_std_regex_str(reg2Ast);
            return zstring("(") + reg1Str + zstring(")(") + reg2Str + zstring(")");
        } else if (u.re.is_union(a_regex, reg1Ast, reg2Ast)) {
            zstring reg1Str = get_std_regex_str(reg1Ast);
            zstring reg2Str = get_std_regex_str(reg2Ast);
            return zstring("(") + reg1Str + zstring(")|(") + reg2Str + zstring(")");
        } else if (u.re.is_star(a_regex, reg1Ast)) {
            zstring reg1Str = get_std_regex_str(reg1Ast);
            return zstring("(") + reg1Str + zstring(")*");
        } else if (u.re.is_range(a_regex, reg1Ast, reg2Ast)) {
            zstring range1val, range2val;
            u.str.is_string(reg1Ast, range1val);
            u.str.is_string(reg2Ast, range2val);
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
            TRACE("str", tout << "BUG: unrecognized regex term " << mk_pp(regex, m) << std::endl;);
            UNREACHABLE();
            return zstring("");
        }
    }

    bool theory_trau::get_len_value(expr* e, rational& val) {
        if (opt_DisableIntegerTheoryIntegration) {
            TRACE("str", tout << "WARNING: integer theory integration disabled" << std::endl;);
            return false;
        }

        context& ctx = get_context();
        

        rational val1;
        expr_ref len(m), len_val(m);
        expr* e1 = nullptr, *e2 = nullptr;
        ptr_vector<expr> todo;
        todo.push_back(e);
        val.reset();
        while (!todo.empty()) {
            expr* c = todo.back();
            todo.pop_back();
            if (u.str.is_concat(c, e1, e2)) {
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

    bool theory_trau::get_arith_value(expr* e, rational& val) const {
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

    bool theory_trau::upper_bound(expr* _e, rational& hi) const {
        context& ctx = get_context();
        
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

    bool theory_trau::lower_bound(expr* _e, rational& lo) const {
        context& ctx = get_context();
        
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

    bool theory_trau::upper_num_bound(expr* e, rational& hi) const {
        context& ctx = get_context();
        
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

    bool theory_trau::lower_num_bound(expr* e, rational& lo) const {
        context& ctx = get_context();
        
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

    void theory_trau::get_concats_in_eqc(expr * n, obj_hashtable<expr> & concats) {

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
    void theory_trau::get_const_str_asts_in_node(expr * node, expr_ref_vector & astList) {
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

    eautomaton* theory_trau::get_automaton(expr* re) {
        eautomaton* result = nullptr;
        
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
    void theory_trau::get_const_regex_str_asts_in_node(expr * node, expr_ref_vector & astList) {
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
    bool theory_trau::has_empty_vars(expr * node) {
        ptr_vector<expr> vars;
        get_nodes_in_concat(node, vars);
        rational vLen;
        for (unsigned i = 0; i < vars.size(); ++i){
            if (get_len_value(vars[i], vLen))
                if (vLen.get_int64() == 0)
                    return true;
        }
        return false;
    }

    /*
     * Collect important vars in AST node
     */
    void theory_trau::get_important_asts_in_node(expr * node, obj_map<expr, int> const& non_fresh_vars, expr_ref_vector & astList, bool consider_itself) {
        if (consider_itself)
            if (non_fresh_vars.contains(node))
                astList.push_back(node);

        if (is_app(node)) {
            app * func_app = to_app(node);
            unsigned int argCount = func_app->get_num_args();
            for (unsigned int i = 0; i < argCount; i++) {
                expr * argAst = func_app->get_arg(i);
                get_important_asts_in_node(argAst, non_fresh_vars, astList, true);
            }
        }
    }

    expr * theory_trau::rewrite_implication(expr * premise, expr * conclusion) {
        
        return m.mk_or(mk_not(m, premise), conclusion);
    }

    void theory_trau::assert_implication(expr * premise, expr * conclusion) {
        
        expr_ref axiom(m.mk_or(mk_not(m, premise), conclusion), m);
        assert_axiom(axiom);
    }

    expr* theory_trau::query_theory_arith_core(expr* n, model_generator& mg){
        context& ctx = get_context();
        family_id afid = m_autil.get_family_id();
        expr_ref_vector values(m);
        app* value = nullptr;
        do {
            theory_mi_arith* tha = get_th_arith<theory_mi_arith>(ctx, afid, n);
            if (tha) {
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(n, m) << std::endl;);
                model_value_proc* tmp = tha->mk_value(ctx.get_enode(n), mg);
                value = tmp->mk_value(mg, values);
                break;
            }
            theory_i_arith* thi = get_th_arith<theory_i_arith>(ctx, afid, n);
            if (thi) {
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(n, m) << std::endl;);
                model_value_proc* tmp = tha->mk_value(ctx.get_enode(n), mg);
                value = tmp->mk_value(mg, values);
                break;
            }
            theory_lra* thr = get_th_arith<theory_lra>(ctx, afid, n);
            if (thr) {
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(n, m) << std::endl;);
                model_value_proc* tmp = tha->mk_value(ctx.get_enode(n), mg);
                value = tmp->mk_value(mg, values);
                break;
            }
            break;
        }
        while (false);

        return value;
    }

    void theory_trau::init_model(model_generator& mg) {
        
        context& ctx = get_context();
        STRACE("str", tout << "initializing model..." << std::endl;);
        expr_ref_vector included_nodes(m);

        // prepare dependency_graph
        for (const auto& n : uState.eq_combination) {
            if (!ctx.is_relevant(n.m_key))
                continue;

            expr_ref_vector dep = get_dependencies(n.m_key);
            expr_ref_vector tmp(m);
            collect_eq_nodes(n.m_key, tmp);
            expr* reg = nullptr;
            for (const auto& nn : dep) {
                if (!ctx.is_relevant(nn))
                    continue;
                if (u.str.is_string(nn) || is_non_fresh(nn) || is_internal_regex_var(nn, reg) || is_regex_concat(nn)) {
                    if (!are_equal_exprs(n.m_key, nn)) {
                        expr* tmp = ctx.get_enode(n.m_key)->get_root()->get_owner();
                        if (!dependency_graph.contains(tmp)){
                            dependency_graph.insert(tmp, {});
                        }
                        dependency_graph[tmp].insert(
                                ctx.get_enode(nn)->get_root()->get_owner());
                    }
                    if (!included_nodes.contains(ctx.get_enode(nn)->get_root()->get_owner()))
                        included_nodes.push_back(ctx.get_enode(nn)->get_root()->get_owner());
                }
            }
        }

        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << std::endl;);
        for (const auto& c : concat_astNode_map) {
            if (!ctx.is_relevant(c.get_value()) || !ctx.is_relevant(c.get_key1()) || !ctx.is_relevant(c.get_key2()))
                continue;
            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(ctx.get_enode(c.get_value())->get_root()->get_owner(), m) << std::endl;);
            rational len;
            if ((get_len_value(c.get_key2(), len) && len.get_int64() == 0) ||
                (get_len_value(c.get_key1(), len) && len.get_int64() == 0))
                continue;

            expr* key1_root = ctx.get_enode(c.get_key1())->get_root()->get_owner();
            expr* key2_root = ctx.get_enode(c.get_key2())->get_root()->get_owner();
            expr* c_root = ctx.get_enode(c.get_value())->get_root()->get_owner();
            expr* reg = nullptr;
            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(c_root, m) << std::endl;);
            if (!dependency_graph.contains(c_root)){
                dependency_graph.insert(c_root, {});
            }

            // arg1
            if (u.str.is_string(key2_root) || is_non_fresh(key2_root) || is_internal_regex_var(key2_root, reg) || is_regex_concat(key2_root)) {
                if (!are_equal_exprs(c_root, key2_root)) {
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(c.get_key2(), m) << " VS " << mk_pp(c.get_value(), m) << std::endl;);
                    dependency_graph[c_root].insert(c.get_key2());
                    if (key2_root != c.get_value())
                        dependency_graph[c_root].insert(key2_root);
                }
            }
            else if (!included_nodes.contains(key2_root)) {
                if ((get_len_value(c.get_key1(), len) && len.get_int64() == 0) || are_equal_exprs(c.get_key2(), c.get_value()))
                    continue;
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(c.get_key2(), m) << " VS " << mk_pp(c.get_value(), m) << std::endl;);
                if (key2_root != c.get_value()) {
                    if (!dependency_graph.contains(key2_root)){
                        dependency_graph.insert(key2_root, {});
                    }
                    dependency_graph[key2_root].insert(c.get_value());
                }
                if (!dependency_graph.contains(c.get_key2())){
                    dependency_graph.insert(c.get_key2(), {});
                }
                dependency_graph[c.get_key2()].insert(c.get_value());
                if (c.get_key2() != key2_root) {
                    if (!expr_array_linkers.contains(key2_root)){
                        expr_array_linkers.insert(key2_root, {});
                    }
                    expr_array_linkers[key2_root] = c.get_key2();
                }
            }

            // arg0
            if (u.str.is_string(key1_root) || is_non_fresh(key1_root) || is_internal_regex_var(key1_root, reg) || is_regex_concat(key1_root)) {
                if (!are_equal_exprs(c_root, key1_root)) {
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(c.get_key1(), m) << " VS " << mk_pp(c.get_value(), m) << std::endl;);
                    dependency_graph[c_root].insert(c.get_key1());
                    if (key1_root != c.get_value())
                        dependency_graph[c_root].insert(key1_root);
                }
            }
            else if (!included_nodes.contains(key1_root)) {
                if ((get_len_value(c.get_key2(), len) && len.get_int64() == 0) || are_equal_exprs(c.get_key1(), c.get_value()))
                    continue;
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(c.get_key1(), m) << " VS " << mk_pp(c.get_value(), m) << std::endl;);
                if (!dependency_graph.contains(key1_root)){
                    dependency_graph.insert(key1_root, {});
                }

                dependency_graph[key1_root].insert(c.get_value());

                if (!dependency_graph.contains(c.get_key1())){
                    dependency_graph.insert(c.get_key1(), {});
                }
                dependency_graph[c.get_key1()].insert(c.get_value());

                if (c.get_key1() != key1_root) {
                    if (!expr_array_linkers.contains(key1_root)){
                        expr_array_linkers.insert(key1_root, {});
                    }
                    expr_array_linkers[key1_root] = c.get_key1();
                }
            }
        }

        for (const auto& e: dependency_graph) {
            STRACE("str", tout << __LINE__ << " " << mk_pp(e.m_key, m) << std::endl;);
            for (const auto& ee : e.m_value)
                STRACE("str", tout << __LINE__ << " \t" << mk_pp(ee, m) << std::endl;);
        }

        default_char = setup_default_char(init_included_char_set(), init_excluded_char_set());
    }

    void theory_trau::finalize_model(model_generator& mg) {
        STRACE("str", tout << "finalizing model..." << std::endl;);
    }

    void theory_trau::assert_axiom(expr *const e) {
        if (e == nullptr || m.is_true(e)) return;

        
        context& ctx = get_context();
        expr_ref ex{e, m};

        if (!ctx.b_internalized(ex)) {
            ctx.internalize(ex, false);
        }
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(e, m) << std::endl;);
        literal lit(ctx.get_literal(ex));
        ctx.mark_as_relevant(lit);
        ctx.mk_th_axiom(get_id(), 1, &lit);
    }

    void theory_trau::assert_axiom(expr *const e1, expr *const e2) {
        assert_implication(e2, e1);
        return;
        
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

    void theory_trau::dump_assignments() {
        STRACE("str", \
                
                context& ctx = get_context();

                for (unsigned i = 0; i < mful_scope_levels.size(); ++i){
                    literal tmp = ctx.get_literal(mful_scope_levels[i].get());
                    int assignLvl = ctx.get_assign_level(tmp);
                    STRACE("str", tout << __LINE__ << " assigned expr " << mk_pp(mful_scope_levels[i].get(), m) << ", assignLevel = " << assignLvl << std::endl;);
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

    void theory_trau::dump_literals() {
        STRACE("str", \
                
                context& ctx = get_context();
                expr_ref_vector tmpExprs(m);
                ctx.get_relevant_literals(tmpExprs);
                for (unsigned i = 0; i < tmpExprs.size(); ++i) {
                    literal tmp = ctx.get_literal(tmpExprs[i].get());
                    int assignLvl = ctx.get_assign_level(tmp);
                    if (ctx.get_assignment(tmpExprs[i].get()) == l_true && !m.is_or(tmpExprs[i].get()) && !m.is_and(tmpExprs[i].get()) && !m.is_ite(tmpExprs[i].get())){
                        STRACE("str", tout << __LINE__ << " guessed literal " << mk_pp(tmpExprs[i].get(), m) << ", assignLevel = " << assignLvl << std::endl;);
                    }
                }
        );
    }

    void theory_trau::fetch_guessed_core_exprs(
            obj_map<expr, ptr_vector<expr>> const& eq_combination,
            expr_ref_vector &guessed_exprs,
            expr_ref_vector const& diseq_exprs,
            rational bound){
        
        // collect vars
        expr_ref_vector all_vars = collect_all_vars_in_eq_combination(eq_combination);
        expr_ref_vector ret(m);
        add_equalities_to_core(guessed_exprs, all_vars, ret);
        add_assignments_to_core(all_vars, ret);
        add_disequalities_to_core(diseq_exprs, ret);

        if (get_bound_str_int_control_var() != nullptr) {
            if (bound == rational(0))
                ret.push_back(createEqualOP(get_bound_str_int_control_var(), mk_int(str_int_bound)));
            else
                ret.push_back(createEqualOP(get_bound_str_int_control_var(), mk_int(bound)));
        }

        guessed_exprs.reset();
        guessed_exprs.append(ret);
    }

    void theory_trau::add_equalities_to_core(expr_ref_vector guessed_exprs, expr_ref_vector &all_vars, expr_ref_vector &core){
        expr_ref_vector tmp_guessed_exprs(m);
        while (true) {
            // collect all eq
            for (const auto &e : guessed_exprs) {
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
                    if (check_intersection_not_empty(argVec, all_vars)) {
                        // add lhs
                        core.push_back(e);
                        adding = true;
                        update_all_vars(all_vars, lhs);
                        update_all_vars(all_vars, rhs);
                    }
                }

                // check lhs
                if (!adding && u.str.is_concat(lhs)) {
                    ptr_vector<expr> argVec;
                    get_nodes_in_concat(lhs, argVec);
                    if (check_intersection_not_empty(argVec, all_vars)) {
                        // add rhs
                        core.push_back(e);
                        adding = true;
                        update_all_vars(all_vars, rhs);
                        update_all_vars(all_vars, lhs);
                    }
                }

                if (!adding){
                    if (!u.str.is_concat(lhs) && !u.str.is_concat(rhs)) {
                        if (!u.str.is_string(lhs) && all_vars.contains(lhs)){
                            core.push_back(e);
                            adding = true;
                            if (!all_vars.contains(rhs))
                                all_vars.push_back(rhs);
                        }
                        else if (!u.str.is_string(rhs) && all_vars.contains(rhs)){
                            core.push_back(e);
                            adding = true;
                            if (!all_vars.contains(lhs))
                                all_vars.push_back(lhs);
                        }
                    }
                }


                if (adding == false)
                    tmp_guessed_exprs.push_back(e);
            }

            // check if no improvement
            if (tmp_guessed_exprs.size() == guessed_exprs.size())
                break;

            guessed_exprs.reset();
            guessed_exprs.append(tmp_guessed_exprs);
            tmp_guessed_exprs.reset();
            tmp_guessed_exprs.append(tmp_guessed_exprs);
        }
    }

    void theory_trau::add_disequalities_to_core(expr_ref_vector const& diseq_exprs, expr_ref_vector &core){
        for (const auto& e : diseq_exprs){
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
                                core.push_back(e);
                        }
                    }
                    else if (is_contain_equality(rhs, key)){
                        zstring keyStr;
                        if (u.str.is_string(key, keyStr)){
                            if (!is_trivial_contain(keyStr))
                                core.push_back(e);
                        }
                    }
                }
            }
        }
    }

    void theory_trau::add_assignments_to_core(expr_ref_vector const& all_vars, expr_ref_vector &core){
        rational len;
        for (const auto& v : all_vars) {
            if (get_len_value(v, len) && len.get_int64() == 0) {
                core.push_back(createEqualOP(v, mk_string("")));
            }
            else if (u.str.is_string(v)) {
                // const = concat
                expr_ref_vector eqs(m);
                collect_eq_nodes(v, eqs);
                for (const auto& eq : eqs)
                    if (u.str.is_concat(eq)) {
                        if ((int)get_assign_lvl(v, eq) < m_scope_level)
                            core.push_back(createEqualOP(v, eq));
                    }
                    else if (all_vars.contains(eq) && eq != v){
                        if (!core.contains(createEqualOP(v, eq)))
                            if ((int)get_assign_lvl(v, eq) < m_scope_level)
                                core.push_back(createEqualOP(v, eq));
                    }
            }
        }
    }

    unsigned theory_trau::get_assign_lvl(expr* a, expr* b){
        context& ctx = get_context();
        expr* tmp = createEqualOP(a, b);
        return ctx.get_assign_level(ctx.get_literal(tmp));
    }

    void theory_trau::fetch_related_exprs(
            expr_ref_vector const& all_vars,
            expr_ref_vector &guessed_eqs){
        

        expr_ref_vector ret(m);
        rational len_value;
        for (const auto &e : guessed_eqs) {
            expr *lhs = to_app(e)->get_arg(0);
            expr *rhs = to_app(e)->get_arg(1);

            // skip empty values
            if (get_len_value(lhs, len_value) && len_value.get_int64() == 0)
                continue;

            if (get_len_value(rhs, len_value) && len_value.get_int64() == 0)
                continue;

            // check rhs
            ptr_vector<expr> argVec;
            get_nodes_in_concat(rhs, argVec);
            if (check_intersection_not_empty(argVec, all_vars)) {
                argVec.reset();
                get_nodes_in_concat(lhs, argVec);
                if (check_intersection_not_empty(argVec, all_vars)) {
                    // add rhs
                    ret.push_back(e);
                }
            }
        }

        // capture empty values
        for (const auto& v : all_vars)
            if (get_len_value(v, len_value) && len_value.get_int64() == 0)
                ret.push_back(createEqualOP(v, mk_string("")));

        guessed_eqs.reset();
        guessed_eqs.append(ret);
        for (unsigned i = 0; i < guessed_eqs.size(); ++i)
            STRACE("str", tout << __LINE__ << " core guessed exprs " << mk_pp(guessed_eqs[i].get(), m) << std::endl;);
    }

    /*
     * v does not contain replacekey
     */
    expr_ref_vector theory_trau::check_contain_related_vars(
            expr* v,
            zstring containKey){
        
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << std::endl;);

        expr_ref_vector ret(m);
        zstring value;
        rational lenValue;
        ptr_vector<expr> childrenVector;
        get_all_nodes_in_concat(v, childrenVector);

        for (unsigned i = 0; i < childrenVector.size(); ++i) {
            ret.push_back(childrenVector[i]);
            if (u.str.is_string(childrenVector[i], value))
                if (value.contains(containKey))
                    return ret;
        }

        int pos = 0;
        expr *arg0 = nullptr, *arg1 = nullptr, *arg2 = nullptr;
        while (pos < (int)ret.size()){
            expr* tmp = ret[pos].get();
            pos++;

            if (get_len_value(tmp, lenValue) && lenValue.get_int64() == 0)
                continue;

            if (u.str.is_replace(tmp, arg0, arg1, arg2)){
                zstring val;
                if (u.str.is_string(arg1, val)) {
                    if (!val.contains(containKey)) {  // x = replace y val ? && val does not contain key --> y does not contain key
                        ptr_vector<expr> childrenVector;
                        get_all_nodes_in_concat(arg0, childrenVector);
                        for (unsigned j = 0; j < childrenVector.size(); ++j)
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
            for (unsigned i = 0; i  < tmpVector.size(); ++i)
                if (!ret.contains(tmpVector[i].get())){
                    STRACE("str", tout << __LINE__ << " " << mk_pp(tmp, m) << " == " << mk_pp(tmpVector[i].get(), m) << std::endl;);
                    ptr_vector<expr> childrenVector;
                    get_all_nodes_in_concat(tmpVector[i].get(), childrenVector);
                    for (unsigned j = 0; j < childrenVector.size(); ++j)
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

    expr_ref_vector theory_trau::collect_all_vars_in_eq_combination(obj_map<expr, ptr_vector<expr>> const& eq_combination){
        expr_ref_vector all_vars(m);
        for (const auto& eq : eq_combination){
            // collect vars or not
            // not collect if it is not important, and none of variable is really important

            for (const auto& e : eq.get_value()) {
                ptr_vector<expr> nodes;
                get_nodes_in_concat(e, nodes);
                for (unsigned i = 0; i < nodes.size(); ++i) {
                    zstring value;
                    if (u.str.is_string(nodes[i], value) && value.length() == 0)
                        continue;
                    if (!all_vars.contains(nodes[i]))
                        all_vars.push_back(nodes[i]);
                }
            }
        }
        return all_vars;
    }

    void theory_trau::update_all_vars(expr_ref_vector &allvars, expr* e){
        if (u.str.is_concat(e)) {
            ptr_vector<expr> nodes;
            get_nodes_in_concat(e, nodes);
            for (unsigned j = 0; j < nodes.size(); ++j)
                if (!allvars.contains(nodes[j]))
                    allvars.push_back(nodes[j]);
        }
        else {
            if (!allvars.contains(e))
                allvars.push_back(e);
        }
    }

    bool theory_trau::check_intersection_not_empty(ptr_vector<expr> const& v, obj_hashtable<expr> const& allvars){
        for (unsigned i = 0; i < v.size(); ++i)
            if (!u.str.is_string(v[i]))
                if (allvars.contains(v[i]))
                    return true;
        return false;
    }

    bool theory_trau::check_intersection_not_empty(ptr_vector<expr> const& v, expr_ref_vector const& allvars){
        for (unsigned i = 0; i < v.size(); ++i)
            if (allvars.contains(v[i]))
                return true;
        return false;
    }

    void theory_trau::fetch_guessed_exprs_from_cache(UnderApproxState const& state, expr_ref_vector &guessed_exprs) {
        guessed_exprs.append(state.equalities);
        fetch_guessed_core_exprs(state.eq_combination, guessed_exprs, state.disequalities, state.str_int_bound);
    }

    void theory_trau::fetch_guessed_exprs_with_scopes(expr_ref_vector &guessed_eqs) {
        
        context& ctx = get_context();
        for (unsigned i = 0; i < mful_scope_levels.size(); ++i) {
            literal tmp = ctx.get_literal(mful_scope_levels[i].get());
            int assignLvl = ctx.get_assign_level(tmp);
            if (assignLvl >= 0)
                if (!m.is_not(mful_scope_levels[i].get()))
                    guessed_eqs.push_back(mful_scope_levels[i].get());
        }
    }

    void theory_trau::fetch_guessed_exprs_with_scopes(expr_ref_vector &guessed_eqs, expr_ref_vector &guessed_diseqs) {
        
        context& ctx = get_context();
        for (unsigned i = 0; i < mful_scope_levels.size(); ++i) {
            literal tmp = ctx.get_literal(mful_scope_levels[i].get());
            int assignLvl = ctx.get_assign_level(tmp);
            if (assignLvl >= 0) {
                if (!m.is_not(mful_scope_levels[i].get()))
                    guessed_eqs.push_back(mful_scope_levels[i].get());
                else
                    guessed_diseqs.push_back(mful_scope_levels[i].get());
            }
        }
    }

    void theory_trau::fetch_guessed_literals_with_scopes(literal_vector &guessedLiterals) {
        
        context& ctx = get_context();

        for (int i = 0; i < (int)mful_scope_levels.size(); ++i)
            if (!m.is_not(mful_scope_levels[i].get()))
            {
                literal tmp = ctx.get_literal(mful_scope_levels[i].get());
                STRACE("str", tout << __LINE__ << " guessedLiterals " << mk_pp(mful_scope_levels[i].get(), m) << std::endl;);
                guessedLiterals.push_back(tmp);
            }
    }

    void theory_trau::fetch_guessed_str_int_with_scopes(expr_ref_vector &guessed_eqs, expr_ref_vector &guessed_diseqs) {
        
        context& ctx = get_context();
        expr_ref_vector assignments(m);
        ctx.get_assignments(assignments);
        expr_ref_vector stored_eq(m);
        expr_ref_vector stored_diseq(m);

        expr* a0 = nullptr, *a1 = nullptr, *a2 = nullptr;
        for (const auto& s : assignments) {
            if (ctx.is_relevant(s)) {
                if (!m.is_not(s, a0)) {
                    app* a = to_app(s);
                    if (a->get_num_args() == 2 && m.is_eq(a, a1, a2) &&
                            ((u.str.is_stoi(a1)) || u.str.is_stoi(a2) || (u.str.is_itos(a1) || u.str.is_itos(a2)))) {
                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(s, m) << std::endl;);
                        if ((u.str.is_stoi(a1) || u.str.is_itos(a1)) && !stored_eq.contains(a1)) {
                            guessed_eqs.push_back(s);
                            stored_eq.push_back(a1);
                        }
                        else if ((u.str.is_stoi(a2) || u.str.is_itos(a2)) && !stored_eq.contains(a2)) {
                            guessed_eqs.push_back(s);
                            stored_eq.push_back(a2);
                        }
                    }
                }
                else if (to_app(s)->get_num_args() == 1){
                    app* a = to_app(a0);
                    if (a->get_num_args() == 2 && m.is_eq(a, a1, a2) &&
                        ((u.str.is_stoi(a1) || u.str.is_stoi(a2) || (u.str.is_itos(a1) || u.str.is_itos(a2))))) {
                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(s, m) << std::endl;);
                        if ((u.str.is_stoi(a1) || u.str.is_itos(a1)) &&
                            !stored_diseq.contains(a1)) {
                            guessed_diseqs.push_back(s);
                            stored_diseq.push_back(a1);
                        }
                        else if ((u.str.is_stoi(a2) || u.str.is_itos(a2)) && !stored_diseq.contains(a2)) {
                            guessed_diseqs.push_back(s);
                            stored_diseq.push_back(a2);
                        }
                    }
                }
            }
        }
    }

    const bool theory_trau::is_theory_str_term(expr *const e) const {
        
        return (m.get_sort(e) == m.mk_sort(m.mk_family_id("seq"), _STRING_SORT, 0, nullptr));
    }

    decl_kind theory_trau::get_decl_kind(expr *const e) const {
        return to_app(e)->get_decl_kind();
    }

    app * theory_trau::string_value_proc::mk_value(model_generator & mg, expr_ref_vector const &  values) {
        clock_t start_clock = clock();
        ast_manager & m = mg.get_manager();
        obj_map<enode, app *> m_root2value = mg.get_root2value();
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ":"  << mk_pp(node, m) << std::endl;);
        clock_t t = clock();
        for (int i = 0; i < (int)m_dependencies.size(); ++i){
            app* val = nullptr;
            if (m_root2value.find(m_dependencies[i].get_enode(), val)) {
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ":"  << mk_pp(m_dependencies[i].get_enode()->get_owner(), m) << std::endl;);
            }
            else
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ":"  << mk_pp(m_dependencies[i].get_enode()->get_owner(), m) << " no value " << std::endl;);
        }

        sort * str_sort = th.u.str.mk_string_sort();
        bool is_string = str_sort == m_sort;

        if (is_string) {
            int len_int = len;
            if (len_int != -1) {
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": len : " << len_int << std::endl;);
                if (non_fresh_var) {
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": important" << std::endl;);
                    if (len_int != -1) {
                        zstring strValue;
                        if (construct_string_from_array(mg, m_root2value, arr_node, len_int, strValue)) {
                        }
                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": value = \"" << strValue << "\"" << std::endl;);
                        return to_app(th.mk_string(strValue));
                    }
                }
                if (regex != nullptr) {
                    zstring strValue;
                    if (construct_string_from_array(mg, m_root2value, arr_node, len_int, strValue)) {
                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(node, m) << " " << strValue << std::endl;);
                        return to_app(th.mk_string(strValue));
                    }
                    if (fetch_value_from_dep_graph(mg, m_root2value, len_int, strValue)) {
                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(node, m) << " " << strValue << std::endl;);
                        return to_app(th.mk_string(strValue));
                    }
                    if (construct_string_from_regex(mg, len_int, m_root2value, strValue)) {
                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": regex value = \"" << strValue << "\"" << std::endl;);
                        return to_app(th.mk_string(strValue));
                    }
                }
                zstring strValue;
                STRACE("str", tout << __LINE__ <<  " current time used: " << ":  " << ((float)(clock() - start_clock))/CLOCKS_PER_SEC << std::endl;);
                construct_normally(mg, len_int, m_root2value, strValue);
                STRACE("str", tout << __LINE__ <<  " current time used: " << ":  " << ((float)(clock() - start_clock))/CLOCKS_PER_SEC << std::endl;);
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(node, m) << " " << strValue << std::endl;);
                return to_app(th.mk_string(strValue));
            }
            else {
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << mk_pp(node, m) << std::endl;);
                SASSERT(false);
            }
        }

        else {
            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": not string: "  << mk_pp(node, m) << std::endl;);
        }
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ":"  << mk_pp(node, m) << " " <<  ((float)(clock() - t))/CLOCKS_PER_SEC<< std::endl;);
        return node;
    }

    bool theory_trau::string_value_proc::construct_string_from_regex(model_generator &mg, int len_int, obj_map<enode, app *> const& m_root2value, zstring &str_value){
        vector<zstring> elements = collect_alternative_components(regex);
        if (th.u.re.is_union(regex)) {
            SASSERT(elements.size() > 0);
            for (unsigned i = 0; i < elements.size(); ++i) {
                if (elements[i].length() == (unsigned)len_int){
                    str_value = elements[i];
                    return true;
                }
            }

            return false;
        }
        else if (th.u.re.is_to_re(regex)) {
            SASSERT(elements.size() == 1);
            str_value = elements[0];
            return true;
        }
        else if (th.u.re.is_star(regex) || th.u.re.is_plus(regex)) {
            zstring value_str("");
            for (int i = 0; i < (int)elements.size(); ++i) {
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " "  << elements[i] << std::endl;);
            }
            if (create_string_with_length(elements, value_str, len_int)) {
                str_value = value_str;
                return true;
            }
            else
                return false;
        }
        return false;
    }

    bool theory_trau::string_value_proc::create_string_with_length(vector<zstring> const& elements, zstring &current_str, int remain_length){
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": current_str: "  << current_str << "; remain_length:" << remain_length << std::endl;);
        if (remain_length == 0)
            return true;

        for (const auto& s : elements) {
            if (s.length() <= (unsigned)remain_length) {
                int x = remain_length / s.length();
                int bak_len = current_str.length();
                for (int j = 0; j < x; ++j)
                    current_str  = current_str + s;
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": current_str: "  << current_str << "; remain_length:" << remain_length << " " << s << std::endl;);
                if (remain_length % s.length() == 0) {
                    return true;
                }
                else {
                    int tmpRemainLength = remain_length % s.length();
                    while ((int)current_str.length() > bak_len) {
                        if (create_string_with_length(elements, current_str, tmpRemainLength)) {
                            return true;
                        } else {
                            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": current_str: "  << current_str << "; remain_length:" << remain_length << " " << s << std::endl;);
                            current_str = current_str.extract(0, current_str.length() - s.length());
                            tmpRemainLength += s.length();
                        }
                    }
                }
            }
        }

        return false;
    }

    vector<zstring> theory_trau::string_value_proc::collect_alternative_components(expr* v){
        vector<zstring> result;
        collect_alternative_components(v, result);
        return result;
    }

    void theory_trau::string_value_proc::collect_alternative_components(expr* v, vector<zstring>& ret){
        expr *arg0 = nullptr, * arg1 = nullptr;
        if (th.u.re.is_to_re(v, arg0)){
            zstring tmpStr;
            th.u.str.is_string(arg0, tmpStr);
            ret.push_back(tmpStr);
        }
        else if (th.u.re.is_union(v, arg0, arg1)){
            collect_alternative_components(arg0, ret);
            collect_alternative_components(arg1, ret);
        }
        else if (th.u.re.is_star(v, arg0) || th.u.re.is_plus(v, arg0)) {
            collect_alternative_components(arg0, ret);
        }
        else if (th.u.re.is_range(v, arg0, arg1)){
            zstring start, finish;
            th.u.str.is_string(arg0, start);
            th.u.str.is_string(arg1, finish);
            SASSERT(start.length() == 1);
            SASSERT(finish.length() == 1);

            for (int i = start[0]; i <= (int)finish[0]; ++i){
                zstring tmp(i);
                ret.push_back(tmp);
            }
        }
        else if (th.u.re.is_concat(v)) {
            expr* tmp = is_regex_plus_breakdown(v);
            if (tmp != nullptr){
                return collect_alternative_components(tmp, ret);
            }
            else
                NOT_IMPLEMENTED_YET();
        }
        else {
            NOT_IMPLEMENTED_YET();
        }
    }

    expr* theory_trau::string_value_proc::is_regex_plus_breakdown(expr* e){
        expr* arg0 = nullptr, *arg1 = nullptr;
        if (th.u.re.is_concat(e, arg0, arg1)){
            expr *arg10 = nullptr;
            if (th.u.re.is_star(arg1, arg10)){
                if (arg10 == arg0)
                    return arg1;
            }

            expr *arg00 = nullptr;
            if (th.u.re.is_star(arg0, arg00)){
                if (arg00 == arg1)
                    return arg0;
            }
        }
        return nullptr;
    }

    bool theory_trau::string_value_proc::construct_normally(model_generator & mg, int len_int, obj_map<enode, app *> const& m_root2value, zstring& strValue){
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(node, mg.get_manager())  << ": NOT important" << std::endl;);
        if (len_int != -1) {
            // non root var
            bool constraint01 = !th.uState.eq_combination.contains(node);
            if (!th.dependency_graph.contains(node))
                th.dependency_graph.insert(node, {});
            bool constraint02 = th.dependency_graph[node].size() > 0;
            if (constraint01 || constraint02) {
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": case non root" << (constraint01 ? " true " : "false ") << (constraint02 ? " true " : "false ") << th.dependency_graph[node].size()<< std::endl;);
                if (!constraint02) {
                    int_vector val;
                    for (int i = 0; i < len_int; ++i)
                        val.push_back(-1);

                    if (th.u.str.is_concat(node))
                        construct_string(mg, node, m_root2value, val);

                    std::string ret = "";
                    for (int i = 0; i < len_int; ++i)
                        if (val[i] == -1) {
                            ret = ret + th.default_char;
                        } else
                            ret = ret + (char)val[i];

                    strValue = zstring(ret.c_str());
                    return to_app(th.mk_string(strValue));
                } else {
                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": case non root" << (constraint01 ? " true " : "false ") << (constraint02 ? " true " : "false ") << th.dependency_graph[node].size()<< std::endl;);
                    if (fetch_value_from_dep_graph(mg, m_root2value, len_int, strValue))
                        return to_app(th.mk_string(strValue));
                }
            }
            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": case root" << std::endl;);
            // root var
            int_vector val;
            for (int i = 0; i < len_int; ++i)
                val.push_back(-1);

            if (th.u.str.is_concat(node))
                construct_string(mg, node, m_root2value, val);
            if (th.uState.eq_combination.contains(node))
                for (const auto &eq : th.uState.eq_combination[node]) {
                    construct_string(mg, eq, m_root2value, val);
                }
            std::string ret = "";
            for (int i = 0; i < len_int; ++i)
                if (val[i] == -1) {
                    ret = ret + th.default_char;
                } else
                    ret = ret + (char)val[i];
            strValue = zstring(ret.c_str());
            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": value = " << ret << std::endl;);
            return to_app(th.mk_string(strValue));

        }
        else {
            SASSERT(false);
        }

        return false;
    }

    bool theory_trau::string_value_proc::construct_string_from_array(model_generator mg, obj_map<enode, app *> const& m_root2value, enode *arr, int len_int, zstring &val){
        SASSERT(arr->get_owner() != nullptr);
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(arr->get_owner(), mg.get_manager()) << " " << len_int << std::endl;);

        app* arr_val = nullptr;
        if (m_root2value.find(arr, arr_val)) {
            int_vector vValue (len_int, -1);

            func_decl * fd = to_func_decl(arr_val->get_parameter(0).get_ast());
            func_interp* fi = mg.get_model().get_func_interp(fd);

            unsigned num_entries = fi->num_entries();
            for (unsigned i = 0; i < num_entries; i++){
                func_entry const* fe = fi->get_entry(i);
                expr* k =  fe->get_arg(0);
                rational key;
                if (th.m_autil.is_numeral(k, key) && key.get_int32() >=0 ) {
                    expr* v =  fe->get_result();

                    rational value;
                    if (th.m_autil.is_numeral(v, value)) {
                        if (key.get_int32() < (int)vValue.size())
                            vValue[key.get_int32()] = value.get_int32();
                    }
                }
            }

            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << std::endl;);

            bool completed = true;
            zstring value;

            unsigned_set char_set;
            get_char_range(char_set);
            value = fill_chars(vValue, char_set, completed);
 ;
            val = value;

            // revise string basing on regex
            if (char_set.size() == 0) {
                if (regex != nullptr) {
                    if (!match_regex(regex, val)) {
                        vector<zstring> elements = collect_alternative_components(regex);
                        if (elements.size() == 1 && len_int % elements[0].length() == 0){
                            zstring new_str("");
                            create_string_with_length(elements, new_str, len_int);
                            val = new_str;
                            return true;
                        }
                        for (int i = 0; i < (int)value.length(); ++i) {
                            zstring tmp = val.extract(0, i);
                            if (!match_regex(regex, tmp)) {
                                int err_pos = i;
                                for (err_pos = i + 1; err_pos < (int)value.length(); ++err_pos)
                                    if (value[err_pos] != value[i]) {
                                        break;
                                    }

                                zstring working_str("");
                                if (i > 0)
                                    working_str = val.extract(0, i - 1);

                                zstring new_str("");
                                if (create_string_with_length(elements, new_str, err_pos - i + 1)) {
                                    val = working_str + new_str + value.extract(i + new_str.length() - 1, value.length() - (i + new_str.length() - 1));
                                }
                                else
                                    NOT_IMPLEMENTED_YET();
                                i = i + new_str.length() - 1;
                            }
                        }
                    }
                }
            }

            if (completed == false) {
                return false;
            }

            return true;
        }

        return false;
    }

    bool theory_trau::string_value_proc::get_char_range(unsigned_set & char_set){
        if (regex != nullptr) {
            // special case for numbers
            vector<zstring> elements = collect_alternative_components(regex);
            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " s: " << mk_pp(regex, th.get_manager()) << " " << elements.size() << std::endl;);
            for (const auto& s : elements) {
                if (s.length() != 1) {
                    char_set.reset();
                    return false;
                } else {
                    char_set.insert(s[0]);
                }
            }
            return true;
        }
        return false;
    }

    zstring theory_trau::string_value_proc::fill_chars(int_vector const& vValue, unsigned_set const& char_set, bool &completed){
        std::string value;

        for (unsigned i = 0; i < vValue.size(); ++i) {
            if (char_set.size() > 0){
                char tmp = (char)vValue[i];
                if (char_set.find(tmp) == char_set.end())
                    value = value + (char)(*(char_set.begin()));
                else
                    value = value + (char) vValue[i];
            }
            else {
                if (vValue[i] <= 0 || vValue[i] >= 128) {
                    value = value + th.default_char;
                    completed = false;
                } else
                    value = value + (char) vValue[i];
            }
        }
        return zstring(value.c_str());
    }

    void theory_trau::string_value_proc::construct_string(model_generator &mg, expr *eq, obj_map<enode, app *> const& m_root2value, int_vector &val){
        if (th.u.str.is_concat(eq)){
            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": sync"  << mk_pp(eq, th.get_manager()) << std::endl;);
            ptr_vector<expr> leafNodes;
            th.get_nodes_in_concat(eq, leafNodes);

            int sum = 0;
            for (int i = 0; i < (int)leafNodes.size(); ++i){
                if (th.is_non_fresh(leafNodes[i]) || th.u.str.is_string(leafNodes[i]) || th.is_regex_var(leafNodes[i])){
                    zstring leafVal;

                    if (get_str_value(th.get_context().get_enode(leafNodes[i]), m_root2value, leafVal)){
                        int len_int = leafVal.length();
                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": updating by: "  << mk_pp(leafNodes[i], th.get_manager())  << " = " << leafVal << std::endl;);
                        for (int j = sum; j < sum + len_int; ++j) {
                            if (val[j] == -1) {
                                val[j] = leafVal[j - sum];
                            } else {
                                if (val[j] != (int) leafVal[j - sum]) {
                                    STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": inconsistent @" << j << " \"" << leafVal << "\" " << mk_pp(leafNodes[i], th.get_manager()) << std::endl;);
                                }
                            }
                        }
                        sum = sum + len_int;
                    }
                    else {
                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": cannot get string: "  << mk_pp(leafNodes[i], th.get_manager()) << std::endl;);
                    }
                }
                else {
                    int len_int = -1;
                    if (get_int_value(mg, th.get_context().get_enode(th.mk_strlen(leafNodes[i])), m_root2value,
                                      len_int)){
                        sum += len_int;
                        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": sum = "  << sum << std::endl;);
                    }
                    else {
                        SASSERT(false);
                    }
                }
            }
        }
    }

    bool theory_trau::string_value_proc::fetch_value_from_dep_graph(model_generator &mg, obj_map<enode, app *> const& m_root2value, int len, zstring &value){
        // component var
        for (const auto &ancestor : th.dependency_graph[node]) {
            STRACE("str",tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(ancestor, mg.get_manager()) << std::endl;);
            zstring ancestorValue;
            if (get_str_value(th.get_context().get_enode(ancestor), m_root2value, ancestorValue)) {
                if (th.u.str.is_concat(ancestor)) {
                    if (fetch_value_belong_to_concat(mg, ancestor, ancestorValue, m_root2value, len, value)) {
                        return true;
                    }
                }

                // find in its eq
                if (th.uState.eq_combination.contains(ancestor)) {
                    for (const auto &ancestor_i : th.uState.eq_combination[ancestor]) {
                        if (th.u.str.is_concat(ancestor_i)) {
                            if (fetch_value_belong_to_concat(mg, ancestor_i, ancestorValue, m_root2value, len, value)) {
                                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": value = " << value << std::endl;);
                                return true;
                            }
                        }
                    }
                }

            }
        }
        return false;
    }

    bool theory_trau::string_value_proc::fetch_value_belong_to_concat(model_generator &mg, expr *concat, zstring concatValue, obj_map<enode, app *> const& m_root2value, int len, zstring &value){
        if (th.u.str.is_concat(concat)){

            ptr_vector<expr> leafNodes;
            th.get_all_nodes_in_concat(concat, leafNodes);

            if (leafNodes.contains(node) || (linker != nullptr && leafNodes.contains(linker))) {
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": found in "  << mk_pp(concat, th.get_manager()) << std::endl;);
                expr* tmp = nullptr;
                if (leafNodes.contains(node))
                    tmp = node;
                else
                    tmp = linker;
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": found in "  << mk_pp(concat, th.get_manager()) << std::endl;);
                int prefix = find_prefix_len(mg, concat, tmp, m_root2value);
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": prefix = "  << prefix << std::endl;);
                value = concatValue.extract(prefix, len);
                return true;
            }
            return false;
        }
        return false;
    }

    int theory_trau::string_value_proc::find_prefix_len(model_generator &mg, expr *concat, expr *subNode, obj_map<enode, app *> const& m_root2value){

        if (th.u.str.is_concat(concat)){
            int prefix = 0;
            find_prefix_len(mg, concat, subNode, m_root2value, prefix);
            return prefix;
        }
        else
            SASSERT(false);

        return -1;
    }

    bool theory_trau::string_value_proc::find_prefix_len(model_generator &mg, expr *concat, expr *subNode, obj_map<enode, app *> const& m_root2value, int &prefix){
        if (concat == subNode)
            return true;
        expr* e1 = nullptr, *e2 = nullptr;
        if (th.u.str.is_concat(concat, e1, e2)){
            if (!find_prefix_len(mg, e1, subNode, m_root2value, prefix)) {
                if (!find_prefix_len(mg, e2, subNode, m_root2value, prefix))
                    return false;
                else
                    return true;
            }
            else
                return true;
        }
        else {
            int subLen = -1;
            zstring val_str;
            if (th.u.str.is_string(concat, val_str)){
                prefix += val_str.length();
            }
            else if (get_int_value(mg, th.get_context().get_enode(th.mk_strlen(concat)), m_root2value, subLen)) {
                prefix += subLen;
            }
            else {
                SASSERT(false);
            }
        }
        return false;
    }

    bool theory_trau::string_value_proc::get_int_value(model_generator &mg, enode *n, obj_map<enode, app *> const& m_root2value, int &value){
        app* val = nullptr;
        if (m_root2value.find(n->get_root(), val)) {
            rational valInt;
            if (th.m_autil.is_numeral(val, valInt)) {
                value = valInt.get_int32();
                return true;
            }
            else {
                return false;
            }
        }
        else {
            // query int theory
            expr *value_ral = th.query_theory_arith_core(n->get_owner(), mg);
            if (value_ral != nullptr) {

                rational tmp;
                if (th.m_autil.is_numeral(value_ral, tmp)) {
                    value = tmp.get_int32();
                    return true;
                }
                else
                SASSERT(false);
            }
            return false;
        }
    }

    bool theory_trau::string_value_proc::get_str_value(enode *n, obj_map<enode, app *> const& m_root2value, zstring &value){
        app* val = nullptr;
        if (m_root2value.find(n->get_root(), val)) {
            zstring valStr;
            if (th.u.str.is_string(val, valStr)) {
                value = valStr;
                return true;
            }
            else {
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": cannot get string: "  << mk_pp(n->get_owner(), th.get_manager()) << std::endl;);
                return false;
            }
        }
        else {
            zstring tmp;
            if (th.u.str.is_string(n->get_owner(), tmp)) {
                value = tmp;
                return true;
            }
            STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": cannot get string: "  << mk_pp(n->get_owner(), th.get_manager()) << std::endl;);
            return false;
        }
    }

    bool theory_trau::string_value_proc::match_regex(expr *a, zstring b){
        expr* tmp = th.u.re.mk_to_re(th.u.str.mk_string(b));
        return match_regex(a, tmp);
    }

    bool theory_trau::string_value_proc::match_regex(expr *a, expr *b) {
        expr* intersection = th.u.re.mk_inter(a, b);
        eautomaton *au01 = get_automaton(intersection);
        return !au01->is_empty();
    }

    eautomaton* theory_trau::string_value_proc::get_automaton(expr* re) {
        eautomaton* result = nullptr;
        if (th.m_re2aut.find(re, result)) {
            return result;
        }

        result = th.m_mk_aut(re);
        th.m_automata.push_back(result);
        th.m_re2aut.insert(re, result);
        th.m_res.push_back(re);
        return result;
    }

    bool can_split(int boundedFlat, int boundSize, int pos, std::string frame, vector<std::string> &flats) {
        if ((int)flats.size() == boundedFlat)
            return false;

        for (int size = 1; size <= boundSize; ++size) { /* size of a flat */
            std::string flat = frame.substr(pos, size);
            flats.push_back(flat); /* add to stack */
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
                if (can_split(boundedFlat, boundSize, tmpPos, frame, flats))
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
     * Pre-Condition: x_i == 0 --> x_i+1 == 0
     */
    bool theory_trau::Arrangment::is_possible_arrangement(pair_expr_vector const &lhs_elements, pair_expr_vector const &rhs_elements) const {
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


    void theory_trau::Arrangment::print(std::string msg){
        if (msg.length() > 0)
        STRACE("str", tout << msg << std::endl;);

        for (unsigned int i = 0; i < left_arr.size(); ++i)
        STRACE("str", tout << left_arr[i] << " ";);

        STRACE("str", tout << std::endl;);
        for (unsigned int i = 0; i < right_arr.size(); ++i)
        STRACE("str", tout << right_arr[i] << " ";);
        STRACE("str", tout <<  std::endl;);
    }
}
