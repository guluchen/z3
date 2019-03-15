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
#include "smt/theory_seq_empty.h"
#include "smt/theory_str.h"
#include "smt/theory_lra.h"
/* TODO:
 *  1. better algorithm for checking solved form
 *  2. on-the-fly over-approximation
 *  3. better algorithm for computing state transform
 */

namespace smt {



    theory_str::theory_str(ast_manager& m, const theory_str_params& params)
            : theory(m.mk_family_id("seq")),
              m_params(params),
            /* Options */

              opt_DisableIntegerTheoryIntegration(false),
              opt_ConcatOverlapAvoid(true),
            /* Internal setup */
              search_started(false),
              m_autil(m),
              m_arrayUtil(m),
              u(m),
              m_scope_level(0),
              m_rewrite(m),
              m_seq_rewrite(m),
              m_trail(m),
              m_delayed_axiom_setup_terms(m),
              m_delayed_assertions_todo(m),
              m_persisted_axiom_todo(m),
              contains_map(m),
              string_int_conversion_terms(m),
              totalCacheAccessCount(0),
              m_fresh_id(0),
              m_trail_stack(*this),
              m_find(*this),
              m_mk_aut(m),
              m_res(m){
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
            STRACE("str", tout << "already attached to theory var" << std::endl;);
            return n->get_th_var(get_id());
        } else {
            theory_var v = theory::mk_var(n);
            m_find.mk_var();
            STRACE("str", tout << "new theory var v#" << v << " find " << m_find.find(v) << std::endl;);
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
    app * theory_str::mk_value_helper(app * n) {
        if (u.str.is_string(n)) {
            return n;
        } else if (u.str.is_concat(n)) {
            // recursively call this function on each argument
            SASSERT(n->get_num_args() == 2);
            expr * a0 = n->get_arg(0);
            expr * a1 = n->get_arg(1);

            app * a0_conststr = mk_value_helper(to_app(a0));
            app * a1_conststr = mk_value_helper(to_app(a1));

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

    model_value_proc *theory_str::mk_value(enode *const n, model_generator& mg) {
        ast_manager& m = get_manager();
        app_ref owner{m};
        owner = n->get_owner();
        // if the owner is not internalized, it doesn't have an e-node associated.
        SASSERT(get_context().e_internalized(owner));
        STRACE("str", tout << "mk_value for: " << mk_ismt2_pp(owner, m) << " (sort "
                           << mk_ismt2_pp(m.get_sort(owner), m) << ")" << std::endl;);
        rational vLen;
        if (get_len_value(n->get_owner(), vLen)) {
            if (vLen.get_int32() == 0)
                return alloc(expr_wrapper_proc, u.str.mk_string(zstring("")));
            else
                STRACE("str", tout << " len = " << vLen << std::endl;);
        }

        app * val = mk_value_helper(owner);
        if (val != nullptr) {
            return alloc(expr_wrapper_proc, val);
        } else {
        }
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
                TRACE("str", tout << __FUNCTION__ << ":" << mk_ismt2_pp(n1->get_owner(), m) << " = "
                           << mk_ismt2_pp(n2->get_owner(), m) << std::endl;);


 //       handle_equality(get_enode(x)->get_owner(), get_enode(y)->get_owner());

        // merge eqc **AFTER** handle_equality
        m_find.merge(x, y);
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

        if (u.str.is_concat(to_app(lhs)) && u.str.is_concat(to_app(rhs))) {
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
//        if (!new_eq_check(lhs, rhs)) {
//            return;
//        }

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

            for (const auto c2 : eqc_concat_rhs){
                expr* n3 = to_app(c2)->get_arg(0);
                expr* n4 = to_app(c2)->get_arg(1);
                if (eqn1.contains(n3)){
                    expr_ref_vector litems(m);
                    litems.push_back(ctx.mk_eq_atom(lhs, rhs));
                    litems.push_back(ctx.mk_eq_atom(n1, n3));

                    expr_ref implyL(mk_and(litems), m);
                    assert_implication(implyL, ctx.mk_eq_atom(n2, n4));
                }

                if (eqn2.contains(n4)){
                    expr_ref_vector litems(m);
                    litems.push_back(ctx.mk_eq_atom(lhs, rhs));
                    litems.push_back(ctx.mk_eq_atom(n2, n4));

                    expr_ref implyL(mk_and(litems), m);
                    assert_implication(implyL, ctx.mk_eq_atom(n1, n3));
                }
            }
        }
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
            for (unsigned i = 0; i < argVec.size(); ++i) {
                bool vArgHasEqcValue = false;
                expr * vArg = get_eqc_value(argVec[i], vArgHasEqcValue);
                resultAst = mk_concat(resultAst, vArg);
            }
            TRACE("str", tout << mk_ismt2_pp(node, m) << " is simplified to " << mk_ismt2_pp(resultAst, m) << std::endl;);

            if (in_same_eqc(node, resultAst)) {
                TRACE("str", tout << "SKIP: both concats are already in the same equivalence class" << std::endl;);
            } else {
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

        TRACE("str", tout << "string-eq length-eq axiom: "
                          << mk_ismt2_pp(premise, m) << " -> " << mk_ismt2_pp(conclusion, m) << std::endl;);
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
                STRACE("str", tout << __FUNCTION__ << ": " << mk_pp(eqc_nn1, m) << " and " << mk_pp(eqc_nn2, m) << " can be equal" << std::endl;);
                // inconsistency check: value
                if (!can_two_nodes_eq(eqc_nn1, eqc_nn2)) {
                    STRACE("str", tout << "inconsistency detected: " << mk_pp(eqc_nn1, m) << " cannot be equal to " << mk_pp(eqc_nn2, m) << std::endl;);
                    expr_ref to_assert(mk_not(m, ctx.mk_eq_atom(eqc_nn1, eqc_nn2)), m);

                    expr_ref_vector litems(m);
                    if (lhs != eqc_nn1)
                        litems.push_back(ctx.mk_eq_atom(lhs, eqc_nn1));
                    if (rhs != eqc_nn2)
                        litems.push_back(ctx.mk_eq_atom(rhs, eqc_nn2));

                    expr_ref implyL(mk_and(litems), m);
                    assert_implication(implyL, mk_not(m, ctx.mk_eq_atom(lhs, rhs)));
                    // this shouldn't use the integer theory at all, so we don't allow the option of quick-return
                    return false;
                }
                eqc_nn2 = get_eqc_next(eqc_nn2);
            } while (eqc_nn2 != rhs);
            eqc_nn1 = get_eqc_next(eqc_nn1);
        } while (eqc_nn1 != lhs);

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
        return true;
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
            STRACE("str", tout << "Concat : "<< mk_pp(ts0, m) << " . " << mk_pp(ts1, m) << " --> " << mk_pp(concat, m) << std::endl;);

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
        TRACE("str", tout << __FUNCTION__ << ": "<< mk_pp(concat, m) << " --- " << mk_pp(new_concat, m) << std::endl;);

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
                    litems.push_back(ctx.mk_eq_atom(concat, value));
                    expr_ref implyL(mk_and(litems), m);
                    assert_axiom(mk_not(implyL));
                    STRACE("str", tout << "assert: " << mk_ismt2_pp(mk_not(implyL), m) << std::endl;);
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
                    litems.push_back(ctx.mk_eq_atom(concat, value));
                    expr_ref implyL(mk_and(litems), m);
                    assert_axiom(mk_not(implyL));
                    STRACE("str", tout << "assert: " << mk_ismt2_pp(mk_not(implyL), m) << std::endl;);
                }
            }

        }
        else {

            // TODO propagation
            expr* overApproxConcat = construct_concat_overapprox(new_concat, litems);
            for (expr_ref_vector::iterator itor = eqConcatList.begin(); itor != eqConcatList.end(); itor++) {
                if (regex_in_var_reg_str_map.contains(*itor)) {
                    STRACE("str", tout << __FUNCTION__ << ": " << mk_ismt2_pp(*itor, m) << std::endl;);

                    for (std::set<zstring>::iterator strItor = regex_in_var_reg_str_map[*itor].begin();
                            strItor != regex_in_var_reg_str_map[*itor].end(); strItor++) {
                        zstring regStr = *strItor;
                        std::pair<expr *, zstring> key1 = std::make_pair(*itor, regStr);
                        if (regex_in_bool_map.find(key1) != regex_in_bool_map.end()) {
                            expr *boolVar = regex_in_bool_map[key1]; // actually the RegexIn term
                            app *a_regexIn = to_app(boolVar);
                            expr *regexTerm = a_regexIn->get_arg(1);
                            expr *intersection = u.re.mk_inter(regexTerm, overApproxConcat);
                            m_trail.push_back(intersection);

                            eautomaton *au01 = get_automaton(intersection);
                            bool matchRes = !au01->is_empty();
                            STRACE("str", tout << mk_ismt2_pp(new_concat, m) << " = " << mk_ismt2_pp(regexTerm, m) << " : "
                                               << (matchRes ? "yes: " : "no: ") << regStr << std::endl;);

                            if (!matchRes) {
                                litems.push_back(boolVar);
                                if (*itor != concat)
                                    litems.push_back(ctx.mk_eq_atom(concat, *itor));

                                expr_ref implyL(mk_and(litems), m);
                                STRACE("str", tout << "assert: " << mk_ismt2_pp(mk_not(implyL), m) << std::endl;);
                                assert_axiom(mk_not(implyL));
                                litems.pop_back();
                                if (*itor != concat)
                                    litems.pop_back();
                            }

                        }
                    }
                }
                else {
                    expr* eqNode = construct_concat_overapprox(*itor, litems);
                    expr *intersection = u.re.mk_inter(eqNode, overApproxConcat);
                    m_trail.push_back(intersection);

                    eautomaton *au01 = get_automaton(intersection);
                    bool matchRes = !au01->is_empty();
                    STRACE("str", tout << mk_ismt2_pp(new_concat, m) << " = " << mk_ismt2_pp(eqNode, m) << " : "
                                       << (matchRes ? "yes: " : "no: ") << std::endl;);
                    if (!matchRes) {
                        if (*itor != concat)
                            litems.push_back(ctx.mk_eq_atom(concat, *itor));

                        expr_ref implyL(mk_and(litems), m);
                        STRACE("str", tout << "assert: " << mk_ismt2_pp(mk_not(implyL), m) << std::endl;);
                        assert_axiom(mk_not(implyL));
                        if (*itor != concat)
                            litems.pop_back();
                    }
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

    expr* theory_str::construct_concat_overapprox(expr* nn, expr_ref_vector & litems){
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
            nullptr;

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
                    bool tmpFound = false;
                    if (regex_in_var_reg_str_map.contains(el)) {
                        std::set<zstring>::iterator strItor = regex_in_var_reg_str_map[el].begin();
                        for (; strItor != regex_in_var_reg_str_map[el].end(); strItor++) {
                            zstring regStr = *strItor;
                            std::pair<expr *, zstring> key1 = std::make_pair(el, regStr);
                            if (regex_in_bool_map.find(key1) != regex_in_bool_map.end()) {
                                expr *boolVar = regex_in_bool_map[key1]; // actually the RegexIn term
                                app *a_regexIn = to_app(boolVar);
                                expr *regexTerm = a_regexIn->get_arg(1);
                                lhs = u.re.mk_concat(lhs, regexTerm);
                                m_trail.push_back(lhs);
                                tmpFound = true;
                                lastIsSigmaStar = false;
                                litems.push_back(boolVar);
                                break;
                            }
                        }
                        if (!tmpFound) {
                            if (!lastIsSigmaStar) {
                                lhs = u.re.mk_concat(lhs, u.re.mk_full_seq(regex_sort));
                                m_trail.push_back(lhs);
                            }
                            lastIsSigmaStar = true;
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
        context & ctx = get_context();

        expr *const n1 = get_enode(x)->get_owner();
        expr *const n2 = get_enode(y)->get_owner();
                STRACE("str", tout << __FUNCTION__ << ": " << mk_ismt2_pp(n1, m) << " != "
                           << mk_ismt2_pp(n2, m) << std::endl;);

//        instantiate_str_diseq_length_axiom(n1, n2);
        // len x != len y --> true
        // len x == len y == 0 --> false

        // n1 = n11 . n12 . n13
        // n2 = n21 . n22. n23
        // n11 = n21
        // len n12 = len n22 = 1 && n12 != n22

        rational n1Len, n2Len;
        bool n1Len_exists = get_len_value(n1, n1Len);
        bool n2Len_exists = get_len_value(n2, n2Len);

        if (n1Len_exists && n1Len == 0)
            return;

        if (n2Len_exists && n2Len == 0)
            return;

        if (n1Len_exists && n2Len_exists && n1Len == n2Len && n1Len == 1){
            // handle in under-approx
            STRACE("str", tout << "len " <<  mk_pp(n1, m) << " = " << n1Len << " == len " <<  mk_pp(n2, m) << " = " << n2Len << std::endl;);
            return;
        }

        if (n1Len_exists && n2Len_exists && n1Len != n2Len){
            // trivial
            STRACE("str", tout << "len " <<  mk_pp(n1, m) << " = " << n1Len << " != len " <<  mk_pp(n2, m) << " = " << n2Len << std::endl;);
            return;
        }

        if (u.str.is_string(n1) || u.str.is_string(n2))
            return;

        expr_ref n11(mk_str_var("n11"), m);
        expr_ref n12(mk_str_var("n12"), m);
        expr_ref n13(mk_str_var("n13"), m);

        expr_ref n21(mk_str_var("n21"), m);
        expr_ref n22(mk_str_var("n22"), m);
        expr_ref n23(mk_str_var("n23"), m);

        expr_ref_vector and_item(m);
        and_item.push_back(ctx.mk_eq_atom(n1, mk_concat(n11, mk_concat(n12, n13))));
        and_item.push_back(ctx.mk_eq_atom(mk_strlen(n12), mk_int(1)));

        and_item.push_back(ctx.mk_eq_atom(n2, mk_concat(n21, mk_concat(n22, n23))));
        and_item.push_back(ctx.mk_eq_atom(mk_strlen(n22), mk_int(1)));

        and_item.push_back(ctx.mk_eq_atom(n11, n21));

        expr_ref thenBranch(mk_and(and_item));
        expr_ref elseBranch(mk_not(m, ctx.mk_eq_atom(n1, n2)), m);

        expr_ref topLevelCond(ctx.mk_eq_atom(mk_strlen(n1), mk_strlen(n2)), m);

        expr_ref finalAxiom(m.mk_ite(topLevelCond, thenBranch, elseBranch), m);
        get_context().get_rewriter()(finalAxiom);
        assert_axiom(finalAxiom);
        STRACE("str", tout << "\t not " << mk_ismt2_pp(n1, m) << " = "
                           << mk_ismt2_pp(n2, m) << " --> " << mk_pp(finalAxiom.get(), m) << std::endl;);
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

        if (ex_sort == str_sort) {
            enode *n = ctx.get_enode(ex);
            instantiate_basic_string_axioms(n);
            if (is_app(ex)) {
                app *ap = to_app(ex);
                if (u.str.is_concat(ap)) {
                    instantiate_concat_axiom(n);
                }
            }
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

    void theory_str::init_search_eh() {
        context & ctx = get_context();
        m_re2aut.reset();
        m_automata.reset();
        m_res.reset();

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
    //    propagate();

        STRACE("str", tout << "search started" << std::endl;);
        search_started = true;
    }

    void theory_str::relevant_eh(app *const n) {
        (void) n;
    }

    void theory_str::assign_eh(bool_var v, const bool is_true) {
    }

    void theory_str::push_scope_eh() {
        TRACE("str", tout << __FUNCTION__ << ": at level " << m_scope_level << std::endl;);
        m_scope_level += 1;
        m_trail_stack.push_scope();
        theory::push_scope_eh();
    }

    void theory_str::pop_scope_eh(const unsigned num_scopes) {
        TRACE("str", tout << __FUNCTION__ << ": at level " << m_scope_level << " pop " << num_scopes << std::endl;);
        m_scope_level -= num_scopes;
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
        STRACE("str", tout << "pop m_basicstr_axiom_todo" << num_scopes << " to " << m_scope_level << std::endl;);
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
        return FC_DONE;
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




    app* theory_str::createSelectOperator(expr* x, expr* y){
        ptr_vector<expr> sel_args;
        ast_manager &m = get_manager();
        sel_args.push_back(x);
        sel_args.push_back(y);
        context & ctx   = get_context();
        app* tmp = m_arrayUtil.mk_select(sel_args.size(), sel_args.c_ptr());
        ctx.internalize(tmp, false);
        return tmp;
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
//        context & ctx = get_context();
//        while (can_propagate()) {
//            TRACE("str", tout << std::endl;);
//
//            while(true) {
//                // this can potentially recursively activate itself
//                unsigned start_count = m_basicstr_axiom_todo.size();
//                ptr_vector<enode> axioms_tmp(m_basicstr_axiom_todo);
//                for (auto const& el : axioms_tmp) {
//                    instantiate_basic_string_axioms(el);
//                }
//                unsigned end_count = m_basicstr_axiom_todo.size();
//                if (end_count > start_count) {
//                    STRACE("str", tout << "new basic string axiom terms added -- checking again" << std::endl;);
//                    continue;
//                } else {
//                    break;
//                }
//            }
//            m_basicstr_axiom_todo.reset();
//
//
//            for (auto const& el : m_concat_axiom_todo) {
//                instantiate_concat_axiom(el);
//            }
//            m_concat_axiom_todo.reset();
//            m_concat_eval_todo.reset();

//            for (auto el : m_delayed_axiom_setup_terms) {
//                // I think this is okay
//                ctx.internalize(el, false);
//                set_up_axioms(el);
//            }
//            m_delayed_axiom_setup_terms.reset();
//
//            for (expr * a : m_persisted_axiom_todo) {
//                assert_axiom(a);
//            }
//            m_persisted_axiom_todo.reset();
//
//            if (search_started) {
//                for (auto const& el : m_delayed_assertions_todo) {
//                    assert_axiom(el);
//                }
//                m_delayed_assertions_todo.reset();
//            }
//        }
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
            STRACE("str", tout <<  __FUNCTION__ << ":\"" << strconst.encode().c_str() << "\"" << std::endl;);
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
        len_x_plus_len_y = m_autil.mk_add(len_x, len_y);
        SASSERT(len_x_plus_len_y);

        // finally assert equality between the two subexpressions
        app * eq = m.mk_eq(len_xy, len_x_plus_len_y);
        SASSERT(eq);
        assert_axiom(eq);
    }

    app * theory_str::mk_strlen(expr * e) {
        return u.str.mk_length(e);
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

        STRACE("str", tout << __FUNCTION__ << ":" << name << " at scope level " << m_scope_level << std::endl;);

        sort * string_sort = u.str.mk_string_sort();
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

    expr * theory_str::mk_concat(expr * n1, expr * n2) {
        context &ctx = get_context();
        ast_manager &m = get_manager();
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ": " << mk_pp(n1, m) << " " << mk_pp(n2, m)  << std::endl;);
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
            expr_ref lenAssert(ctx.mk_eq_atom(concat_length, m_autil.mk_add(items.size(), items.c_ptr())), m);
            assert_axiom(lenAssert);
        }
        return concatAst;
    }

    app * theory_str::mk_int(int n) {
        return m_autil.mk_numeral(rational(n), true);
    }

    app * theory_str::mk_int(rational & q) {
        return m_autil.mk_numeral(q, true);
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
        ast_manager &m = get_manager();
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

            ast_manager & m = get_manager();
            return e->get_th_var(get_id());
        }
        return null_theory_var;
    }

    app * theory_str::get_ast(theory_var v) {
        return get_enode(v)->get_owner();
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
        ast_manager & m = get_manager();
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


    void theory_str::track_variable_scope(expr * var) {
        if (internal_variable_scope_levels.find(m_scope_level) == internal_variable_scope_levels.end()) {
            internal_variable_scope_levels[m_scope_level] = obj_hashtable<expr>();
        }
        internal_variable_scope_levels[m_scope_level].insert(var);
    }

    void theory_str::assert_implication(expr * premise, expr * conclusion) {
        ast_manager & m = get_manager();
        TRACE("str", tout << __FUNCTION__ << ":" << mk_ismt2_pp(premise, m) << " -> " << mk_ismt2_pp(conclusion, m) << std::endl;);
        expr_ref axiom(m.mk_or(mk_not(m, premise), conclusion), m);
        assert_axiom(axiom);
    }

    void theory_str::init_model(model_generator& mg) {
        STRACE("str", tout << "initializing model..." << std::endl;);
        ast_manager& m = get_manager();
        context& ctx = get_context();
        for (const auto& n : variable_set){
            STRACE("str", tout << "var " << mk_pp(n, m););
            rational vLen;
            if (get_len_value(n, vLen))
                STRACE("str", tout << " len = " << vLen << std::endl;);
            STRACE("str", tout << std::endl;);
        }

        for (const auto& n : arrMap){
            STRACE("str", tout << "var " << mk_pp(n.first, m) << " --> " << mk_pp(n.second, m) << std::endl;);
            rational vLen;
            if (get_len_value(n.first, vLen)){
                STRACE("str", tout << "var " << mk_pp(n.first, m) << " has len = " <<  vLen << std::endl;);
                for (int i = 0; i < vLen.get_int32(); ++i){
                    expr* val_i = createSelectOperator(n.second, m_autil.mk_int(i));
                    STRACE("str", tout << "\t var " << mk_pp(val_i, m) << std::endl;);
                    rational v_i;
                    if (get_arith_value(val_i, v_i)) {
                        STRACE("str", tout << " val_" << i << " = " << v_i << std::endl;);
                    }
                    else {
                        rational l_vi, r_vi;
                        if (lower_num_bound(val_i, l_vi)){
                            STRACE("str", tout << " low val_" << i << " = " << l_vi << std::endl;);
                        }
                        if (upper_num_bound(val_i, r_vi)){
                            STRACE("str", tout << " upper val_" << i << " = " << r_vi << std::endl;);
                        }
                    }
                }

            }
            STRACE("str", tout << std::endl;);
        }
    }


    void theory_str::assert_axiom(expr *const e) {
        if (e == nullptr || get_manager().is_true(e)) return;

        ast_manager& m = get_manager();
        context& ctx = get_context();
        expr_ref ex{e, m};
        STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << mk_pp(e, m) << std::endl;);
        if (!ctx.b_internalized(ex)) {
            ctx.internalize(ex, false);
        }
        literal lit(ctx.get_literal(ex));
        ctx.mark_as_relevant(lit);
        ctx.mk_th_axiom(get_id(), 1, &lit);
    }



    decl_kind theory_str::get_decl_kind(expr *const e) const {
        return to_app(e)->get_decl_kind();
    }



}
