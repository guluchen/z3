#ifndef _THEORY_TRAU_H_
#define _THEORY_TRAU_H_

#include <list>
#include <set>
#include <stack>
#include <map>
#include <vector> 
#include "ast/arith_decl_plugin.h"
#include "ast/array_decl_plugin.h"
#include "ast/ast_pp.h"
#include "smt/params/theory_str_params.h"
#include "smt/proto_model/value_factory.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/seq_decl_plugin.h"
#include "smt/smt_model_generator.h"
#include "smt/smt_theory.h"
#include "util/hashtable.h"
#include "util/scoped_vector.h"
#include "util/scoped_ptr_vector.h"
#include "util/trail.h"
#include "util/union_find.h"
#include "smt/smt_arith_value.h"

#define LOCALSPLITMAX 20
#define SUMFLAT 100000000
#define EMPTYFLAT 9999999

#define REGEX_CODE -10000
#define MINUSZERO 999

#define LENPREFIX "len_"
#define ARRPREFIX "arr_"
#define ITERSUFFIX "__iter"
#define ZERO "0"
#define REGEXSUFFIX "_10000"

namespace smt {

    namespace str {
        using expr_pair = std::pair<expr_ref, expr_ref>;
        typedef hashtable<std::pair<expr*, expr*>, obj_ptr_pair_hash<expr, expr>, default_eq<std::pair<expr*, expr*>> > expr_pair_set;
    }

    class theory_trau : public theory {
        ast_manager&                    m;
        int                             m_scope_level;
        scoped_vector<expr_ref>         mful_scope_levels;
        const theory_str_params&        m_params;
        scoped_vector<str::expr_pair>   m_we_expr_memo;
        scoped_vector<str::expr_pair>   m_wi_expr_memo;
        scoped_vector<str::expr_pair>   membership_memo;
        scoped_vector<str::expr_pair>   non_membership_memo;

        typedef union_find<theory_trau>     th_union_find;
        typedef trail_stack<theory_trau>    th_trail_stack;
        struct zstring_hash_proc {
            unsigned operator()(zstring const & s) const {
                return string_hash(s.encode().c_str(), static_cast<unsigned>(s.length()), 17);
            }
        };
        typedef map<zstring, expr*, zstring_hash_proc, default_eq<zstring> >    string_map;
        typedef hashtable<zstring, zstring_hash_proc,default_eq<zstring> >      string_set;
        typedef hashtable<int, int_hash, default_eq<int> >                      int_set;
        typedef hashtable<char, unsigned_hash, default_eq<char> >               unsigned_set;
        typedef hashtable<expr*, obj_ptr_hash<expr>, ptr_eq<expr> >             expr_set;
        typedef std::pair<expr*, int>                                           expr_int;
        typedef old_svector<expr_int>                                           pair_expr_vector;


        class Arrangment{
        public:
            int_vector left_arr;
            int_vector right_arr;

            Arrangment(int_vector const& _left_arr, int_vector const& _right_arr):left_arr(_left_arr), right_arr(_right_arr){}
            ~Arrangment() {}
            void add_left(int number) {left_arr.push_back(number);}
            void add_right(int number) {right_arr.push_back(number);}
            bool can_split(int boundedFlat, int boundSize, int pos, std::string frame, vector<std::string> &flats);
            bool is_possible_arrangement(pair_expr_vector const &lhs_elements, pair_expr_vector const &rhs_elements) const;
            void print(std::string msg = "");
        };

        typedef map<std::pair<int, int>, vector<Arrangment>, pair_hash<int_hash, int_hash>, default_eq<std::pair<int, int>>> arrangment_map;
        class UnderApproxState{
        public:
            obj_map<expr, ptr_vector<expr>> eq_combination;
            obj_map<expr, int> non_fresh_vars;
            expr_ref_vector equalities;
            expr_ref_vector disequalities;
            bool reassertEQ = false;
            bool reassertDisEQ = false;
            int eqLevel = -1;
            int diseqLevel = -1;
            expr_ref_vector asserting_constraints;
            rational str_int_bound;

            UnderApproxState(ast_manager &m) : equalities(m), disequalities(m), asserting_constraints(m){
                eq_combination.reset();
            }

            UnderApproxState(ast_manager &m, int _eqLevel, int _diseqLevel,
                             obj_map<expr, ptr_vector<expr>> const& _eq_combination,
                             obj_map<expr, int> const& _non_fresh_vars,
                            expr_ref_vector const& _equalities,
                            expr_ref_vector const& _disequalities,
                            rational _str_int_bound):
                            eq_combination(_eq_combination),
                            non_fresh_vars(_non_fresh_vars),
                            equalities(m),
                            disequalities(m),
                            eqLevel(_eqLevel),
                            diseqLevel(_diseqLevel),
                            asserting_constraints(m),
                            str_int_bound(_str_int_bound){
                asserting_constraints.reset();
                equalities.reset();
                equalities.append(_equalities);
                disequalities.reset();
                disequalities.append(_disequalities);
                reassertEQ = true;
                reassertDisEQ = true;
            }

            UnderApproxState clone(ast_manager &m){
                UnderApproxState tmp(m, eqLevel, diseqLevel, eq_combination, non_fresh_vars, equalities, disequalities, str_int_bound);
                tmp.add_asserting_constraints(asserting_constraints);
                reassertEQ = true;
                reassertDisEQ = true;
                return tmp;
            }

            void reset_eq(){
                STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ <<  ": eqLevel = " << eqLevel << "; diseqLevel = " << diseqLevel << std::endl;);
                eqLevel = -1;
                reassertEQ = false;
            }

            void reset_diseq(){
                STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ <<  ": eqLevel = " << eqLevel << "; diseqLevel = " << diseqLevel << std::endl;);
                diseqLevel = -1;
                reassertDisEQ = false;
            }

            UnderApproxState&  operator=(const UnderApproxState& other){
                eqLevel = other.eqLevel;
                diseqLevel = other.diseqLevel;
                eq_combination = other.eq_combination;
                non_fresh_vars = other.non_fresh_vars;
                equalities.reset();
                equalities.append(other.equalities);
                disequalities.reset();
                disequalities.append(other.disequalities);
                asserting_constraints.reset();
                reassertEQ = true;
                reassertDisEQ = true;
                for (unsigned i = 0; i < other.asserting_constraints.size(); ++i)
                    asserting_constraints.push_back(other.asserting_constraints[i]);

                STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << ":  eq_combination: " << other.eq_combination.size() << " --> " << eq_combination.size() << std::endl;);
                return *this;
            }

            void add_asserting_constraints(expr_ref_vector _assertingConstraints){
                for (unsigned i = 0; i < _assertingConstraints.size(); ++i)
                    asserting_constraints.push_back(_assertingConstraints.get(i));
            }

            void add_asserting_constraints(expr_ref assertingConstraint){
                asserting_constraints.push_back(assertingConstraint);
            }

            bool operator==(const UnderApproxState state){
                obj_map<expr, ptr_vector<expr>> _eq_combination = state.eq_combination;
                if (_eq_combination.size() != eq_combination.size()) {
                    STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << ": " << _eq_combination.size() << " vs " << eq_combination.size() <<  std::endl;);
                    return false;
                }

                for (const auto& v : non_fresh_vars)
                    if (!state.non_fresh_vars.contains(v.m_key)) {
                        return false;
                    }

                for (const auto& n : eq_combination) {
                    if (_eq_combination.contains(n.m_key)) {
                        return false;
                    }
                    ptr_vector<expr> tmp = _eq_combination[n.m_key];
                    for (const auto &e : n.get_value()) {

                        if (!tmp.contains(e)) {
                            return false;
                        }
                        else {
                            // it is ok if some elements missing because if its size = 0
                        }
                    }
                }
                STRACE("str", tout << __LINE__ <<  " *** " << __FUNCTION__ << ": Equal. " << std::endl;);
                return true;
            }
        };

        class string_value_proc : public model_value_proc {
            theory_trau&                     th;
            sort*                           m_sort;
            svector<model_value_dependency> m_dependencies;
            app*                            node;
            enode*                          arr_node;
            bool                            non_fresh_var;
            expr*                           regex;
            expr*                           linker;
            int                             len;
        public:

            string_value_proc(theory_trau& th, sort * s, app* node, bool _non_fresh_var, enode* arr_node, expr* regex, int len = -1):
                    th(th), m_sort(s), node(node), arr_node(arr_node), non_fresh_var(_non_fresh_var), regex(regex), len(len){
            }

            string_value_proc(theory_trau& th, sort * s, app* node, bool _non_fresh_var, expr* regex, int len = -1):
                    th(th), m_sort(s), node(node), non_fresh_var(_non_fresh_var), regex(regex), len(len){
            }

            ~string_value_proc() override {}

            void add_entry(unsigned num_args, enode * const * args, enode * value) {
                SASSERT(num_args > 0);
                for (unsigned i = 0; i < num_args; i++)
                    m_dependencies.push_back(model_value_dependency(args[i]));
                m_dependencies.push_back(model_value_dependency(value));
            }
            void add_entry(enode * value){
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << ":"  << mk_pp(node, th.get_manager()) << " --> " << mk_pp(value->get_owner(), th.get_manager()) << std::endl;);
                m_dependencies.push_back(model_value_dependency(value));
            }
            void set_linker(expr * link){
                linker = link;
            }
            void get_dependencies(buffer<model_value_dependency> & result) override {
                result.append(m_dependencies.size(), m_dependencies.c_ptr());
            }

            app * mk_value(model_generator & mg, expr_ref_vector const & values) override ;
            bool construct_string_from_regex(model_generator &mg, int len_int, obj_map<enode, app *> const& m_root2value, zstring &str_value);
            bool create_string_with_length(vector<zstring> const& elements, zstring &current_str, int remain_length);
            vector<zstring> collect_alternative_components(expr* v);
            void collect_alternative_components(expr* v, vector<zstring>& ret);
            expr* is_regex_plus_breakdown(expr* e);
            bool construct_normally(model_generator & mg, int len_int, obj_map<enode, app *> const& m_root2value, zstring& strValue);
            bool construct_string_from_array(model_generator mg, obj_map<enode, app *> const& m_root2value, enode *arr, int len_int, zstring &val);
            bool get_char_range(unsigned_set & char_set);
            zstring fill_chars(int_vector const& vValue, unsigned_set const& char_set, bool &completed);
            void construct_string(model_generator &mg, expr *eq, obj_map<enode, app *> const& m_root2value, int_vector &val);
            bool fetch_value_from_dep_graph(model_generator &mg, obj_map<enode, app *> const& m_root2value, int len, zstring &value);
            bool fetch_value_belong_to_concat(model_generator &mg, expr *concat, zstring concatValue, obj_map<enode, app *> const& m_root2value, int len, zstring &value);
            int find_prefix_len(model_generator &mg, expr *concat, expr *subNode, obj_map<enode, app *> const& m_root2value);
            bool find_prefix_len(model_generator &mg, expr *concat, expr *subNode, obj_map<enode, app *> const& m_root2value, int &prefix);
            bool get_int_value(model_generator &mg, enode *n, obj_map<enode, app *> const& m_root2value, int &value);
            bool get_str_value(enode *n, obj_map<enode, app *> const& m_root2value, zstring &value);
            bool match_regex(expr *a, zstring b);
            bool match_regex(expr *a, expr *b);
            eautomaton* get_automaton(expr* re);
        };


    public:
        theory_trau(ast_manager& m, const theory_str_params& params);
        ~theory_trau() override;
        void display(std::ostream& os) const override;
        th_trail_stack& get_trail_stack() { return m_trail_stack; }
        void merge_eh(theory_var, theory_var, theory_var v1, theory_var v2) {}
        void after_merge_eh(theory_var r1, theory_var r2, theory_var v1, theory_var v2) { }
        void unmerge_eh(theory_var v1, theory_var v2) {}

    protected:
        void init(context *ctx) override;
        bool internalize_atom(app *atom, bool gate_ctx) override;
        bool internalize_term(app *term) override;
        theory_var mk_var(enode *n) override;
        theory *mk_fresh(context *) override { return alloc(theory_trau, get_manager(), m_params); }

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
        app * mk_value_helper(app * n, model_generator& mg);
        model_value_proc *mk_value(enode *n, model_generator& mg) override;
        bool is_non_fresh(expr *n);
        bool is_non_fresh(expr *n, int &val);
        bool is_regex_var(expr* n, expr* &regexExpr);
        bool is_regex_var(expr* n);
        bool is_regex_concat(expr* n);
        expr_ref_vector get_dependencies(expr *n);

        void add_theory_assumptions(expr_ref_vector& assumptions) override;
        lbool validate_unsat_core(expr_ref_vector& unsat_core) override;
        void new_eq_eh(theory_var, theory_var) override;
            /*
            * x . "abc" = x . y && y = "abc"
            */
            bool is_trivial_eq_concat(expr* x, expr* y);
        void new_diseq_eh(theory_var, theory_var) override;
            bool is_inconsistent_inequality(expr* lhs, expr* rhs);
            bool is_not_added_diseq(expr_ref n1, expr_ref n2);
            void assert_cached_diseq_state();
            /*
             * Add an axiom of the form:
             * len lhs != len rhs -> lhs != rhs
             * len lhs == 0 == len rhs --> lhs == rhs
             */
            void instantiate_str_diseq_length_axiom(expr * lhs, expr * rhs, bool& skip);
                expr* handle_trivial_diseq(expr * e, zstring value);
        string_set extract_const(expr* e, int lvl = 0);
        void create_pq();
        void init_search_eh() override;
        void relevant_eh(app *n) override;
        void assign_eh(bool_var v, bool is_true) override;
        void push_scope_eh() override;
        void pop_scope_eh(unsigned num_scopes) override;
        void reset_eh() override;
        final_check_status final_check_eh() override;
            bool eval_str_int();
            bool eval_disequal_str_int();
                bool eq_to_i2s(expr* n, expr* &i2s);

            /*
             * Check agreement between integer and string theories for the term a = (str.to-int S).
             * Returns true if axioms were added, and false otherwise.
             */
            bool eval_str2int(app * a);
                rational string_to_int(zstring str, bool &valid);
                int eval_invalid_str2int(expr* e, expr* &eq_node);
            bool eval_int2str(app * a);
            bool init_chain_free(obj_map<expr, int> &non_fresh_vars, obj_map<expr, ptr_vector<expr>> &eq_combination);
                bool analyze_upper_bound_str_int();
                rational log_10(rational n);
                rational ten_power(rational n);
            bool refined_init_chain_free(obj_map<expr, int> &non_fresh_vars, obj_map<expr, ptr_vector<expr>> &eq_combination);
                void refine_not_contain_vars(obj_map<expr, int> &non_fresh_vars, obj_map<expr, ptr_vector<expr>> const& eq_combination);
                bool is_not_important(expr* haystack, zstring needle, obj_map<expr, ptr_vector<expr>> const& eq_combination, obj_map<expr, int> const& non_fresh_vars);
                bool appear_in_eq(expr* haystack, zstring needle, ptr_vector<expr> const& s, obj_map<expr, int> const& non_fresh_vars);
                bool eq_in_list(expr* n, ptr_vector<expr> const& nodes);
                bool can_omit(expr* lhs, expr* rhs, zstring needle);
                bool appear_in_other_eq(expr* root, zstring needle, obj_map<expr, ptr_vector<expr>> const& eq_combination);
            bool is_completed_branch(bool &addAxiom, expr_ref_vector &diff);
            void update_state();
            bool propagate_eq_combination(obj_map<expr, ptr_vector<expr>> const& eq_combination);
            bool is_notContain_consistent(obj_map<expr, ptr_vector<expr>> const& eq_combination);
                bool is_notContain_consistent(expr* lhs, expr* rhs, expr* core);
                bool is_notContain_const_consistent(expr* lhs, zstring containKey, expr_ref premise);

            bool not_contain(expr* haystack, expr* needle, expr* &realHaystack);
            bool does_contain(expr* haystack, expr* needle, expr* &realHaystack);

            bool parikh_image_check(obj_map<expr, ptr_vector<expr>> const& eq_combination);
                bool equal_parikh(expr* nn, expr* n);
                    void get_parikh_from_strs(zstring s, map<char, int, unsigned_hash, default_eq<char>> &img);
                    bool eq_parikh(map<char, int, unsigned_hash, default_eq<char>> const& lhs, map<char, int, unsigned_hash, default_eq<char>> const& rhs);
                bool same_prefix_same_parikh(expr* nn, expr* n);
                bool can_match(zstring value, expr* n);
                void not_contain_string_in_expr(expr* n, expr_ref_vector &constList);
                bool agree_on_not_contain(expr* n, expr* key);
                int get_lower_bound_image_in_expr(expr* n, expr* str);
                bool get_image_in_expr(expr* n, expr_ref_vector &constList);

            int get_actual_trau_lvl();
                bool at_same_eq_state(UnderApproxState const& state, expr_ref_vector &diff);
                bool at_same_diseq_state(expr_ref_vector const& curr_eq, expr_ref_vector const& curr_diseq, expr_ref_vector const& prev_diseq);
                bool is_empty_comparison(expr* e);
        bool review_starting_ending_combination(obj_map<expr, ptr_vector<expr>> const& eq_combination);
            unsigned_set collect_char_domain_from_concat();
            unsigned_set collect_char_domain_from_eqmap(obj_map<expr, ptr_vector<expr>> const& eq_combination);
            bool handle_contain_family(obj_map<expr, ptr_vector<expr>> const& eq_combination);
                expr* create_equations_over_contain_vars(expr* x, expr* y);
            bool handle_charAt_family(obj_map<expr, ptr_vector<expr>> const& eq_combination);
                bool are_equal_exprs(expr* x, expr* y);
            obj_hashtable<expr> get_eqc_roots();
            void add_theory_aware_branching_info(expr * term, double priority, lbool phase);


            bool propagate_concat();
            bool propagate_value(expr_ref_vector & concat_set);
            bool propagate_length(expr_ref_vector & varSet, expr_ref_vector & concatSet);
                void collect_var_concat(expr * node, expr_ref_vector & vars, expr_ref_vector & concats);
                void get_unique_non_concat_nodes(expr * node, expr_ref_vector & argSet);
                bool propagate_length_within_eqc(expr * var);
            bool underapproximation(
                    obj_map<expr, ptr_vector<expr>> const& eq_combination,
                    obj_map<expr, int> & non_fresh_vars,
                    expr_ref_vector const& diff);
                bool assert_state(expr_ref_vector const& guessed_eqs, expr_ref_vector const& guessed_diseqs);
                bool handle_str_int();
                    void handle_str2int(expr* num, expr* str);
                    void handle_int2str(expr* num, expr* str);
                        rational get_max_s2i(expr* n);
                        bool quickpath_str2int(expr* num, expr* str, bool cached = true);
                        bool quickpath_int2str(expr* num, expr* str, bool cached = true);
                        expr* unroll_str2int(expr* n);
                        expr* unroll_str_int(expr* num, expr* str);
                        expr* valid_str_int(expr* str);
                        expr* lower_bound_str_int(expr* num, expr* str);
                        expr* lower_bound_int_str(expr* num, expr* str);
                        expr* fill_0_1st_loop(expr* num, expr* str);
                            bool is_char_at(expr* str);
                void print_eq_combination(obj_map<expr, ptr_vector<expr>> const& eq_combination, int line = -1);
                bool is_equal(UnderApproxState const& preState, UnderApproxState const& currState);
                    bool are_some_empty_vars_omitted(expr* n, ptr_vector<expr> const& v);
                bool is_equal(expr_ref_vector const& corePrev, expr_ref_vector const& coreCurr);
            bool underapproximation_cached();
            void init_underapprox(obj_map<expr, ptr_vector<expr>> const& eq_combination, obj_map<expr, int> &non_fresh_vars);
                void mk_and_setup_arr(expr* v, obj_map<expr, int> &non_fresh_vars);
                void setup_str_int_arr(expr* v, int start);
                void setup_str_const(zstring val, expr* arr, expr* premise = nullptr);
                expr* setup_regex_var(expr* var, expr* rexpr, expr* arr, rational bound, expr* prefix);
                    expr* setup_char_range_arr(expr* e, expr* arr, rational bound, expr* prefix);
                void create_notcontain_map();
                void create_const_set();
                char setup_default_char(unsigned_set const& included_chars, unsigned_set const& exclude_chars);
                unsigned_set init_excluded_char_set();
                unsigned_set init_included_char_set();
                void create_appearance_map(obj_map<expr, ptr_vector<expr>> const& eq_combination);
                void setup_flats();
                bool should_use_flat();
            void init_underapprox_cached();

            void handle_diseq_notcontain(bool cached = false);
                void handle_disequalities();
                void handle_disequalities_cached();

            bool review_not_contain(expr* lhs, expr* needle, obj_map<expr, ptr_vector<expr>> const& eq_combination);
                expr* remove_empty_in_concat(expr* s);
                bool review_notcontain_trivial(expr* lhs, expr* needle);
            bool review_disequalities_not_contain(obj_map<expr, ptr_vector<expr>> const& eq_combination);
                bool review_disequality(expr* lhs, expr* rhs, obj_map<expr, ptr_vector<expr>> const& eq_combination);
                bool review_disequality_trivial(expr* lhs, expr* rhs);
                    void handle_disequality(expr *lhs, expr *rhs);
                    void handle_disequality_const(expr *lhs, zstring rhs);
                    void handle_disequality_var(expr *lhs, expr *rhs);
                void handle_not_contain();
                void handle_not_contain_cached();
                    void handle_not_contain(expr *lhs, expr *rhs, bool cached = false);
                    void handle_not_contain_var(expr *lhs, expr *rhs, expr *premise, bool cached = false);
                    void handle_not_contain_const(expr *lhs, zstring rhs, expr *premise, bool cached = false);
                    bool is_contain_equality(expr* n);
                    bool is_contain_equality(expr* n, expr* &contain);
                    bool is_trivial_contain(zstring s);
                void  init_connecting_size(obj_map<expr, ptr_vector<expr>> const& eq_combination, obj_map<expr, int> &non_fresh_vars, bool prep = true);
                    void static_analysis(obj_map<expr, ptr_vector<expr>> const& eq_combination);
            bool convert_equalities(obj_map<expr, ptr_vector<expr>> const& eq_combination,
                                           obj_map<expr, int> & non_fresh_vars,
                                           expr* premise);
                bool is_long_equality(ptr_vector<expr> const& eqs);
                expr* convert_other_equalities(ptr_vector<expr> const& eqs, obj_map<expr, int> const& non_fresh_vars);
                expr* convert_long_equalities(expr* var, ptr_vector<expr> const& eqs, obj_map<expr, int> &non_fresh_vars);
                expr* convert_const_nonfresh_equalities(expr* var, ptr_vector<expr> const& eqs, obj_map<expr, int> const& non_fresh_vars);
                void convert_regex_equalities(expr* regexExpr, expr* var, obj_map<expr, int> const& non_fresh_vars, expr_ref_vector &assertedConstraints, bool &axiomAdded);
                expr* const_contains_key(zstring c, expr* pre_contain, expr* key, rational len);
                void assert_breakdown_combination(expr* e, expr* premise, expr_ref_vector &assertedConstraints, bool &axiomAdded);
                void assert_breakdown_combination(expr* e, expr* var);
                void negate_context();
                void negate_equalities();
                void negate_context(expr* e);
                void negate_context(expr_ref_vector const& v);
                expr* find_equivalent_variable(expr* e);
                bool is_internal_var(expr* e);
                bool is_internal_regex_var(expr* e, expr* &regex);
                bool is_internal_regex_var(expr* e);
                bool is_splitable_regex(expr* e);
                /*
                * (abc)*__XXX -> abc
                */
                zstring parse_regex_content(zstring str);
                zstring parse_regex_content(expr* str);
                expr_ref_vector combine_const_str(expr_ref_vector const& v);
                    bool isRegexStr(zstring str);
                    bool isUnionStr(zstring str);

                expr_ref_vector parse_regex_components(expr* reg);

                    /*
                    * (a) | (b) --> {a, b}
                    */
                    vector<zstring> collect_alternative_components(zstring str);
                    expr_ref_vector collect_alternative_components(expr* v);
                    bool collect_alternative_components(expr* v, expr_ref_vector& ret);
                    bool collect_alternative_components(expr* v, vector<zstring>& ret);
                    int find_correspond_right_parentheses(int leftParentheses, zstring str);

                string_set collect_strs_in_membership(expr* v);
                void collect_strs_in_membership(expr* v, string_set &ret);
                    expr* remove_star_in_star(expr* reg);
                    bool contain_star(expr* reg);
                zstring getStdRegexStr(expr* regex);
                void setup_encoded_chars(unsigned_set &s);
            /*
             * convert lhs == rhs to SMT formula
             */
            expr* equality_to_arith(pair_expr_vector const& lhs_elements, pair_expr_vector const& rhs_elements, obj_map<expr, int> const& non_fresh_variables, int p = PMAX);
                expr* equality_to_arith_ordered(pair_expr_vector const& lhs_elements, pair_expr_vector const& rhs_elements, obj_map<expr, int> const& non_fresh_variables, int p);
                zstring create_string_representation(pair_expr_vector const& lhs_elements, pair_expr_vector const& rhs_elements);
            /*
             * lhs: size of the lhs
             * rhs: size of the rhs
             * lhs_elements: elements of lhs
             * rhs_elements: elements of rhs
             *
             * Pre-Condition: x_i == 0 --> x_i+1 == 0
             *
             */
            expr_ref_vector arrange(pair_expr_vector const& lhs_elements, pair_expr_vector const& rhs_elements, obj_map<expr, int> const& non_fresh_variables, int p = PMAX);
            void get_arrangements(pair_expr_vector const& lhs_elements, pair_expr_vector const& rhs_elements, obj_map<expr, int> const& non_fresh_variables, vector<Arrangment> &possibleCases);
            void update_possible_arrangements(pair_expr_vector const& lhs_elements, pair_expr_vector const& rhs_elements, vector<Arrangment> const& tmp, vector<Arrangment> &possibleCases);

            /*
             *
             */
            Arrangment create_arrangments_manually(pair_expr_vector const& lhs_elements, pair_expr_vector const& rhs_elements);

            /*
             * a_1 + a_2 + b_1 + b_2 = c_1 + c_2 + d_1 + d_2 ---> SMT
             */
            expr* to_arith(int p, int_vector const& left_arr, int_vector const& right_arr, pair_expr_vector const& lhs_elements,
                            pair_expr_vector const& rhs_elements,
                            obj_map<expr, int> const& non_fresh_variables);
                expr* to_arith_others(bool (&checkLeft)[10000], bool (&checkRight)[10000], int p,
                        int_vector const& left_arr,
                        int_vector const& right_arr,
                        pair_expr_vector const& lhs_elements,
                        pair_expr_vector const& rhs_elements,
                        obj_map<expr, int> const& non_fresh_variables);
                expr* to_arith_emptyflats(bool (&checkLeft)[10000], bool (&checkRight)[10000],
                                          int_vector const& left_arr,
                                          int_vector const& right_arr,
                                          pair_expr_vector const& lhs_elements,
                                          pair_expr_vector const& rhs_elements);
                expr* to_arith_right(bool (&checkLeft)[10000], bool (&checkRight)[10000], int p,
                                     int_vector const& left_arr,
                                     int_vector const& right_arr,
                                     pair_expr_vector const& lhs_elements,
                                     pair_expr_vector const& rhs_elements,
                                     obj_map<expr, int> const& non_fresh_variables);
                expr* to_arith_left(bool (&checkLeft)[10000], bool (&checkRight)[10000], int p,
                                    int_vector const& left_arr,
                                    int_vector const& right_arr,
                                    pair_expr_vector const& lhs_elements,
                                    pair_expr_vector const& rhs_elements,
                                    obj_map<expr, int> const& non_fresh_variables);
                void insert_top(expr_int const& e, pair_expr_vector &v);
            /*
             * Flat = Flat
             * size = size && it = it  ||
             * size = size && it = 1
             */
            expr* gen_constraint01(
                    expr_int a, expr_int b,
                    int pMax,
                    obj_map<expr, int> const& non_fresh_variables,
                    bool optimizing);
            pair_expr_vector init_expr_vector(expr_int p);
            vector<zstring> init_zstring_vector(zstring p);
                void gen_constraint01_const_var(
                        expr_int a, expr_int b,
                        obj_map<expr, int> const& non_fresh_variables,
                        bool optimizing,
                        expr_ref_vector &result);

                void gen_constraint01_const_const(
                        expr_int a, expr_int b,
                        bool optimizing,
                        expr *nameA,
                        expr_ref_vector &result);

                expr* gen_constraint01_regex_head(expr_int a, expr_int b, expr *nameA);
                expr* gen_constraint01_regex_tail(expr_int a, expr_int b, expr *nameA);
                expr* gen_constraint01_regex_regex(expr_int a, expr_int b, expr *nameA);
                expr* gen_constraint01_const_const(expr_int a, expr_int b, expr *nameA);

                void gen_constraint01_var_var(
                        expr_int a, expr_int b,
                        int pMax,
                        obj_map<expr, int> const& non_fresh_variables,
                        bool optimizing,
                        expr *nameA,
                        expr_ref_vector &result);

            expr* gen_constraint_var_var(
                    expr_int a,
                    expr_int b,
                    int pMax,
                    rational bound);

            expr* gen_constraint_flat_var(
                    expr_int a,
                    pair_expr_vector const& elements,
                    int pos,
                    int pMax,
                    rational bound);

            expr* gen_constraint_flat_flat(
                    expr_int a,
                    pair_expr_vector const& elements,
                    int pos,
                    int pMax,
                    rational bound,
                    bool skip_init = false);
            int lcd(int x, int y);
            bool match_regex(expr* a, zstring b);
            bool match_regex(expr* a, expr* b);
            /*
             * Flat = sum (flats)
             */
            expr* gen_constraint02(
                    expr_int a,
                    pair_expr_vector const& elements,
                    int pMax,
                    obj_map<expr, int> const& non_fresh_variables,
                    bool optimizing);

                bool gen_constraint02_const_regex(expr_int a,
                                                  pair_expr_vector const& elements,
                                                  int pMax,
                                                  obj_map<expr, int> const& non_fresh_variables,
                                                  bool optimizing,
                                                  expr_ref_vector &result);

                bool generate_constraint02_var(expr_int a,
                                                    pair_expr_vector const& elements,
                                                    obj_map<expr, int> const& non_fresh_variables,
                                                    bool optimizing,
                                                    expr_ref_vector &result);

                bool is_reg_union(expr* n);
                /*
                * Input: split a string
                * Output: SMT
                */
                expr* gen_constraint_non_fresh_var_const(
                        expr_int a, /* const || regex */
                        pair_expr_vector const& elements, /* const + non_fresh_ var */
                        int_vector const& split,
                        obj_map<expr, int> const& non_fresh_variables,
                        bool optimizing,
                        int pMax);

                    /*
                    *
                    */
                    expr* lengthConstraint_tonon_fresh_VarConstraint(
                            expr_int a, /* const || regex */
                            pair_expr_vector const& elements,
                            expr_ref_vector const& subElements,
                            int currentPos,
                            int subLength,
                            obj_map<expr, int> const& non_fresh_variables,
                            bool optimizing,
                            int pMax);

                        /*
                        *
                        */
                        expr_ref positional_non_fresh_var_in_array(
                                expr_int a, /* const or regex */
                                pair_expr_vector const& elements, /* have non_fresh_ var */
                                int var_pos,
                                int var_length,
                                obj_map<expr, int> const& non_fresh_variables,
                                bool optimizing,
                                int pMax);
                /*
                 * Input: split a string
                 * Output: SMT
                 */
                expr_ref_vector gen_constraint_without_non_fresh_vars(
                        expr_int a, /* const || regex */
                        pair_expr_vector const& elements, /* no non_fresh_ var */
                        int_vector const& split,
                        bool optimizing);
                /*
                 *
                 */
                expr* unroll_non_fresh_variable(
                        expr_int a, /* non_fresh_ variable */
                        pair_expr_vector const& elements, /* contain const */
                        obj_map<expr, int> const& non_fresh_variables,
                        bool optimizing,
                        int pMax = PMAX);
                    /*
                     * Generate constraints for the case
                     * X = T . "abc" . Y . Z
                     * constPos: position of const element
                     * return: (or (and length header = i && X_i = a && X_[i+1] = b && X_[i+2] = c))
                     */
                    expr_ref handle_positional_subconst_in_array(
                            expr_int a, // non_fresh_ var
                            pair_expr_vector const& elements,
                            int constPos,
                            bool optimizing,
                            int pMax = PMAX);

                        /*
                        * Generate constraints for the case
                        * X = T . "abc"* . Y . Z
                        * regexPos: position of regex element
                        * return: forAll (i Int) and (i < |abc*|) (y[i + |T|] == a | b | c)
                        */
                        expr_ref handle_positional_regex_in_array(
                                expr_int a, // non_fresh_ var
                                pair_expr_vector const& elements,
                                int regexPos,
                                bool optimizing,
                                int pMax = PMAX,
                                expr *extraConstraint = NULL/* length = ? */
                        );

                        /*
                        * Generate constraints for the case
                        * X = T . "abc" . Y . Z
                        * constPos: position of const element
                        * return: (or (and length header = i && X_i = a && X_[i+1] = b && X_[i+2] = c))
                        */
                        expr_ref handle_positional_const_in_array(
                                expr_int a,
                                pair_expr_vector const& elements,
                                int constPos,
                                zstring value, /* value of regex */
                                int start, int finish,
                                bool optimizing,
                                int pMax = PMAX,
                                expr *extraConstraint = NULL /* length = ? */);

                    /*
                    * non_fresh_ = a + non_fresh_ + b
                    */
                    expr* handle_non_fresh_non_fresh_array(
                            expr_int a,
                            pair_expr_vector const& elements,
                            int pos,
                            int bound,
                            bool optimizing,
                            int pMax = PMAX);

                /*
                 *
                 */
                expr* gen_constraint_non_fresh_var(
                        expr_int a, /* const or regex */
                        pair_expr_vector const& elements, /* have non_fresh_ var, do not have const */
                        obj_map<expr, int> const& non_fresh_variables,
                        bool optimizing,
                        int pMax);

                expr* unroll_regex_non_fresh_variable(
                        expr_int const& a, /* const or regex */
                        expr_int const& b,
                        int pMax,
                        int part_cnt,
                        int max_len,
                        expr* sub_len,
                        expr* prefix_lhs,
                        expr* prefix_rhs);

                expr* unroll_var_non_fresh_variable(
                        expr_int a, /* const or regex */
                        pair_expr_vector const& elements, /* have non_fresh_ var, do not have const */
                        int pMax,
                        int pos,
                        int part_cnt);

                expr* unroll_const_variable(
                        expr_int a, /* const or regex */
                        expr_int b,
                        int pMax,
                        int max_len,
                        expr* sub_len,
                        expr* prefix_lhs,
                        expr* prefix_rhs);

                expr* unroll_const_non_fresh_variable_str2int(
                        expr_int a, /* const or regex */
                        expr_int b,
                        int max_len,
                        expr* sub_len,
                        expr* prefix_lhs,
                        expr* prefix_rhs);

                expr* unroll_const_non_fresh_variable(
                        expr_int a, /* const or regex */
                        expr_int b,
                        int pMax,
                        int max_len,
                        expr* sub_len,
                        expr* prefix_lhs,
                        expr* prefix_rhs);

                expr* gen_regex_non_fresh_variable(
                        expr_int a, /* const or regex */
                        pair_expr_vector const& elements, /* have non_fresh_ var, do not have const */
                        obj_map<expr, int> const& non_fresh_variables,
                        int pMax,
                        int pos,
                        int part_cnt,
                        expr* sub_len,
                        expr* prefix_rhs);
                expr* gen_regex_regex(
                    expr_int a, /* const or regex */
                    pair_expr_vector const& elements, /* have non_fresh_ var, do not have const */
                    obj_map<expr, int> const& non_fresh_variables,
                    int pMax,
                    int pos);

                /*
                 * elements[pos] is a non_fresh_.
                 * how many parts of that non_fresh_ variable are in the const | regex
                 */
                expr* find_partsOfnon_fresh_variablesInAVector(int pos, pair_expr_vector const& elements, int &partCnt);
                /*
                * pre elements + pre fix of itself
                */
                expr* leng_prefix_lhs(expr_int a, pair_expr_vector const& elements, int pos, bool optimizing, bool unrollMode);

                /*
                *  pre fix of itself
                */
                expr* leng_prefix_rhs(expr_int a, /* var */ bool unrollMode);

                /*
                 * 0: No const, No non_fresh_ var
                * 1: const		No non_fresh_ var
                * 2: no const, non_fresh_ var
                * 3: have both
                */
                int choose_split_type(pair_expr_vector const& elements, obj_map<expr, int> const& non_fresh_variables, expr* lhs);

                /*
                * Input: constA and a number of flats
                * Output: all possible ways to split constA
                */
                vector<int_vector > collect_splits(expr_int lhs, pair_expr_vector const& elements, bool optimizing);
                    bool not_contain_check(expr* e, pair_expr_vector const& elements);
                    bool const_vs_regex(expr* reg, pair_expr_vector const& elements);
                    bool const_vs_str_int(expr* e, pair_expr_vector const& elements, expr* &extra_assert);
                        expr* find_i2s(expr* e);
                    bool length_base_split(expr* e, pair_expr_vector const& elements);
                /*
                * textLeft: length of string
                * nMax: number of flats
                * pMax: size of a flat
                *
                * Pre-Condition: 1st flat and n-th flat must be greater than 0
                * Output: of the form 1 * 1 + 1 * 0 + 1 * 0 + 1 * 0 + 1 * 0 + 1 * 0 + 1 * 0 + 1 * 0 + 1 * 3 + 2 * 3 = 10
                */
                void collect_const_splits(
                        int pos,
                        zstring str, /* const */
                        int pMax,
                        pair_expr_vector const& elements,
                        int_vector currentSplit,
                        vector<int_vector > &allPossibleSplits
                );
                    /*
                     * (a)|(b | c) --> {a, b, c}
                     */
                    string_set get_regex_components(zstring s);
                    /*
                    * (a) --> a
                    */
                    void remove_parentheses(zstring &s);
                /*
                * (a|b|c)*_xxx --> range <a, c>
                */
                vector<std::pair<int, int>> collect_char_range(expr* a);
                void collect_char_range(expr* a, vector<bool> &chars);
                bool feasible_const_split(zstring str, pair_expr_vector const &elements, int_vector const &currentSplit, int bound);
            /*
             * Given a flat,
             * generate its size constraint
             */
            expr* get_var_size(expr_int const& a);
            /*
             *
             */
            std::string gen_flat_iter(expr_int const& a);
            expr* get_flat_iter(expr_int const& a);
            /*
             * Given a flat,
             * generate its size constraint
             */
            std::string gen_flat_size(expr_int const& a);
            expr* get_var_flat_size(expr_int const& a);

            /*
             *
             */
            app* createEqualOP(expr* x, expr* y);
            app* createMulOP(expr *x, expr *y);
            app* createModOP(expr* x, expr* y);
            app* createMinusOP(expr* x, expr* y);
            app* createAddOP(expr* x, expr* y);
            app* createAddOP(expr_ref_vector adds);
            app* createLessOP(expr* x, expr* y);
            app* createLessEqOP(expr* x, expr* y);
            app* createGreaterOP(expr* x, expr* y);
            app* createGreaterEqOP(expr* x, expr* y);
            app* createAndOP(expr_ref_vector ands);
            app* createOrOP(expr_ref_vector ors);
            app* createSelectOP(expr* x, expr* y);

            int optimized_lhs(
                    int i, int startPos, int j,
                    int_vector const& left_arr,
                    int_vector const& right_arr,
                    vector<std::pair<std::string, int>> const& lhs_elements,
                    vector<std::pair<std::string, int>> const& rhs_elements);

            int optimized_rhs(
                    int i, int startPos, int j,
                    int_vector const& left_arr,
                    int_vector const& right_arr,
                    vector<std::pair<std::string, int>> const& lhs_elements,
                    vector<std::pair<std::string, int>> const& rhs_elements);
            /*
             * Given a flat,
             * generate its array name
             */
            zstring gen_flat_arr(expr_int const& a);
            expr* get_var_flat_array(expr_int const& a);
            expr* get_var_flat_array(expr* e);
            expr* get_bound_str_int_control_var();
            expr* get_bound_p_control_var();
            expr* get_bound_q_control_var();

            app* createITEOP(expr* c, expr* t, expr* e);
            /*
            * First base case
            */
            void setup_0_0_general();
            /*
             * 2nd base case [0] = (sum rhs...)
             */
            void setup_0_n_general(int lhs, int rhs);
            /*
             * 2nd base case (sum lhs...) = [0]
             */
            void setup_n_0_general(int lhs, int rhs);
            /*
             * general case
             */
            void setup_n_n_general(int lhs, int rhs);
            vector<std::pair<std::string, int>> vectorExpr2vectorStr(pair_expr_vector const& v);
            std::string expr2str(expr* node);

            /*
             * Input: x . y
             * Output: flat . flat . flat . flat . flat . flat
             */
            pair_expr_vector create_equality(expr* node, bool unfold = true);
            pair_expr_vector create_equality(ptr_vector<expr> const& list, bool unfold = true);
            pair_expr_vector create_equality_final(ptr_vector<expr> const& list, bool unfold = true);
                void create_internal_int_vars(expr* v);
                void setup_str_int_len(expr* e, int start);
                void reuse_internal_int_vars(expr* v);
            unsigned findMaxP(ptr_vector<expr> const& v);

            /*
             * cut the same prefix and suffix and check if var is still there
             */
            bool check_var_after_optimizing(expr* lhs, expr* rhs, expr* var);
            /*
             * cut the same prefix and suffix
             */
            void optimize_equality(expr* lhs, expr* rhs, ptr_vector<expr> &new_lhs, ptr_vector<expr> &new_rhs);
                expr* create_concat_from_vector(ptr_vector<expr> const& v, int from_pos);
                expr* create_concat_from_vector(ptr_vector<expr> const& v);
                bool have_same_len(expr* lhs, expr* rhs);
            /*
             * cut the same prefix and suffix
             */
            void optimize_equality(expr* lhs, ptr_vector<expr> const& rhs, ptr_vector<expr> &new_lhs, ptr_vector<expr> &new_rhs);
            /*
             * cut the same prefix and suffix
             */
            bool propagate_equality(expr* lhs, expr* rhs, expr_ref_vector &to_assert);
                bool propagate_equality_right_2_left(expr* lhs, expr* rhs, int &suffix, expr_ref_vector &and_rhs, expr_ref_vector &to_assert);
                bool propagate_equality_left_2_right(expr* lhs, expr* rhs, int &prefix, expr_ref_vector &and_lhs, expr_ref_vector &to_assert);

            obj_map<expr, int> collect_non_fresh_vars();
            expr_set collect_non_ineq_vars();
            expr_set collect_needles();
            void collect_non_fresh_vars_str_int(obj_map<expr, int> &vars);
            void add_non_fresh_var(expr* const &e, obj_map<expr, int> &vars, int len);
            void update_string_int_vars(expr* v, obj_hashtable<expr> &s);
            bool is_str_int_var(expr* e);
            void refine_important_vars(obj_map<expr, int> &non_fresh_vars, expr_ref_vector &fresh_vars, obj_map<expr, ptr_vector<expr>> const& eq_combination);
                bool check_union_membership(expr *nn, int &len);
                bool belong_to_var_var_inequality(expr* nn);
                vector<zstring> collect_all_inequalities(expr* nn);
                    bool is_var_var_inequality(expr* x, expr* y);
                expr* create_conjuct_all_inequalities(expr* nn);
                    bool is_trivial_inequality(expr* n, zstring s);
                bool collect_not_contains(expr* nn, expr_set const& ineq_vars, expr_set const& needles);
                    bool is_haystack(expr* nn);
                    bool is_needle(expr* nn);
                bool more_than_two_occurrences(expr* n, obj_map<expr, int> const& occurrences);
                bool is_non_fresh_occurrence(expr *nn, obj_map<expr, int> const &occurrences, expr_set const& ineq_vars, expr_set const& needles, int &len);
                bool is_non_fresh_recheck(expr *nn, int len, obj_map<expr, ptr_vector<expr>> const& combinations);
                obj_map<expr, int> count_occurrences_from_root();
                        bool is_replace_var(expr* x);
                    obj_map<expr, int> count_occurrences_from_combination(obj_map<expr, ptr_vector<expr>> const &eq_combination, obj_map<expr, int> const &non_fresh_vars);
            void print_all_assignments();
            void print_guessed_literals();
            obj_map<expr, ptr_vector<expr>> normalize_eq(expr_ref_vector &subNodes, obj_map<expr, int> &non_fresh_vars, bool &axiom_added);
            obj_map<expr, ptr_vector<expr>> refine_eq_combination(obj_map<expr, int> &non_fresh_vars, obj_map<expr, ptr_vector<expr>> const& combinations, expr_ref_vector const& subNodes);

                bool can_merge_combination(obj_map<expr, ptr_vector<expr>> const& combinations);
                    bool concat_in_set(expr* n, ptr_vector<expr> const& s);
                /*
                * true if var does not appear in eqs
                */
                bool appear_in_eqs(ptr_vector<expr> const& s, expr* var);

                bool is_important_concat(expr* e, obj_map<expr, int> const& non_fresh_vars);
                bool is_trivial_combination(expr* v, ptr_vector<expr> const& eq, obj_map<expr, int> const& non_fresh_vars);
                ptr_vector<expr> refine_eq_set(expr* var, ptr_vector<expr> s, obj_map<expr, int> const& non_fresh_vars, expr_ref_vector const& notnon_fresh_vars);
                ptr_vector<expr> refine_eq_set(expr* var, ptr_vector<expr> s, obj_map<expr, int> const& non_fresh_vars);
                    void refine_all_duplications(ptr_vector<expr> &s);
                    bool are_equal_concat(expr* lhs, expr* rhs);
                    ptr_vector<expr> refine_eq_set(ptr_vector<expr> const& s, obj_map<expr, int> const& non_fresh_vars);
                bool is_non_fresh(expr *n, obj_map<expr, int> const &non_fresh_vars);
                bool is_non_fresh(expr *n, obj_map<expr, int> const &non_fresh_vars, int &l);
                ptr_vector<expr> extend_object(expr* object, obj_map<expr, ptr_vector<expr>> &combinations, expr_ref_vector &subNodes, expr_ref_vector const& parents, obj_map<expr, int> const& non_fresh_vars);
                    expr* create_concat_with_concat(expr* n1, expr* n2);
                    expr* create_concat_with_str(expr* n, zstring str);
                    expr* create_concat_with_str(zstring str, expr* n);
                    expr* ends_with_str(expr* n);
                    expr* starts_with_str(expr* n);
                void add_subnodes(expr* concatL, expr* concatR, expr_ref_vector &subNodes);
        bool can_propagate() override;
        void propagate() override;
        expr* query_theory_arith_core(expr* n, model_generator& mg);
        void init_model(model_generator& m) override;
        void finalize_model(model_generator& mg) override;

        void assert_cached_eq_state();
        void handle_equality(expr * lhs, expr * rhs);
            bool new_eq_check_wrt_disequalities(expr* n, zstring containKey, expr_ref conclusion, obj_hashtable<expr> &checked_nodes);
            void special_assertion_for_contain_vs_substr(expr* lhs, expr* rhs);
            expr_ref_vector collect_all_empty_start(expr* lhs, expr* rhs);
            expr_ref_vector collect_all_empty_end(expr* lhs, expr* rhs);
            expr_ref_vector negate_equality(expr* lhs, expr* rhs);
            bool is_inconsisten(obj_hashtable<expr> concat_lhs, obj_hashtable<expr> const& concat_rhs, obj_hashtable<expr> const_lhs, obj_hashtable<expr> const& const_rhs, bool &wrongStart, bool &wrongEnd);
        /*
         * strArgmt::solve_concat_eq_str()
         * Solve concatenations of the form:
         *   const == Concat(const, X)
         *   const == Concat(X, const)
         */
        void solve_concat_eq_str(expr * concat, expr * str);
        // previously Concat() in strTheory.cpp
        // Evaluates the concatenation (n1 . n2) with respect to
        // the current equivalence classes of n1 and n2.
        // Returns a constant string expression representing this concatenation
        // if one can be determined, or NULL if this is not possible.
        expr * eval_concat(expr * n1, expr * n2);
        void group_terms_by_eqc(expr * n, obj_hashtable<expr> & concats, obj_hashtable<expr> & vars, obj_hashtable<expr> & consts);
        expr * simplify_concat(expr * node);

        /*
         * Add an axiom of the form:
         * (lhs == rhs) -> ( Length(lhs) == Length(rhs) )
         */
        void instantiate_str_eq_length_axiom(enode * lhs, enode * rhs);

        // Check that a string's length can be 0 iff it is the empty string.
        void check_eqc_empty_string(expr * lhs, expr * rhs);

        /*
         * Check whether n1 and n2 could be equal.
         * Returns true if n1 could equal n2 (maybe),
         * and false if n1 is definitely not equal to n2 (no).
         */
        bool can_two_nodes_eq(expr * n1, expr * n2);
        bool can_concat_eq_str(expr * concat, zstring& str);
        bool can_concat_eq_concat(expr * concat1, expr * concat2);
        expr * getMostLeftNodeInConcat(expr * node);
        expr * getMostRightNodeInConcat(expr * node);

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
        bool new_eq_check(expr * lhs, expr * rhs);
            expr* collect_empty_node_in_concat(expr* n);
            void propagate_const_str(expr * lhs, expr * rhs, zstring value);
            void propagate_non_const(expr_ref_vector litems, expr * concat, expr * new_concat);
        void check_regex_in(expr * nn1, expr * nn2);
            void check_regex_in_lhs_rhs(expr * nn1, expr * nn2);
                expr* construct_overapprox(expr* nn, expr_ref_vector & litems);
        void propagate_contain_in_new_eq(expr * n1, expr * n2);
        void check_contain_by_eqc_val(expr * varNode, expr * constNode);
        void check_contain_by_substr(expr * varNode, expr_ref_vector & willEqClass);
        bool in_contain_idx_map(expr * n);
        void check_contain_by_eq_nodes(expr * n1, expr * n2);
        /*
        * Decide whether n1 and n2 are already in the same equivalence class.
        * This only checks whether the core considers them to be equal;
        * they may not actually be equal.
        */
        bool in_same_eqc(expr * n1, expr * n2);

        expr * collect_eq_nodes(expr * n, expr_ref_vector & eqcSet);

        /*
        * Add axioms that are true for any string variable:
        * 1. Length(x) >= 0
        * 2. Length(x) == 0 <=> x == ""
        * If the term is a string constant, we can assert something stronger:
        *    Length(x) == strlen(x)
        */
        void instantiate_basic_string_axioms(enode * str);
        /*
        * Instantiate an axiom of the following form:
        * Length(Concat(x, y)) = Length(x) + Length(y)
        */
        void instantiate_concat_axiom(enode * cat);
        void instantiate_axiom_prefixof(enode * e);
        void instantiate_axiom_suffixof(enode * e);
        void instantiate_axiom_contains(enode * e);
        void instantiate_axiom_charAt(enode * e);
        void instantiate_axiom_indexof(enode * e);
        void instantiate_axiom_indexof_extended(enode * _e);
        void instantiate_axiom_substr(enode * e);
        void instantiate_axiom_replace(enode * e);
        void instantiate_axiom_regexIn(enode * e);
        void instantiate_axiom_int_to_str(enode * e);
        void instantiate_axiom_str_to_int(enode * e);

        bool can_solve_contain_family(enode * e);
        bool can_reduce_contain_family(expr* ex);
        app* mk_replace(expr* a, expr* b, expr* c) const;
        app* mk_at(expr* a, expr* b) const;
        expr* is_regex_plus_breakdown(expr* e);
        void sync_index_head(expr* pos, expr* base, expr* first_part, expr* second_part);
        app * mk_fresh_const(char const* name, sort* s);
        app * mk_strlen(expr * e);
        expr * mk_string(zstring const& str);
        expr * mk_string(const char * str);
        app * mk_str_var(std::string name);
        expr * mk_concat(expr * n1, expr * n2);
        expr * mk_concat_const_str(expr * n1, expr * n2);
        app * mk_int(int n);
        app * mk_int(rational & q);
        app * mk_contains(expr * haystack, expr * needle);
        app * mk_indexof(expr * haystack, expr * needle);
        app * mk_int_var(std::string name);
        app * mk_regex_rep_var();
        expr * mk_regexIn(expr * str, expr * regexp);
        app * mk_unroll(expr * n, expr * bound);
        app * mk_unroll_bound_var();
        app * mk_str_to_re(expr *);
        app * mk_arr_var(zstring name);

        void get_nodes_in_concat(expr * node, ptr_vector<expr> & nodeList);
        void get_nodes_in_reg_concat(expr * node, ptr_vector<expr> & nodeList);
        void get_all_nodes_in_concat(expr * node, ptr_vector<expr> & nodeList);
        expr * get_eqc_value(expr * n, bool & hasEqcValue);
        expr * z3str2_get_eqc_value(expr * n , bool & hasEqcValue);
        expr * get_eqc_next(expr * n);

        theory_var get_var(expr * n) const;
        app * get_ast(theory_var v);
        zstring get_std_regex_str(expr * regex);
        bool get_len_value(expr* e, rational& val);
        bool get_arith_value(expr* e, rational& val) const;
        bool lower_bound(expr* _e, rational& lo) const;
        bool upper_bound(expr* _e, rational& hi) const;
        bool upper_num_bound(expr* e, rational& hi) const;
        bool lower_num_bound(expr* e, rational& hi) const;
        void get_concats_in_eqc(expr * n, obj_hashtable<expr> & concats);
        /*
         * Collect constant strings (from left to right) in an AST node.
         */
        void get_const_str_asts_in_node(expr * node, expr_ref_vector & astList);
        /*
        * Collect constant strings (from left to right) in an AST node.
        */
        void get_const_regex_str_asts_in_node(expr * node, expr_ref_vector & astList);

        /*
         * Check if there are empty vars in an AST node.
         */
        bool has_empty_vars(expr * node);

        /*
         * Collect important vars in AST node
         */
        void get_important_asts_in_node(expr * node, obj_map<expr, int> const& non_fresh_vars, expr_ref_vector & astList, bool consider_itself = false);
        eautomaton* get_automaton(expr* re);

        expr * rewrite_implication(expr * premise, expr * conclusion);
        void assert_implication(expr * premise, expr * conclusion);

        enode* ensure_enode(expr* e);
        bool                                                search_started;
        th_rewriter                                         m_rewrite;
        seq_rewriter                                        m_seq_rewrite;
        arith_util                                          m_autil;
        array_util                                          m_arrayUtil;
        seq_util                                            u;
        expr_ref_vector                                     m_trail; // trail for generated terms
        th_union_find                                       m_find;
        th_trail_stack                                      m_trail_stack;

        obj_pair_map<expr, expr, expr*>                     concat_astNode_map;

        obj_map<expr, expr*>                                 regex_in_bool_map;
        obj_map<expr, string_set >                          regex_in_var_reg_str_map;

        scoped_ptr_vector<eautomaton>                       m_automata;
        ptr_vector<eautomaton>                              regex_automata;
        obj_hashtable<expr>                                 regex_terms;
        obj_map<expr, ptr_vector<expr> >                    regex_terms_by_string; // S --> [ (str.in.re S *) ]

        // hashtable of all exprs for which we've already set up term-specific axioms --
        // this prevents infinite recursive descent with respect to axioms that
        // include an occurrence of the term for which axioms are being generated
        obj_hashtable<expr>                                 axiomatized_terms;
        obj_hashtable<expr>                                 variable_set;
        obj_hashtable<expr>                                 internal_variable_set;
        obj_hashtable<expr>                                 regex_variable_set;

        expr_ref_vector                                     m_delayed_axiom_setup_terms;

        ptr_vector<enode>                                   m_basicstr_axiom_todo;
        svector<std::pair<enode*,enode*> >                  m_str_eq_todo;
        ptr_vector<enode>                                   m_concat_axiom_todo;
        ptr_vector<enode>                                   m_concat_eval_todo;
        expr_ref_vector                                     m_delayed_assertions_todo;

        // enode lists for library-aware/high-level string terms (e.g. substr, contains)
        obj_hashtable<enode>                                m_library_aware_axiom_todo;
        obj_hashtable<expr>                                 input_var_in_len;
        expr_ref_vector                                     string_int_conversion_terms;
        obj_hashtable<expr>                                 string_int_axioms;
        obj_hashtable<expr>                                 string_int_vars;
        obj_hashtable<expr>                                 int_string_vars;

        expr_ref_vector                                     m_persisted_axiom_todo;

        expr_ref_vector                                     contains_map;

        obj_pair_map<expr, expr, expr*>                     contain_pair_bool_map;
        obj_map<expr, str::expr_pair_set >                  contain_pair_idx_map;
        obj_map<enode, std::pair<enode*,enode*>>            contain_split_map;
        obj_map<expr, expr*>                                index_head;
        obj_map<expr, std::pair<expr*, expr*>>              index_tail;
        str::expr_pair_set                                  length_relation;
        unsigned                                            m_fresh_id;
        string_map                                          stringConstantCache;
        unsigned long                                       totalCacheAccessCount;

        obj_map<expr, eautomaton*>                          m_re2aut;
        re2automaton                                        m_mk_aut;
        expr_ref_vector                                     m_res;
        rational                                            p_bound = rational(2);
        rational                                            q_bound = rational(10);
        rational                                            str_int_bound;
        rational                                            max_str_int_bound = rational(10);
        rational                                            max_p_bound = rational(3);
        rational                                            max_q_bound = rational(20);
        expr*                                               str_int_bound_expr = nullptr;
        expr*                                               p_bound_expr = nullptr;
        expr*                                               q_bound_expr = nullptr;
        bool                                                flat_enabled = false;
        bool                                                need_change = false;
        /*
         * If DisableIntegerTheoryIntegration is set to true,
         * ALL calls to the integer theory integration methods
         * (get_arith_value, get_len_value, lower_bound, upper_bound)
         * will ignore what the arithmetic solver believes about length terms,
         * and will return no information.
         *
         * This reduces performance significantly, but can be useful to enable
         * if it is suspected that string-integer integration, or the arithmetic solver itself,
         * might have a bug.
         *
         * The default behaviour of Z3str2 is to set this to 'false'.
         */
        bool                                                opt_DisableIntegerTheoryIntegration;

        /*
         * If ConcatOverlapAvoid is set to true,
         * the check to simplify Concat = Concat in handle_equality() will
         * avoid simplifying wrt. pairs of Concat terms that will immediately
         * result in an overlap. (false = Z3str2 behaviour)
         */
        bool                                                 opt_ConcatOverlapAvoid;


        // under approximation vars
        const int                                           CONNECTINGSIZE = 300;
        static const int                                    PMAX = 2;
        const std::string                                   FLATPREFIX = "__flat_";
        int                                                 flat_var_counter = 0;


        obj_map<expr, int>                                  var_pieces_counter;
        obj_map<expr, int>                                  curr_var_pieces_counter;
        string_set                                          generated_equalities;
        arrangment_map                                      arrangements; 
        string_set                                          const_set;
        unsigned_set                                        sigma_domain;
        obj_map<expr, ptr_vector <expr>>                    length_map;
        obj_map<expr, ptr_vector <expr>>                    iter_map;
        obj_map<expr, expr_set>                             appearance_map;
        obj_map<expr, expr_set>                             not_contain_map;
        obj_map<expr, expr_set>                             dependency_graph;
        obj_map<expr, expr*>                                expr_array_linkers;
        obj_map<expr, expr*>                                array_map;
        string_map                                          array_map_reverse;
        obj_map<expr, expr*>                                arr_linker;
        int                                                 connectingSize;
        char                                                default_char = 'a';
        UnderApproxState                                    uState;
        vector<UnderApproxState>                            completed_branches;

        expr_ref_vector                                     implied_facts;
    private:
        clock_t                                             startClock;
        bool                                                newConstraintTriggered = false;
        void assert_axiom(expr *e);
        void assert_axiom(expr *const e1, expr *const e2);
        void dump_assignments();
        void dump_literals();
        void fetch_guessed_core_exprs(
                obj_map<expr, ptr_vector<expr>> const& eq_combination,
                expr_ref_vector &guessed_exprs,
                expr_ref_vector const& diseq_exprs,
                rational bound = rational(0));
        void add_equalities_to_core(expr_ref_vector guessed_exprs, expr_ref_vector &all_vars, expr_ref_vector &core);
        void add_disequalities_to_core(expr_ref_vector const& diseq_exprs, expr_ref_vector &core);
        void add_assignments_to_core(expr_ref_vector const& all_vars, expr_ref_vector &core);
        unsigned get_assign_lvl(expr* a, expr* b);
        void fetch_related_exprs(expr_ref_vector const& all_vars, expr_ref_vector &guessed_eqs);
        expr_ref_vector check_contain_related_vars(expr* v, zstring replaceKey);
        expr_ref_vector collect_all_vars_in_eq_combination(obj_map<expr, ptr_vector<expr>> const& eq_combination);
        void update_all_vars(expr_ref_vector &allvars, expr* e);
        bool check_intersection_not_empty(ptr_vector<expr> const& v, obj_hashtable<expr> const& allvars);
        bool check_intersection_not_empty(ptr_vector<expr> const& v, expr_ref_vector const& allvars);
        void fetch_guessed_exprs_from_cache(UnderApproxState const& state, expr_ref_vector &guessed_exprs);
        void fetch_guessed_exprs_with_scopes(expr_ref_vector &guessedEqs);
        void fetch_guessed_exprs_with_scopes(expr_ref_vector &guessedEqs, expr_ref_vector &guessedDisEqs);
        void fetch_guessed_literals_with_scopes(literal_vector &guessedLiterals);
        void fetch_guessed_str_int_with_scopes(expr_ref_vector &guessedEqs, expr_ref_vector &guessedDisEqs);
        const bool is_theory_str_term(expr *e) const;
        decl_kind get_decl_kind(expr *e) const;
        void set_up_axioms(expr * ex);

        enum {
            NONE = 0,
            LEFT_EMPTY = 1,
            LEFT_EQUAL = 2,
            LEFT_SUM = 3,
            RIGHT_EMPTY = 4,
            RIGHT_EQUAL = 5,
            RIGHT_SUM = 6
        };

        enum {
            SIMPLE_CASE = 0,
            CONST_ONLY = 1,
            NON_FRESH__ONLY = 2,
            CONST_NON_FRESH = 3
        };
    };


//    class int_expr_solver:expr_solver{
//        bool unsat_core=false;
//        kernel m_kernel;
//        ast_manager& m;
//        bool initialized;
//        expr_ref_vector erv;
//    public:
//        int_expr_solver(ast_manager& m, smt_params fp):
//                m_kernel(m, fp), m(m),erv(m){
//            fp.m_string_solver = symbol("none");
//            initialized=false;
//        }
//
//        lbool check_sat(expr* e) override;
//
//        void initialize(context& ctx);
//
//        void assert_expr(expr * e);
//    };

}

#endif /* _THEORY_TRAU_H_ */
