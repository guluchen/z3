#include <iostream>
#include <string>
#include "util/trace.h"
#include "ast/ast_pp.h"
#include "smt/smt_theory.h"
#include "smt/theory_str/theory_str.h"

namespace smt {

    namespace str {

        bool counter_system::cs_assign::operator<(const counter_system::cs_assign &other) const {
            if (type < other.type) return true;
            if (num < other.num) return true;
            if (vars.size() < other.vars.size()) return true;
            return false;
        }

        bool counter_system::add_var_expr(const std::string &str, std::list<expr*> exprs, const std::string& str_short) {
            if (var_expr.count(str)==0) {
                var_expr.insert({str,{exprs,str_short}});
                return true;
            }
            return false;
        }

        bool counter_system::add_transition(const smt::str::counter_system::cs_state s,
                                            const smt::str::counter_system::cs_assign &assign,
                                            const smt::str::counter_system::cs_state s_to) {
            if (relation.count(s) == 0) {
                const std::set<cs_transition> tr = {{assign, s_to}};
                relation.insert({s, tr});
                return true;
            } else {
                relation[s].insert({assign, s_to});
                return false;
            }
        }

        const std::string counter_system::cs_assign::type2str() const {
            switch (type) {
                case counter_system::assign_type::CONST:
                    return "CONST";
                case counter_system::assign_type::VAR:
                    return "VAR";
                case counter_system::assign_type::PLUS_ONE:
                    return "PLUS_ONE";
                case counter_system::assign_type::PLUS_VAR:
                    return "PLUS_VAR";
                default:
                    return "";  // not reachable
            }
        }

        counter_system::counter_system(const smt::str::solver &solv) {
            SASSERT(!solv.get_success_leaves().empty());
            bool on_screen =false;
            cs_state counter = 1;
            std::unordered_map<state::cref, cs_state, state::hash, std::equal_to<state>> mapped_states;
            std::queue<state::cref> process_queue;
            std::unordered_set<state::cref, state::hash, std::equal_to<state>> processed_states;
            // set initial states
            for (const auto &s : solv.get_success_leaves()) {  // assume all succ_states are different (set of states)
                add_init_state(counter);
                SASSERT(mapped_states.count(s) == 0);
                mapped_states.insert({s, counter});
                process_queue.push(s);
                counter++;
            }
            // for the case of no initial states (no success states), add all states to queue and map
            if (solv.get_success_leaves().empty()) {
                for (const auto &s : solv.get_graph().access_map()) {
                    SASSERT(mapped_states.count(s.first) == 0);
                    mapped_states.insert({s.first, counter});
                    process_queue.push(s.first);
                    counter++;
                }
            }
            // processing relations
            cs_state cs_curr, cs_tgt;
            std::list<solver::move> moves;
            cs_assign assign;
            while (!process_queue.empty()) {
                const state &curr = process_queue.front();
                SASSERT(mapped_states.count(curr) != 0);
                cs_curr = mapped_states[curr];
                process_queue.pop();
                if (processed_states.count(curr) != 0) {
                    continue;  // already processed, skip
                } else {
                    processed_states.insert(curr);
                }
                for (auto const &m : solv.get_graph().incoming_moves(curr)) {
                    const state &tgt = m.m_from;
                    if (mapped_states.count(tgt) == 0) {  // if tgt is new, add to mapping
                        mapped_states.insert({tgt, counter});
                        cs_tgt = counter;
                        counter++;
                    } else {
                        cs_tgt = mapped_states[tgt];
                    }
                    switch (m.m_type) {
                        case solver::move::t::TO_EMPTY:
                            assign.type = counter_system::assign_type::CONST;
                            assign.num = 0;  // assign to zero
                            for (auto const &e : m.m_record) {
                                assign.vars.push_back(e.value().encode());
                                add_var_expr(e.value().encode(), e.origin_expr(), e.shortname());
                            }
                            break;
                        case solver::move::t::TO_CONST:
                            assign.type = counter_system::assign_type::CONST;
                            assign.num = m.m_record.size() - 1;  // assign to a constant >= 1
                            SASSERT(assign.num >= 1);
                            assign.vars.push_back(m.m_record[0].value().encode());
                            add_var_expr(m.m_record[0].value().encode(), m.m_record[0].origin_expr(), m.m_record[0].shortname());
                            break;
                        case solver::move::t::TO_VAR:
                            assign.type = counter_system::assign_type::VAR;
                            for (auto const &e : m.m_record) {
                                assign.vars.push_back(e.value().encode());
                                add_var_expr(e.value().encode(), e.origin_expr(), e.shortname());
                            }
                            break;
                        case solver::move::t::TO_VAR_VAR:
                            assign.type = counter_system::assign_type::PLUS_VAR;
                            for (auto const &e : m.m_record) {
                                assign.vars.push_back(e.value().encode());
                                add_var_expr(e.value().encode(), e.origin_expr(), e.shortname());
                            }
                            break;
                        case solver::move::t::TO_CHAR_VAR:
                            assign.type = counter_system::assign_type::PLUS_ONE;
                            assign.vars.push_back(m.m_record[0].value().encode());
                            add_var_expr(m.m_record[0].value().encode(), m.m_record[0].origin_expr(), m.m_record[0].shortname());
                            break;
                        default: SASSERT(false);
                    }
                    add_transition(cs_curr, assign, cs_tgt);
                    assign.vars.clear();
                    if (processed_states.count(tgt) == 0)  // if tgt is not processed yet, add to queue
                        process_queue.push(tgt);
                }
            }
            set_final_state(mapped_states[solv.get_root()]);  // at last, set final state
            num_states = mapped_states.size();
            STRACE("str", tout << "[COUNTER_SYSTEM]\nmapped_states final...\n";);
            STRACE("str", tout << "mapped_states size = " << num_states << '\n';);
            unsigned int num_trans = 0;
            for (const auto& e : relation) {
                num_trans += e.second.size();
            }
            for (const auto& e : mapped_states) {
                STRACE("str", tout << "state number " << e.second << " maps to state:\n" << e.first  << '\n';);
            }
            if(on_screen) std::cout << "[COUNTER_SYSTEM]:\n";
            if(on_screen) std::cout << "#states = " << num_states << "; #transitions = " << num_trans << '\n';
            if(on_screen) std::cout << "ROOT quadratic? " << std::boolalpha << solv.get_root().get().quadratic() << '\n';
            if(on_screen) std::cout << "is dag? " << std::boolalpha << is_dag() << '\n';
            STRACE("str", tout << "[COUNTER_SYSTEM]:\n";);
            STRACE("str", tout << "#states=" << num_states << "; #transitions=" << num_trans << '\n';);
            STRACE("str", tout << "ROOT quadratic? " << std::boolalpha << solv.get_root().get().quadratic() << '\n';);
            STRACE("str", tout << "is dag? " << std::boolalpha << is_dag() << '\n';);

            STRACE("str", tout << "mapped_states final..." << std::endl;);
            STRACE("str", tout << "mapped_states size = " << num_states << std::endl;);
//            for (const auto& e : mapped_states) {
//                STRACE("str", tout << e.first  << "    " << e.second << std::endl;);
//            }
            STRACE("str", tout << "counter_system extracted!" << std::endl;);
        }

        void counter_system::print_var_expr(ast_manager &m) {
            STRACE("str", tout << "[var_name <--> expr] in counter system: " << std::endl;);
            std::stringstream tmp_str;
            for (const auto& ve: var_expr) {
                if (ve.second.first.size() > 1) {  // concat of variables
                    for (auto& e : ve.second.first) {
                        tmp_str << mk_pp(e, m);
                    }
                    STRACE("str", tout << "[ " << ve.first << " ] <--> [ " << tmp_str.str() << " ]" << std::endl;);
                }
                else {
                    STRACE("str", tout << "[ " << ve.first << " ] <--> [ " << mk_pp(ve.second.first.front(),m) << " ]" << std::endl;);
                }
            }
        }

        void counter_system::print_transition(const smt::str::counter_system::cs_state s,
                                              const smt::str::counter_system::cs_assign &assign,
                                              const smt::str::counter_system::cs_state s_to) const {
            std::string sep_str;
            STRACE("str", tout << "(" << s << "," << s_to << ")[";);
            switch (assign.type) {
                case counter_system::assign_type::CONST:
                    sep_str = "";
                    for (const auto v : assign.vars) {
//                        STRACE("str", tout << sep_str << v << "=" << assign.num;);
                        STRACE("str", tout << sep_str << var_expr.find(v)->second.second << "=" << assign.num;);
                        sep_str = ",";
                    }
                    break;
                case counter_system::assign_type::VAR:
                    STRACE("str", tout << var_expr.find(*(assign.vars.begin()))->second.second << "=" <<
                    var_expr.find(*(std::next(assign.vars.begin())))->second.second;);
                    break;
                case counter_system::assign_type::PLUS_ONE:
                    STRACE("str", tout << var_expr.find(*(assign.vars.begin()))->second.second << "=" <<
                    var_expr.find(*(assign.vars.begin()))->second.second << "+1";);
                    break;
                case counter_system::assign_type::PLUS_VAR:
                    STRACE("str", tout << *(assign.vars.begin()) << "=" <<
                    var_expr.find(*(assign.vars.begin()))->second.second << "+" <<
                    var_expr.find(*(std::next(assign.vars.begin())))->second.second;);
                    break;
                default:
                    break;
            }
            STRACE("str", tout << "]";);
        }

        void counter_system::print_counter_system() const {
            bool on_screen=true;
            std::string sep_str;
            if(on_screen) std::cout<<" digraph counter_system {\n";

            STRACE("str", tout << "counter system pretty print..." << std::endl;);
            STRACE("str", tout << "init={";);
            sep_str = "";
            for (auto i : init) {
                STRACE("str", tout << sep_str << i;);
                sep_str = ", ";
            }
            STRACE("str", tout << "}" << std::endl;);
            STRACE("str", tout << "final=" << final << ", " << "#var=" << var_expr.size() << std::endl;);
            STRACE("str", tout << "vars={";);
            sep_str = "";
            for (auto const v : var_expr) {
                STRACE("str", tout << sep_str << v.second.second;);
                sep_str = ", ";
            }
            STRACE("str", tout << "}" << std::endl;);
            STRACE("str", tout << "relations(" << relation.size() << "): {" << std::endl;);
            char tab[] = "    ";
            for (auto const &r : relation) {
                for (auto const &tran: r.second) {
                    STRACE("str", tout << tab;);
                    print_transition(r.first, tran.first, tran.second);
                    if(on_screen) std::cout<<r.first<<" -> "<<tran.second<<";\n";
                    STRACE("str", tout << std::endl;);
                }
            }
            STRACE("str", tout << "}" << std::endl;);
            if(on_screen) std::cout<<"}"<<std::endl;

        }

        bool counter_system::is_dag() {  // standard dag cycle detection algorithm
            std::set<int> white{}, gray{}, black{};
            std::map<int,std::set<int>> graph;
            std::map<int,int> parent;  // maps to -1 means no parent state
            int curr = -1, next = -1;
            // copy relation into a graph of cs_state for processing
            for (const auto& rel : relation) {
                white.insert(rel.first);
                graph[rel.first] = {};
                for (const auto& tran : rel.second) {
                    white.insert(tran.second);  // in case of a state without outgoing transition
                    graph[rel.first].insert(tran.second);
                }
            }
            // start algorithm
            while (!white.empty()) {
                if (curr == -1) {
                    curr = *white.begin();
                    gray.insert(curr);
                    white.erase(curr);
                    parent[curr] = -1;  // no parent
                }
                while (!graph[curr].empty()) {
                    next = *graph[curr].begin();
                    parent[next] = curr;
                    graph[curr].erase(next);
                    curr = next;
                    if (black.find(curr) != black.end()) {
                        curr = parent[curr];
                    }
                    else if (gray.find(curr) != gray.end()) {
                        return false;  // found cycle
                    }
                    else if (white.find(curr) != white.end()) {
                        gray.insert(curr);
                        white.erase(curr);
                    }
                    else assert(false);
                }
                assert(gray.find(curr) != gray.end());
                black.insert(curr);
                gray.erase(curr);
                curr = parent[curr]; // go parent
            }
            return true;
        }

        apron_counter_system::node::node(ap_manager_t *man, ap_abstract1_t &base_abs) {
            abs = ap_abstract1_copy(man, &base_abs);
            abs_pre = ap_abstract1_copy(man, &base_abs);
        }

        apron_counter_system::node::node(ap_manager_t *man, ap_environment_t *env, bool top_flag) {
            if (top_flag) {
                abs = ap_abstract1_top(man, env);
                abs_pre = ap_abstract1_top(man, env);
            } else {
                abs = ap_abstract1_bottom(man, env);
                abs_pre = ap_abstract1_bottom(man, env);
            }
        }

        void apron_counter_system::node::print_abs_silent(ap_manager_t *man) {
            FILE *fptr = fopen("/dev/null", "w");
            ap_abstract1_fprint(fptr, man, &abs);
        }

        void apron_counter_system::node::widening(ap_manager_t *man) {
            ap_abstract1_t abs_tmp = abs;
            abs = ap_abstract1_widening(man, &abs_pre, &abs);
            ap_abstract1_clear(man, &abs_tmp);
            ap_abstract1_clear(man, &abs_pre);
            abs_pre = ap_abstract1_copy(man, &abs);
        }

        long int ap_coeff2int(ap_coeff_t *c) {
            SASSERT(mpz_get_si(&c->val.scalar->val.mpq->_mp_den) == 1);  // make sure it is an integer
            return mpz_get_si(&c->val.scalar->val.mpq->_mp_num);
        }

        ap_length_constraint::len_cons::len_cons(ap_manager_t *ap_man, ap_lincons1_t* ap_cons_ptr,
                const std::map<std::string,std::pair<std::list<expr*>,std::string>>& var_expr) {
            ap_constyp_t *ap_constyp;
            ap_coeff_t *ap_cst, *ap_coeff;
            ap_environment_name_of_dim_t *name_of_dim;

            // set constraint type
            ap_constyp = ap_lincons1_constypref(ap_cons_ptr);
            switch (*ap_constyp) {
                case AP_CONS_EQ:
                    m_type = lcons_type::EQ;
                    break;
                case AP_CONS_SUPEQ:
                    m_type = lcons_type::SUPEQ;
                    break;
                case AP_CONS_SUP:
                    std::cout << "AP_CONS_SUP\n";
                case AP_CONS_EQMOD:
                    std::cout << "AP_CONS_EQMOD\n";
                case AP_CONS_DISEQ:
                    std::cout << "AP_CONS_DISEQ\n";
                    std::cout << "Unsupported type" << std::endl;
                default:
                    SASSERT(false);
            }

            // set coefficients and constant
            ap_cst = ap_lincons1_cstref(ap_cons_ptr);
            SASSERT(ap_cst->discr == AP_COEFF_SCALAR &&
                    ap_cst->val.scalar->discr == AP_SCALAR_MPQ);  // only support this case
            name_of_dim = ap_environment_name_of_dim_alloc(ap_cons_ptr->env);
            m_cst = ap_coeff2int(ap_cst);
            long int num_coeff;
            for (unsigned int j = 0; j < name_of_dim->size; j++) {
                ap_coeff = ap_lincons1_coeffref(ap_cons_ptr, name_of_dim->p[j]);
                SASSERT(ap_coeff != NULL &&
                        ap_coeff->discr == AP_COEFF_SCALAR &&
                        ap_coeff->val.scalar->discr == AP_SCALAR_MPQ);  // only support this case
                num_coeff = ap_coeff2int(ap_coeff);
                if (num_coeff != 0) {
                    std::string var_name(name_of_dim->p[j]);
                    m_var_expr_coeff[var_name] = std::make_pair(var_expr.find(var_name)->second.first,num_coeff);
                }
            }
            ap_environment_name_of_dim_free(name_of_dim);
        }

        void ap_length_constraint::len_cons::pretty_print(ast_manager &ast_man) {
            std::stringstream tmp_str;
            for (const auto& ve : m_var_expr_coeff) {
                if (ve.second.first.size() > 1) {  // concat of variables
                    tmp_str << "(concat";
                    for (auto& e : ve.second.first) {
                        tmp_str << " " << mk_pp(e, ast_man);
                    }
                    STRACE("str", tout << "(" << ve.second.second << ")*" << tmp_str.str() << " + ";);
                }
                else {
                    STRACE("str", tout << "(" << ve.second.second << ")*" << mk_pp(ve.second.first.front(), ast_man) << " + ";);
                }
            }
            STRACE("str", tout << m_cst;);
            switch (m_type) {
                case lcons_type::EQ:
                    STRACE("str", tout << " = 0";);
                    break;
                case lcons_type::SUPEQ:
                    STRACE("str", tout << " >=0";);
                    break;
                default:
                    SASSERT(false);
            }
            STRACE("str", tout << std::endl;);
        }

        void ap_length_constraint::pretty_print(ast_manager &ast_man) {
            STRACE("str", tout << "total linear constraints: " << m_cons.size() << '\n';);
            for (auto& e : m_cons) {
                e.pretty_print(ast_man);
            }
        }

        expr_ref ap_length_constraint::len_cons::export_z3exp(ast_manager& m) {
            arith_util ap_util_a(m);
            seq_util ap_util_s(m);

            expr_ref ret = {ap_util_a.mk_int(m_cst),m};
            expr_ref var_len_exp(m);

            for (const auto& ve : m_var_expr_coeff) {
                int i = 1;
                if (ve.second.first.size() > 1) {  // addition of variable lengths if more than one expression
                    for (auto& e : ve.second.first) {
                        if (i==1) {
                            var_len_exp = {ap_util_s.str.mk_length(e),m};
                        }
                        else {
                            var_len_exp = {ap_util_a.mk_add(var_len_exp, ap_util_s.str.mk_length(e)),m};
                        }
                        i++;
                    }
                }
            }
            switch (m_type) {
                case lcons_type::EQ:
                    ret = {ap_util_a.mk_eq(ret,ap_util_a.mk_int(0)),m};
                    break;
                case lcons_type::SUPEQ:
                    ret = {ap_util_a.mk_ge(ret,ap_util_a.mk_int(0)),m};
                    break;
                default:
                    SASSERT(false);
            }
            return ret;
        }

        expr_ref ap_length_constraint::export_z3exp(ast_manager& m) {
            arith_util ap_util_a(m);
            expr_ref ret(m);
            if (empty()) {
                std::cout << "ERROR: empty length constraint! export nothing..." << std::endl;
                return ret;
            }

            bool flg = false;
            for (auto& e : m_cons) {
                if (flg) {
                    ret = {m.mk_and(ret,e.export_z3exp(m)),m};
                }
                else {
                    ret = {e.export_z3exp(m),m};
                    flg = true;
                }
            }
            return ret;
        }

        ap_length_constraint::ap_length_constraint(ap_manager_t *ap_man, ap_abstract1_t *ap_abs_ptr,
                const std::map<std::string,std::pair<std::list<expr*>,std::string>>& var_expr) {
            ap_lincons1_array_t cons_arr = ap_abstract1_to_lincons_array(ap_man, ap_abs_ptr);
            size_t len_cons_arr = ap_lincons1_array_size(&cons_arr);
            ap_lincons1_t ap_cons;
            for (size_t i = 0; i < len_cons_arr; i++) {
                ap_cons = ap_lincons1_array_get(&cons_arr, i);
                m_cons.emplace_back(len_cons(ap_man, &ap_cons, var_expr));
            }
        }

        void apron_counter_system::node::join_and_update_abs(ap_manager_t *man, ap_abstract1_t &from_abs) {
            ap_abstract1_clear(man, &abs_pre);
            abs_pre = abs;
            abs = ap_abstract1_join(man, false, &abs, &from_abs);
        }

        void apron_counter_system::ap_assign::abstraction_propagate(ap_manager_t *man, node &s, node &s_to) {
            ap_abstract1_t s_abs = ap_abstract1_copy(man, &s.get_abs());
            SASSERT(!var_exp_pairs.empty());
            for (auto &var_exp : var_exp_pairs) {
                s_abs = ap_abstract1_assign_linexpr(man, true, &s_abs, var_exp.first, &var_exp.second, NULL);
            }
            s_to.join_and_update_abs(man, s_abs);
            ap_abstract1_minimize(man, &s_to.get_abs());  // necessary for efficiency
            ap_abstract1_clear(man, &s_abs);
        }

        apron_counter_system::ap_assign::ap_assign(ap_environment_t *env, const counter_system::cs_assign &assign) {
            using cs_assign_type = counter_system::assign_type;
            char *var, *var_to;
            ap_linexpr1_t expr;
            switch (assign.type) {
                case cs_assign_type::CONST:
                    for (const auto &v : assign.vars) {
                        var = strdup(v.c_str());
                        expr = ap_linexpr1_make(env, AP_LINEXPR_SPARSE, 0);
                        ap_linexpr1_set_list(&expr,
                                             AP_CST_S_INT, assign.num,
                                             AP_END);
                        var_exp_pairs.emplace_back(std::make_pair(var, expr));
                    }
                    break;
                case cs_assign_type::VAR:
                    var = strdup(assign.vars.front().c_str());
                    var_to = strdup(assign.vars.back().c_str());
                    expr = ap_linexpr1_make(env, AP_LINEXPR_SPARSE, 0);
                    ap_linexpr1_set_list(&expr,
                                         AP_COEFF_S_INT, 1, var_to,
                                         AP_END);
                    var_exp_pairs.emplace_back(std::make_pair(var, expr));
                    break;
                case cs_assign_type::PLUS_ONE:
                    var = strdup(assign.vars.front().c_str());
                    var_to = strdup(assign.vars.back().c_str());
                    expr = ap_linexpr1_make(env, AP_LINEXPR_SPARSE, 0);
                    ap_linexpr1_set_list(&expr,
                                         AP_COEFF_S_INT, 1, var_to,
                                         AP_CST_S_INT, 1,
                                         AP_END);
                    var_exp_pairs.emplace_back(std::make_pair(var, expr));
                    break;
                case cs_assign_type::PLUS_VAR:
                    var = strdup(assign.vars.front().c_str());
                    var_to = strdup(assign.vars.back().c_str());
                    expr = ap_linexpr1_make(env, AP_LINEXPR_SPARSE, 0);
                    ap_linexpr1_set_list(&expr,
                                         AP_COEFF_S_INT, 1, var,
                                         AP_COEFF_S_INT, 1, var_to,
                                         AP_END);
                    var_exp_pairs.emplace_back(std::make_pair(var, expr));
                    break;
                default: SASSERT(false);
            }
            SASSERT(!var_exp_pairs.empty());
        }

        apron_counter_system::apron_counter_system(const smt::str::counter_system &cs) {
            // copy var_expr from counter system by operator= (overloaded)
            var_expr = cs.get_var_expr();
            // set variables names to C-style
            num_vars = var_expr.size();
            variables = (ap_var_t *) malloc(sizeof(ap_var_t) * var_expr.size());
            int count = 0;
            for (auto &e : var_expr) {
                variables[count] = strdup(e.first.c_str());  // best way to copy c_str() to char*
                count++;
            }
            // set state-related attributes
            init = cs.init_states();
            final = cs.final_state();
            num_states = cs.get_num_states();
            // set apron environment
//            man = box_manager_alloc();
//            man = oct_manager_alloc();
//            man = pk_manager_alloc(true);
            man = ap_ppl_poly_manager_alloc(true);
//            man = pkeq_manager_alloc();
//            man = ap_ppl_grid_manager_alloc();
            env = ap_environment_alloc(variables, var_expr.size(), NULL, 0);
            // initialize nodes
            for (ap_state i = 1; i <= num_states; i++) {
                if (init.count(i) > 0) {
                    nodes.emplace(i, node(man, env, true));
                } else {
                    nodes.emplace(i, node(man, env, false));
                }
                ap_abstract1_minimize(man, &nodes[i].get_abs());  // necessary to avoid slow-down
            }
            // set relations
            for (const auto &rel : cs.get_relations()) {
                ap_state src_state = rel.first;
                for (const auto &tr : rel.second) {
                    ap_assign assign = ap_assign(env, tr.first);
                    if (relations.count(src_state) == 0) {
                        relations[src_state] = {{assign, tr.second}};
                    } else {
                        relations[src_state].push_back({assign, tr.second});
                    }
                }
            }
        }

        void apron_counter_system::print_apron_counter_system() {
            std::string sep_str;
            std::cout << "apron counter system pretty print..." << std::endl;
            std::cout << "init={";
            sep_str = "";
            for (auto i : init) {
                std::cout << sep_str << i;
                sep_str = ", ";
            }
            std::cout << "}" << std::endl;
            std::cout << "final=" << final << ", " << "#var=" << num_vars << std::endl;
            std::cout << "variables : { ";
            sep_str = "";
            for (int i = 0; i < (int) num_vars; i++) {
                printf("%s%s", sep_str.c_str(), (char *) variables[i]);
                sep_str = ", ";
            }
            std::cout << " }" << std::endl;
            char tab[] = "    ";
            std::cout << "nodes(" << nodes.size() << "): {" << std::endl;
            for (auto &n : nodes) {
                std::cout << "state " << n.first << "-->" << std::endl;
                n.second.print_abs(man);
            }
            std::cout << "}" << std::endl;
            std::cout << "relations(" << relations.size() << "): {" << std::endl;
            for (auto const &r : relations) {
                for (auto const &tran: r.second) {
                    std::cout << tab;
                    std::cout << "(" << r.first << "," << tran.second << ")[";
                    sep_str = "";
                    for (auto a : tran.first.get_var_exp_pairs()) {
                        printf("%s%s=", sep_str.c_str(), a.first);
                        ap_linexpr1_fprint(stdout, &a.second);
                        sep_str = ", ";
                    }
                    std::cout << "]" << std::endl;
                }
            }
            std::cout << "}" << std::endl;
        }

        bool apron_counter_system::fixpoint_check(bool widen_flag) {
            bool ret = true;
            for (auto &p : nodes) {
                if (!p.second.equal_to_pre(man)) {
                    ret = false;
                    if (widen_flag) p.second.widening(man);
                }
            }
            return ret;
        }

        void apron_counter_system::abstraction() {
            ap_state curr_s;
            std::queue<ap_state> process_queue;
            std::set<ap_state> visited;
            // processing
            for (const auto s : init) process_queue.push(s);
            while (!process_queue.empty()) {
                curr_s = process_queue.front();
                process_queue.pop();
                if (visited.count(curr_s) > 0) continue;
                SASSERT(nodes.count(curr_s) != 0);
                visited.insert(curr_s);
                for (auto &tr : relations[curr_s]) {
                    SASSERT(nodes.count(tr.second) != 0);
                    // std::cout << "abstraction propagate from node " << curr_s << " to " << tr.second << std::endl;
                    tr.first.abstraction_propagate(man, nodes[curr_s], nodes[tr.second]);
                    if (visited.count(tr.second) == 0) process_queue.push(tr.second);
                }
            }
            // Note: assume final is in nodes
            SASSERT(nodes.count(final) != 0);
        }

        void apron_counter_system::run_abstraction() {
            unsigned int loops = 1;
            do {
                abstraction();
                loops++;
                bool widen = loops >= widening_threshold;
                if (loops >= 10) {
                    if (fixpoint_check(widen)) break;
                }
            } while (loops <= 12);
        }

    }
}
