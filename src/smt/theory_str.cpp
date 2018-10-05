#include "ast/ast_smt2_pp.h"
#include "smt/smt_context.h"
#include "smt/theory_str.h"
#include "smt/smt_model_generator.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include<algorithm>
#include "smt/theory_seq_empty.h"
#include "smt/theory_arith.h"
#include "ast/ast_util.h"
#include "ast/rewriter/seq_rewriter.h"
#include "smt_kernel.h"

namespace smt {
    theory_str::theory_str(ast_manager & m, theory_str_params const & params):
    theory(m.mk_family_id("seq")),
    sLevel(0),
    m_params(params)
    {
    }

    theory_str::~theory_str() {

    }

    void theory_str::init(context * ctx) {
        theory::init(ctx);
    }

    bool theory_str::internalize_atom(app * atom, bool gate_ctx) {
        return internalize_term(atom);
    }

    bool theory_str::internalize_term(app * term) {
        context & ctx = get_context();
        ast_manager & m = get_manager();
        SASSERT(term->get_family_id() == get_family_id());

        TRACE("str", tout << "internalizing term: " << mk_ismt2_pp(term, get_manager()) << std::endl;);

        unsigned num_args = term->get_num_args();
        for (unsigned i = 0; i < num_args; ++i) {
            ctx.internalize(term->get_arg(i), false);
        }
        if (ctx.e_internalized(term)) {
            enode * e = ctx.get_enode(term);
            mk_var(e);
            return true;
        }
//        std::cout << "the term: " << mk_ismt2_pp(term, get_manager()) << " is bool? "<< m.is_bool(term) << std::endl;
        enode * e = ctx.mk_enode(term, false, m.is_bool(term), true);
        if (m.is_bool(term)) {
            bool_var bv = ctx.mk_bool_var(term);
            ctx.set_var_theory(bv, get_id());
            ctx.set_enode_flag(bv, true);
        }
        // make sure every argument is attached to a theory variable
        for (unsigned i = 0; i < num_args; ++i) {
            enode * arg = e->get_arg(i);
            theory_var v_arg = mk_var(arg);
            TRACE("str", tout << "arg has theory var #" << v_arg << std::endl;); (void)v_arg;
        }

        theory_var v = mk_var(e);
        TRACE("str", tout << "term has theory var #" << v << std::endl;);
        return true;
    }

    theory_var theory_str::mk_var(enode* n) {
        TRACE("str", tout << "mk_var for " << mk_pp(n->get_owner(), get_manager()) << std::endl;);
//        ast_manager & m = get_manager();
        if (!(is_string_theory_term(n->get_owner()))) {
            return null_theory_var;
        }
        if (is_attached_to_var(n)) {
            TRACE("str", tout << "already attached to theory var v#" << n->get_th_var(get_id()) << std::endl;);
            return n->get_th_var(get_id());
        } else {
            theory_var v = theory::mk_var(n);
            TRACE("str", tout << "new theory var v#" << v << " find " << get_enode(v) << std::endl;);
            get_context().attach_th_var(n, this, v);
            get_context().mark_as_relevant(n);
            return v;
        }
    }

    bool theory_str::can_propagate() {
        return false;
    }

    void theory_str::propagate() {
        TRACE("str", tout << "propagating..." << std::endl;);
    }

    void theory_str::reset_eh() {
        TRACE("str", tout << "resetting" << std::endl;);
    }

    void theory_str::add_theory_assumptions(expr_ref_vector & assumptions) {
        TRACE("str", tout << "add theory assumption for theory_str" << std::endl;);
    }

    lbool theory_str::validate_unsat_core(expr_ref_vector & unsat_core) {
        return l_undef;
    }

    void theory_str::init_search_eh() {

    }

    void theory_str::new_eq_eh(theory_var x, theory_var y) {


        ast_manager & m = get_manager();
        enode* n1 = get_enode(x);
        enode* n2 = get_enode(y);
        expr_ref e1(n1->get_owner(), m);
        expr_ref e2(n2->get_owner(), m);
        equation_pair weq1(e1, e2);
//        std::cout << "new equality " << get_context().get_scope_level() << ": "<<
//        mk_ismt2_pp(get_enode(x)->get_owner(), get_manager()) << " = " <<
//        mk_ismt2_pp(get_enode(y)->get_owner(), get_manager()) << std::endl;

        m_eqs.push_back(weq1);
        TRACE("str", tout << "new eq: " << mk_ismt2_pp(get_enode(x)->get_owner(), get_manager()) << " = " <<
              mk_ismt2_pp(get_enode(y)->get_owner(), get_manager()) << std::endl;);
    }

    void theory_str::new_diseq_eh(theory_var x, theory_var y) {
        ast_manager & m = get_manager();
        enode* n1 = get_enode(x);
        enode* n2 = get_enode(y);
        expr_ref e1(n1->get_owner(), m);
        expr_ref e2(n2->get_owner(), m);
        equation_pair weq1(e1, e2);
//        std::cout << "new disequality " << get_context().get_scope_level() << ": "<<
//                  mk_ismt2_pp(get_enode(x)->get_owner(), get_manager()) << " = " <<
//                  mk_ismt2_pp(get_enode(y)->get_owner(), get_manager()) << std::endl;

        m_nqs.push_back(weq1);
        TRACE("str", tout << "new diseq: " << mk_ismt2_pp(get_enode(x)->get_owner(), get_manager()) << " = " <<
                          mk_ismt2_pp(get_enode(y)->get_owner(), get_manager()) << std::endl;);
    }

    void theory_str::relevant_eh(app * n) {
        TRACE("str", tout << "relevant: " << mk_ismt2_pp(n, get_manager()) << std::endl;);
    }

    void theory_str::assign_eh(bool_var v, bool is_true) {
        //YFC:membership constraint goes here
        std::cout << "assign: v" << v << " #" << get_context().bool_var2expr(v)->get_id() << " is_true: " << is_true << std::endl;

        TRACE("str", tout << "assign: v" << v << "--> " << mk_ismt2_pp(get_context().bool_var2expr(v), get_manager()) << " is_true: " << is_true << std::endl;);
    }

    void theory_str::push_scope_eh() {
        sLevel += 1;
        m_eqs.push_scope();
        m_nqs.push_scope();
     //   std::cout<< "push to " << sLevel << std::endl;
        TRACE("str", tout << "push to " << sLevel << std::endl;);
    }

    void theory_str::pop_scope_eh(unsigned num_scopes) {
        sLevel -= num_scopes;
        m_eqs.pop_scope(num_scopes);
        m_nqs.pop_scope(num_scopes);

     //   std::cout<< "pop " << num_scopes << " to " << sLevel << std::endl;
        TRACE("str", tout << "pop " << num_scopes << " to " << sLevel << std::endl;);

    }

    final_check_status theory_str::final_check_eh() {
//        context & ctx = get_context();
        ast_manager & m = get_manager();
        std::cout<< "level: " << get_context().get_scope_level() << "\n"<<std::endl;

        state root(m);


        for (auto const& e : m_eqs) {
            word_term lhs=get_word_term(e.ls());
            word_term rhs=get_word_term(e.rs());


            root.add_word_equation(word_equ(lhs,rhs));
            root.add_word_equation(word_equ(lhs,rhs));
            root.add_word_equation(word_equ(rhs,lhs));
        }
        std::cout<<root<<std::endl;

        std::list<state> next=root.transport();

        for(auto& st:next){
            std::cout<<st<<std::endl;
        }
        std::cout<<root<<std::endl;

        //The word equations are UNSAT, remove them from the solution space
        expr* toAssert=NULL;
        for (auto const& e : m_eqs) {
            expr* exp=m.mk_not(mk_eq_atom( e.ls(),e.rs()));
            if(toAssert==NULL){
                toAssert=exp;
            }else{
                toAssert = m.mk_or(toAssert, exp);
            }
            std::cout << e.ls() << " = " << e.rs() << " \n";
        }

        for (auto const& e : m_nqs) {
            expr* exp=mk_eq_atom( e.ls(),e.rs());
            if(toAssert==NULL){
                toAssert=exp;
            }else{
                toAssert = m.mk_or(toAssert, exp);
            }
            std::cout << e.ls() << " != " << e.rs() << " \n";
        }

        if(toAssert!=NULL) {
            std::cout << "asserting " << mk_pp(toAssert, m) << std::endl;
            assert_axiom(toAssert);
            TRACE("str", tout << "final check" << std::endl;);
            return FC_CONTINUE;

        }else {
            TRACE_CODE(dump_assignments(););
            return FC_DONE;
        }
    }
    void theory_str::init_model(model_generator & mg) {
        TRACE("str", tout << "initializing model" << std::endl;);

    }

    model_value_proc * theory_str::mk_value(enode * n, model_generator & mg) {
        TRACE("str", tout << "mk_value for: " << mk_ismt2_pp(n->get_owner(), get_manager()) <<
                          " (sort " << mk_ismt2_pp(get_manager().get_sort(n->get_owner()), get_manager()) << ")" << std::endl;);
        ast_manager & m = get_manager();
        app_ref owner(m);
        owner = n->get_owner();

        // If the owner is not internalized, it doesn't have an enode associated.
        SASSERT(get_context().e_internalized(owner));

        return alloc(expr_wrapper_proc, owner);

    }

    void theory_str::finalize_model(model_generator & mg) {}
    void theory_str::display(std::ostream & out) const {
        out << "TODO: theory_str display" << std::endl;
    }






    /*=====================================
     *
     * Helper functions of string theory
     *
     *=====================================*/


    void theory_str::dump_assignments() {
        TRACE_CODE(
                ast_manager & m = get_manager();
                context & ctx = get_context();
                tout << "dumping all assignments:" << std::endl;
                expr_ref_vector assignments(m);
                ctx.get_assignments(assignments);
                for (expr_ref_vector::iterator i = assignments.begin(); i != assignments.end(); ++i) {
                    expr * ex = *i;
                    tout << mk_ismt2_pp(ex, m) << (ctx.is_relevant(ex) ? "" : " (NOT REL)") << std::endl;
                }
        );
    }

    void theory_str::assert_axiom(expr * _e) {
        if (_e == nullptr)
            return;

        if (get_manager().is_true(_e)) return;
        context & ctx = get_context();
        ast_manager& m = get_manager();
        TRACE("str", tout << "asserting " << mk_ismt2_pp(_e, m) << std::endl;);


        expr_ref e(_e, m);
        if (!ctx.b_internalized(e)) {
            ctx.internalize(e, false);
        }
        literal lit(ctx.get_literal(e));
        ctx.mark_as_relevant(lit);
        ctx.mk_th_axiom(get_id(), 1, &lit);

    }

    bool theory_str::is_string_theory_term(expr *e){
        ast_manager & m = get_manager();
        return (m.get_sort(e) == m.mk_sort(m.mk_family_id("seq"), _STRING_SORT, 0, nullptr));
    }

    decl_kind theory_str::get_decl_kind(expr *e) {
        return to_app(e)->get_decl_kind();
    }

    word_term theory_str::get_word_term(expr *e){
        word_term result(get_manager());

        if(get_decl_kind(e)==OP_STRING_CONST){
            result.push_back_string_const(e);

        }else if(get_decl_kind(e)==OP_SEQ_CONCAT){
            unsigned num_args = to_app(e)->get_num_args();
            for (unsigned i = 0; i < num_args; ++i) {
                word_term sub_term=get_word_term(to_app(e)->get_arg(i));
                result.push_back(sub_term);
            }

        }else {//is variable
            result.push_back_string_var(e);
        }

        return result;
    }


    /*=====================================
     *
     * For output
     *
     *=====================================*/



    std::ostream& operator<<(std::ostream& os, const sym& s) {
        if(s.type==STR_VAR){
            os<<"V("<<s.content<<")";
        }else{
            os<<" "<<s.content<<" ";
        }
        return os;
    }

    std::ostream &operator<<(std::ostream& os, const word_term& word_t) {
        for(auto const& s:word_t.content){
            os<<s;
        }
        return os;
    }

    std::ostream &operator<<(std::ostream& os, const word_equ& word_e){
        os<<word_e.m_lhs<<" = "<<word_e.m_rhs;
        return os;
    }

    std::ostream &operator<<(std::ostream& os, const state& st){
        for(auto const& we:st.weqs){
            os<<we;
            os<<std::endl;
        }
        return os;
    }

    /*=====================================
     *
     * For sym class
     *
     *=====================================*/

    bool sym::operator==(const sym &other) const {
        if (other.type != type) return false;
        else if (other.content != content) return false;
        else return true;
    }
    bool sym::operator>(const sym &other) const {
        if (type < other.type) return false;
        else if (type > other.type) return true;
        else return content > other.content;
    }

    /*=====================================
     *
     * For word_term class
     *
     *=====================================*/


    void word_term::push_back_string_const(expr *e){
        std::stringstream ss;
        ss << mk_ismt2_pp(e, m);
        std::string name = ss.str();
        for(int i=name.length()-2;i>0;i--){
            content.insert(content.end(),sym(STR_CONST, name.substr(i,1)));
        }
    }
    void word_term::push_back(word_term &other){
        content.insert(content.end(),other.content.begin(),other.content.end());
    }
    void word_term::push_back(sym s){
        content.push_back(s);
    }

    std::set<sym,compare_symbol> word_term::get_variables() const{
        std::set<sym,compare_symbol> result;
        for(auto& s:content){
            if(s.type==STR_VAR){
                result.insert(s);
            }
        }

        return result;
    }

    bool word_term::has_constant() const{
        for(auto& s:content){
            if(s.type==STR_CONST){
                return true;
            }
        }
        return false;
    }

    void word_term::push_back_string_var(expr *e){
        std::stringstream ss;
        ss << mk_ismt2_pp(e, m);
        std::string name = ss.str();
        content.insert(content.end(),sym(STR_VAR, name));
    }
    void word_term::remove_front(){
        content.pop_front();
    }
    sym word_term::peek_front() const{
        return *content.begin();
    }


    void word_term::replace(const sym&  src, word_term& des){
        std::list<sym>::iterator findIter = std::find(content.begin(),content.end(),src);
        while(findIter!=content.end()){
            content.insert(findIter, des.content.begin(),des.content.end());
            content.erase(findIter++);
            findIter = std::find(findIter,content.end(),src);
        }
    }

    bool word_term::operator>(const word_term &other) const {
        if (content.size() > other.content.size()) return true;
        else if (content.size() < other.content.size()) return false;
        else {
            std::list<sym>::const_iterator otherIter=other.content.begin();
            for(std::list<sym>::const_iterator myIter=content.begin();myIter!=content.end();myIter++){
                if(*myIter>*otherIter) return true;
                else if (*otherIter>*myIter) return false;
                otherIter++;
            }
        }
        return false;
    }

    word_term& word_term::operator = (const word_term & other) {
        content.insert(content.begin(),other.content.begin(),other.content.end());
        return *this;
    }

    /*=====================================
    *
    * For word_equ class
    *
    *=====================================*/

    std::set<sym,compare_symbol> word_equ::get_variables() {
        std::set<sym,compare_symbol> result;
        for(auto& s:m_lhs.content){
            if(s.type==STR_VAR){
                result.insert(s);
            }
        }
        for(auto& s:m_rhs.content){
            if(s.type==STR_VAR){
                result.insert(s);
            }
        }

        return result;
    }

    void word_equ::replace(const sym&  src, word_term& des){
        m_lhs.replace(src,des);
        m_rhs.replace(src,des);
    }

    bool word_equ::operator>(const word_equ &other) const {
        word_term my_larger_word_equ=m_lhs>m_rhs?m_lhs:m_rhs;
        word_term my_smaller_word_equ=m_lhs>m_rhs?m_rhs:m_lhs;

        word_term other_larger_word_equ=other.m_lhs>other.m_rhs?other.m_lhs:other.m_rhs;
        word_term other_smaller_word_equ=other.m_lhs>other.m_rhs?other.m_rhs:other.m_lhs;

        if(my_smaller_word_equ>other_smaller_word_equ) return true;
        else if (other_smaller_word_equ>my_smaller_word_equ) return false;
        else if(my_larger_word_equ>other_larger_word_equ) return true;
        else return false;
    }

    void word_equ::removeEquivalentPrefix(){
        while(m_lhs.peek_front().content==m_rhs.peek_front().content && m_lhs.peek_front().type==m_rhs.peek_front().type) {
            m_lhs.remove_front();
            m_rhs.remove_front();
        }
    }

    /*=====================================
     *
     * For state class
     *
     *=====================================*/

    void state::add_word_equation(word_equ input){
        weqs.insert(input);
    }

    bool state::is_inconsistent(){

        for(auto& weq: weqs){
            if( (weq.ls().length()==0 && weq.rs().has_constant()) ||
                (weq.rs().length()==0 && weq.ls().has_constant()) ){
                return true;
            }
        }

    }
    bool state::is_in_solved_form(){


    }


    std::list<state> state::transport(){

        std::list<state> result;

        //the state is inconsistent, matching an empty word term with a non-empty one
        for(auto& weq: weqs){
            if( (weq.ls().length()==0 && weq.rs().has_constant()) ||
                (weq.rs().length()==0 && weq.ls().has_constant()) ){
                return result;
            }
        }



        std::list<sym> source;
        std::list<word_term> destination;

        word_equ main_equation=*weqs.begin();

        word_term lhs=main_equation.ls();
        word_term rhs=main_equation.rs();

        //remove symbols that are identical in both word terms
        while(lhs.peek_front().content==rhs.peek_front().content && lhs.peek_front().type==rhs.peek_front().type){
            lhs.remove_front();
            rhs.remove_front();
        }

        //if both are string constant and their content are different, this state is inconsistent and we can stop.
        if (lhs.peek_front().type==STR_CONST && rhs.peek_front().type==STR_CONST)return result;

        if(lhs.peek_front().type==STR_VAR && rhs.peek_front().type==STR_VAR){
            //Encountered the case X...=Y...
            //X => epsilon
            source.push_back(lhs.peek_front());
            destination.push_back(word_term(m));
            //Y => epsilon
            source.push_back(rhs.peek_front());
            destination.push_back(word_term(m));
            //X => YX
            source.push_back(lhs.peek_front());
            word_term dest1(m);
            dest1.push_back(rhs.peek_front());
            dest1.push_back(lhs.peek_front());
            destination.push_back(dest1);
            //Y => XY
            source.push_back(rhs.peek_front());
            word_term dest2(m);
            dest2.push_back(lhs.peek_front());
            dest2.push_back(rhs.peek_front());
            destination.push_back(dest2);
            //X => Y
            source.push_back(lhs.peek_front());
            word_term dest3(m);
            dest3.push_back(rhs.peek_front());
            destination.push_back(dest3);
        }else{
            sym *vsym,*csym;

            //the types of the fronts of lhs and rhs are different
            if(lhs.peek_front().type==STR_VAR){
                sym var=lhs.peek_front();
                vsym=&var;
                sym con=rhs.peek_front();
                csym=&con;
            }else{
                sym var=rhs.peek_front();
                vsym=&var;
                sym con=lhs.peek_front();
                csym=&con;
            }

            //X => epsilon
            source.push_back(*vsym);
            destination.push_back(word_term(m));

            //X => aX
            source.push_back(*vsym);
            word_term dest1(m);
            dest1.push_back(*csym);
            dest1.push_back(*vsym);
            destination.push_back(dest1);

            //X => a
            source.push_back(*vsym);
            word_term dest2(m);
            dest2.push_back(*csym);
            destination.push_back(dest2);
        }

        std::list<sym>::iterator source_iter=source.begin();
        std::list<word_term>::iterator destination_iter=destination.begin();

        while(source_iter!=source.end()){
            state to_result(m);

            for(auto s:weqs){
                s.replace(*source_iter,*destination_iter);
                s.removeEquivalentPrefix();

                to_result.add_word_equation(s);
            }
            source_iter++;
            destination_iter++;
            result.push_back(to_result);
        }


        return result;
    }

}; /* namespace smt */
