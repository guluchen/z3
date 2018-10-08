#ifndef _THEORY_STR_H_
#define _THEORY_STR_H_

#include "util/trail.h"
#include "util/union_find.h"
#include "util/scoped_vector.h"
#include "util/scoped_ptr_vector.h"
#include "util/hashtable.h"
#include "ast/ast_pp.h"
#include "ast/arith_decl_plugin.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/seq_decl_plugin.h"
#include "smt/smt_theory.h"
#include "smt/params/theory_str_params.h"
#include "smt/proto_model/value_factory.h"
#include "smt/smt_model_generator.h"
#include<set>
#include<stack>
#include<vector>
#include<map>
#include<list>

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
enum sym_type{STR_VAR, STR_CONST};

class sym {

public:
    std::string content;
    sym_type type;

    sym(sym_type type, std::string content) : content(content),type(type) {}
    bool operator==(const sym &other) const;
    bool operator>(const sym &other) const;

    friend std::ostream &operator<<(std::ostream &os, const sym &s);
};
struct compare_symbol { bool operator ()( const sym &s1, const sym &s2 ) const { return s1>s2; }};


class word_term {
    std::list<sym> content;
    ast_manager & m;
public:
    word_term(ast_manager& m):m(m){}

    word_term(const word_term& other):m(other.m){
        content.insert(content.begin(),other.content.begin(),other.content.end());
    }

    void push_back(sym s);
    void push_back_string_const(expr *e);
    void push_back(word_term &other);
    void push_back_string_var(expr *e);
    void remove_front();
    size_t length() const{return content.size();};
    std::set<sym,compare_symbol> get_variables() const;
    bool has_constant() const;

    sym peek_front() const;
    void replace(const sym&  src, word_term& des);
    bool operator>(const word_term &other) const;
    word_term& operator = (const word_term & other);

    friend std::ostream &operator<<(std::ostream& os, const word_term& word_t);
    friend class word_equ;
    friend class state;


};


class word_equ {
    word_term  m_lhs;
    word_term  m_rhs;
    ast_manager & m;

public:

    word_equ(word_term& l, word_term& r):m_lhs(l), m_rhs(r), m(l.m){}
    word_equ(word_equ const& other): m_lhs(other.m_lhs), m_rhs(other.m_rhs), m(other.m) {}

    word_term const& ls() const { return m_lhs; }
    word_term const& rs() const { return m_rhs; }
    void replace(const sym&  src, word_term& des);
    void removeEquivalentPrefix();
    std::set<sym,compare_symbol> get_variables();
    bool operator>(const word_equ &other) const ;

    friend std::ostream &operator<<(std::ostream& os, const word_equ& word_t);

};
struct compare_word_equ { bool operator ()( const word_equ &p1, const word_equ &p2 ) const { return p1>p2; }};

class state {
    std::set<word_equ,compare_word_equ> weqs;
    ast_manager & m;

public:
    state(ast_manager& m):m(m){}
    void add_word_equation(word_equ input);
    std::list<state> transport();
    std::set<sym,compare_symbol> get_variables() const;
    bool operator>(const state &other) const ;
    state replace(const sym&  src, word_term& des);


    bool is_inconsistent();
    bool is_in_solved_form();

    friend std::ostream &operator<<(std::ostream& os, const state& word_t);

};
struct compare_state { bool operator ()( const state &p1, const state &p2 ) const { return p1>p2; }};

// Asserted or derived equality
class equation_pair {
    expr_ref  m_lhs;
    expr_ref  m_rhs;
public:
    equation_pair(expr_ref& l, expr_ref& r): m_lhs(l), m_rhs(r){}
    equation_pair(equation_pair const& other): m_lhs(other.m_lhs), m_rhs(other.m_rhs) {}
    expr_ref const& ls() const { return m_lhs; }
    expr_ref const& rs() const { return m_rhs; }
};


class theory_str : public theory {
public:
    theory_str(ast_manager & m, theory_str_params const & params);
    ~theory_str() override;
    void display(std::ostream & out) const override;

protected:
    int sLevel;
    theory_str_params const & m_params;
    scoped_vector<equation_pair>          m_eqs;        // set of current equations.
    scoped_vector<equation_pair>          m_nqs;        // set of current disequalities.
    void assert_axiom(expr * e);

    bool internalize_atom(app * atom, bool gate_ctx) override;
    bool internalize_term(app * term) override;
    theory_var mk_var(enode * n) override;
    void new_eq_eh(theory_var, theory_var) override;
    void new_diseq_eh(theory_var, theory_var) override;

    theory* mk_fresh(context*) override { return alloc(theory_str, get_manager(), m_params);}
    void init(context * ctx) override;
    void init_search_eh() override;
    void add_theory_assumptions(expr_ref_vector & assumptions) override;
    lbool validate_unsat_core(expr_ref_vector & unsat_core) override;
    void relevant_eh(app * n) override;
    void assign_eh(bool_var v, bool is_true) override;
    void push_scope_eh() override;
    void pop_scope_eh(unsigned num_scopes) override;
    void reset_eh() override;

    bool can_propagate() override;
    void propagate() override;
    final_check_status final_check_eh() override;

    void init_model(model_generator & m) override;
    model_value_proc * mk_value(enode * n, model_generator & mg) override;
    void finalize_model(model_generator & mg) override;
    void dump_assignments();
private:
    bool is_string_theory_term(expr *);
    decl_kind get_decl_kind(expr *);
    word_term get_word_term(expr *e);

};


};

#endif /* _THEORY_STR_H_ */
