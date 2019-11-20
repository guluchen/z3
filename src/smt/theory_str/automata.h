#ifndef THEORY_STR_AUTOMATA_H_
#define THEORY_STR_AUTOMATA_H_


#include <functional>
#include <list>
#include <set>
#include <stack>
#include <map>
#include <memory>
#include <queue>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include "ast/arith_decl_plugin.h"
#include "ast/seq_decl_plugin.h"
#include "smt/params/theory_str_params.h"
#include "smt/smt_kernel.h"
#include "smt/smt_theory.h"
#include "util/scoped_vector.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/th_rewriter.h"

#include <fst/fstlib.h>
#include <fst/script/print.h>

namespace smt {

    namespace str {

        class automaton {
        public:
            const static unsigned maximal_char=255;
            using ptr = std::unique_ptr<automaton>;
            using sptr = std::shared_ptr<automaton>;
            using ptr_pair = std::pair<ptr, ptr>;
            using state = unsigned;
            using len_offset = unsigned;
            using len_period = unsigned;
            using len_constraint = std::pair<len_offset, len_period>;
            static const unsigned MAX_CHAR_NUM = 255;
        public:
            virtual ~automaton() = 0;
            virtual bool is_empty() = 0;
            virtual bool is_deterministic() = 0;
            virtual bool is_final(state s) { std::set<state> finals = get_finals(); return finals.find(s) != finals.end(); }
            virtual state get_init() = 0;
            virtual std::set<state> get_finals() = 0;
            virtual ptr clone() = 0;
            virtual ptr simplify() { return clone(); }
            virtual ptr determinize() = 0;
            virtual ptr complement() = 0;
            virtual ptr append(sptr other) = 0;
            virtual ptr intersect_with(sptr other) = 0;
            virtual ptr union_with(sptr other) = 0;
            virtual std::list<ptr> remove_prefix(const zstring& prefix);
            virtual std::list<ptr_pair> split();
            virtual void set_init(state s) = 0;
            virtual void add_final(state s) = 0;
            virtual void remove_final(state s) = 0;
            virtual std::set<state> reachable_states() { return reachable_states(get_init()); }
            virtual std::set<state> reachable_states(state s) = 0;
            virtual std::set<state> successors(state s) = 0;
            virtual std::set<state> successors(state s, const zstring& ch) = 0;
            virtual std::set<len_constraint> length_constraints() = 0;
            virtual std::ostream& display(std::ostream& os) = 0;
            virtual bool operator==(const automaton& other) = 0;
            virtual bool operator!=(const automaton& other) { return !(*this == other); }
            friend std::ostream& operator<<(std::ostream& os, automaton::sptr a);
        };

        class automaton_factory {
        public:
            using sptr = std::shared_ptr<automaton_factory>;
        public:
            virtual ~automaton_factory() = 0;
            virtual automaton::sptr mk_empty() = 0;
            virtual automaton::sptr mk_universe() { return mk_empty()->complement(); }
            virtual automaton::sptr mk_from_word(const zstring& str) = 0;
            virtual automaton::sptr mk_from_re_expr(expr *re, bool minimize_result) = 0;
        };

        class zaut : public automaton {
        public:
            using internal = ::automaton<sym_expr, sym_expr_manager>;
            using move = internal::move;
            using moves = internal::moves;
            using maker = re2automaton;
            using handler = symbolic_automata<sym_expr, sym_expr_manager>;
            using symbol = sym_expr;
            using symbol_ref = obj_ref<sym_expr, sym_expr_manager>;
            using symbol_manager = sym_expr_manager;
            class symbol_boolean_algebra : public boolean_algebra<sym_expr *> {
            public:
                using expr = symbol *;
                struct displayer {
                    std::ostream& display(std::ostream& os, expr e) { return e->display(os); }
                };
            private:
                ast_manager& m_ast_man;
                expr_solver& m_solver;
            public:
                symbol_boolean_algebra(ast_manager& m, expr_solver& s);
                expr mk_true() override;
                expr mk_false() override;
                expr mk_and(expr e1, expr e2) override;
                expr mk_and(unsigned size, const expr *es) override;
                expr mk_or(expr e1, expr e2) override;
                expr mk_or(unsigned size, const expr *es) override;
                expr mk_not(expr e) override;
                lbool is_sat(expr e) override;
            };
            class symbol_solver : public expr_solver {
                kernel m_kernel;
            public:
                symbol_solver(ast_manager& m, smt_params& p) : m_kernel{m, p} {
                    STRACE("str", tout << __LINE__ << " enter " << __FUNCTION__ << std::endl;);
                    STRACE("str", tout << __LINE__ << " leave " << __FUNCTION__ << std::endl;);
                }
                lbool check_sat(expr *e) override;
            };
            struct dependency_ref {
                ast_manager& ast_man;
                seq_util& util_s;
                symbol_manager& sym_man;
                symbol_boolean_algebra& sym_ba;
                handler& han;
                using am = ast_manager;
                using sm = symbol_manager;
                using sba = symbol_boolean_algebra;
                using h = handler;
                dependency_ref(am& m, seq_util& su, sm& sm, sba& sba, h& h);
            };
        private:
            internal *m_imp;
            dependency_ref m_dep;
        public:
            zaut(internal *a, dependency_ref dep) : m_imp{a}, m_dep{dep} {}
            ~zaut() override { dealloc(m_imp); }
            bool is_empty() override { return m_imp->is_empty(); }
            bool is_deterministic() override;
            bool is_final(state s) override { return m_imp->is_final_state(s); }
            state get_init() override { return m_imp->init(); }
            std::set<state> get_finals() override;
            ptr clone() override;
            ptr determinize() override;
            ptr complement() override;
            ptr intersect_with(sptr other) override;
            ptr union_with(sptr other) override;
            ptr append(sptr other) override;
            void set_init(state s) override;
            void add_final(state s) override;
            void remove_final(state s) override;
            std::set<state> reachable_states(state s) override;
            std::set<state> successors(state s) override;
            std::set<state> successors(state s, const zstring& ch) override;
            std::set<len_constraint> length_constraints() override;
            std::ostream& display(std::ostream& out) override;
            std::ostream& display_timbuk(std::ostream& out);
            bool operator==(const automaton& other) override;
        private:
            std::set<state> epsilon_closure(state s);
            moves transitions();
            moves transform_transitions(std::function<move(move)> transformer);
            symbol *mk_char(const zstring& ch);
            lbool symbol_check_sat(const symbol_ref& s);
            bool contains(const zaut& other) const;
            ptr mk_ptr(internal *&& a) const;
        };

        class oaut : public automaton {
        public:
            using internal = fst::StdVectorFst;
            using symbol = fst::StdArc::Label;
            using moves = fst::StdArc;
            using StateId = int;
            using Label = int;
            const float Zero = std::numeric_limits<float>::infinity();
            const float One = 0;
        private:
            internal m_imp;
        public:
            explicit oaut(internal a);
            ~oaut() override = default;
            bool is_empty() override;
            bool is_deterministic() override;
            state get_init() override { return m_imp.Start(); }
            std::set<state> get_finals() override;
            ptr clone() override;
            ptr determinize() override;
            oaut::ptr complement() override;
            ptr intersect_with(sptr other) override;
            ptr union_with(sptr other) override;
            state add_state(){return m_imp.AddState();};
            void set_init(state s) override {m_imp.SetStart(s);};
            void add_final(state s) override {m_imp.SetFinal(s, One);};
            void remove_final(state s) override {m_imp.SetFinal(s, Zero);};
            ptr append(sptr other) override;
            std::set<state> reachable_states(state s) override;
            std::set<state> successors(state s) override;
            std::set<state> successors(state s, const zstring& ch) override;
            std::set<len_constraint> length_constraints() override;
            std::ostream& display_timbuk(std::ostream& os);
            std::ostream& display(std::ostream& os) override;
            std::ostream& display(std::ostream& os, const std::string& description);
            bool operator==(const automaton& other) override;
            friend class oaut_adaptor;
        private:
            fst::StdArc makeArc(Label symbol, StateId to) {
                return fst::StdArc(symbol, symbol, 0, to);
            };
            void cloneInternalStructure(internal& out);
            void totalize();
        };

        class zaut_adaptor : public automaton_factory {
            ast_manager& m_ast_man;
            seq_util m_util_s;
            zaut::maker m_aut_make;
            zaut::symbol_manager *m_sym_man;
            zaut::symbol_solver *m_sym_solver;
            zaut::symbol_boolean_algebra *m_sym_ba;
            zaut::handler *m_aut_man;
            std::map<std::string, zaut::sptr> m_re_aut_cache;
        public:
            zaut_adaptor(ast_manager& m, context& ctx);
            ~zaut_adaptor() override;
            automaton::sptr mk_empty() override;
            automaton::sptr mk_from_word(const zstring& str) override;
            automaton::sptr mk_from_re_expr(expr *re, bool minimize_result) override;
        };

        class oaut_adaptor : public automaton_factory {
            using StateId = int;
            using Label = int;
            const float Zero = std::numeric_limits<float>::infinity();
            const float One = 0;

            ast_manager& m;
            seq_util m_util_s;
        public:
            oaut_adaptor(ast_manager& m, context& ctx) : m{m}, m_util_s{m} {}
            automaton::sptr mk_empty() override;
            automaton::sptr mk_from_word(const zstring& str) override;
            automaton::sptr mk_from_re_expr(expr *re, bool minimize_result) override;

        private:
            std::shared_ptr<oaut> mk_oaut_from_re_expr(expr *re);
            unsigned exprToUnsigned(expr *);
            fst::StdArc makeArc(Label symbol, StateId to) {
                return fst::StdArc(symbol, symbol, One, to);
            };
        };

    }
}
#endif //THEORY_STR_AUTOMATA_H_
