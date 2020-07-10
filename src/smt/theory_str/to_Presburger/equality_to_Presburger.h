#ifndef _EQUALITY_TO_PRESBURGER_H
#define _EQUALITY_TO_PRESBURGER_H

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
#include <smt/params/smt_params.h>
#include "ast/arith_decl_plugin.h"
#include "ast/seq_decl_plugin.h"
#include "smt/params/theory_str_params.h"
#include "smt/smt_kernel.h"
#include "smt/smt_theory.h"
#include "smt/smt_arith_value.h"
#include "util/scoped_vector.h"
#include "util/union_find.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/th_rewriter.h"




class formula_modifier {
	unsigned loop_size = 3;
	unsigned loop_num = 2;



public:
	void equality_in(std::string L_term, std::string R_term, std::vector<std::string>& formula_set);
	void inequality_in(std::string L_term, std::string R_term, std::vector<std::string>& formula_set);


};


#endif //_EQUALITY_TO_PRESBURGER_H