#include "smt/theory_str/to_Presburger/equality_to_Presburger.h"

void formula_modifier::equality_in(std::string L_term, std::string R_term, std::vector<std::string>& formula_set)
{
    
};





// not fin
void formula_modifier::inequality_in(std::string L_term, std::string R_term, std::vector<std::string>& formula_set)
{
	std::cout << "\nHello! Yen.\n";
	std::vector<std::string> eq_formula_set;
	equality_in(L_term, R_term, eq_formula_set);
	return;
};