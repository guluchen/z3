#ifndef _FORMULA_MODIFY_H
#define _FORMULA_MODIFY_H

#include <iostream>
#include <string>
#include <set>
#include <algorithm>
#include <cctype>
#include<vector>
#include <map>
//
#include "smt/theory_str/extended_flat_automaton/extended_flat_automaton.h"
#include "smt/theory_str/extended_flat_automaton/global_variable.h"


class formula_modify {
    //unsigned encoding_len;
public:
    std::pair<std::string, std::string> no_repeat(std::string left_term, std::string right_term, std::vector<std::string> &formula_set);
    //void set_encoding_len(unsigned len);
    extended_flat_automaton term_to_automaton(std::string term, std::vector<std::string>& formula_set, unsigned num_loop, unsigned size_loop, const unsigned encoding_len);
    extended_flat_automaton term_to_automaton_with_loop_size_1(std::string term, std::vector<std::string>& formula_set, unsigned num_loop, const unsigned encoding_len);
    extended_flat_automaton term_to_automaton_with_loop_size_1_and_computing_Parikh_connected_formula(std::string term, std::vector<std::string>& formula_set, unsigned num_loop, const unsigned encoding_len);
    std::string in_or_out_state_edges_sum(std::set < std::tuple <std::string, std::string, std::string>>& edge_set);
    void in_or_out_edges_sum_of_state(std::string in_or_out, std::map < std::string, std::set < std::tuple <std::string, std::string, std::string>>> &state_edge_set, std::vector<std::string>& formula_set);
    void Parikh_consistent_formula_in_edges_eql_out_edges(std::set<std::string>& Vertex, std::string initial, std::string accepting, std::vector<std::string>& formula_set);
};




#endif //_FORMULA_MODIFY_H
