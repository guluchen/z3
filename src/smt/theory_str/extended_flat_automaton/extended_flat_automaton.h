//
// Created by bottle on 2020/4/27.
//

#ifndef _EXTENDED_FLAT_AUTOMATON_H
#define _EXTENDED_FLAT_AUTOMATON_H

#include <iostream>
#include <string>
#include <set>
#include <algorithm>
#include <cctype>
#include<vector>
#include <map>
#include <tuple>
#include <cmath>

#include "smt/theory_str/extended_flat_automaton/global_variable.h"
#include "smt/theory_str/extended_flat_automaton/global_variable.h"


class extended_flat_automaton{
    std::string name;
    bool flat;
    bool old;
    unsigned num_loop;
    unsigned size_loop;
    
public:
    std::string v_0;
    std::string v_f;
    std::set<std::string> Vertex;
    std::set < std::tuple <std::string, std::string, std::string>> Edge;

    void hello();
    std::string get_name();
    bool is_flat();
    unsigned get_num_loop();
    unsigned get_size_loop();
//
    extended_flat_automaton();
    extended_flat_automaton(std::string given_automaton, bool is_flat, unsigned set_num_loop, unsigned set_size_loop);
    extended_flat_automaton(std::string given_automaton, bool is_flat, unsigned set_num_loop, std::vector<std::string>& formula_set);
    extended_flat_automaton(std::string given_automaton, bool is_string);
    void info();

    void make_empty();
    void concat(extended_flat_automaton A, std::vector<std::string>& formula_set);
    void concat(extended_flat_automaton A, extended_flat_automaton B, std::vector<std::string>& formula_set);
    void concat_a_string(std::string str, std::vector<std::string>& formula_set);
    //
    void concat_and_computing_Parikh_connected_formula(extended_flat_automaton A, std::vector<std::string>& formula_set, unsigned encoding_len);
    void concat_a_string_and_computing_Parikh_connected_formula(std::string str_var_name, std::string str_value, std::vector<std::string>& formula_set, unsigned encoding_len);

    void product(extended_flat_automaton A,extended_flat_automaton B, std::vector<std::string>& formula_set);

    void product_automata_and_computing_in_out_edges_of_states_and_inintial_state_used(extended_flat_automaton A, extended_flat_automaton B, std::vector<std::string>& formula_set,
        std::map<std::string, std::set < std::tuple <std::string, std::string, std::string>>> &state_in_edges, 
        std::map<std::string, std::set < std::tuple <std::string, std::string, std::string>>> &state_out_edges, 
        unsigned encoding_len);
};


#endif //_EXTENDED_FLAT_AUTOMATON_H