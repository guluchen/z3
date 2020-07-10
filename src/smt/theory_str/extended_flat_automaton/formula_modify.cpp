#include "smt/theory_str/extended_flat_automaton/formula_modify.h"




/*
void formula_modify::set_encoding_len(unsigned len)
{
    encoding_len = len;
};
*/


void var_equ_var_formluae_with_loop_size_1(std::string var_x, std::string var_y, unsigned num_loop, std::vector<std::string>& formula_set)
{
    for (unsigned i = 0; i < num_loop-1; i++)
    {
        formula_set.push_back("(= t" + LBra + var_x + std::to_string(i) + space + var_x + std::to_string(i) + RBra + " t" + LBra + var_y + std::to_string(i) + space + var_y + std::to_string(i) + RBra + ")");
        formula_set.push_back("(= t" + LBra + var_x + std::to_string(i) + space + var_x + std::to_string(i+1) + RBra + " t" + LBra + var_y + std::to_string(i) + space + var_y + std::to_string(i + 1) + RBra + ")");
    }
    if (num_loop == 1)
        formula_set.push_back("(= t" + LBra + var_x + std::to_string(0) + space + var_x + std::to_string(0) + RBra + " t" + LBra + var_y + std::to_string(0) + space + var_y + std::to_string(0) + RBra + ")");
    else
        formula_set.push_back("(= t" + LBra + var_x + std::to_string(num_loop-1) + space + var_x + std::to_string(num_loop-1) + RBra + " t" + LBra + var_y + std::to_string(num_loop-1) + space + var_y + std::to_string(num_loop-1) + RBra + ")");
};


extended_flat_automaton formula_modify::term_to_automaton_with_loop_size_1_and_computing_Parikh_connected_formula(std::string term, std::vector<std::string>& formula_set, unsigned num_loop, const unsigned encoding_len)
{
    std::string rep = "";
    for (unsigned i = 0; i < encoding_len; i++)
        rep += "$";
    const unsigned num_loop_str_automaton = 2;
    const unsigned size_loop_str_automaton = 0;
    const unsigned size_loop = 1;
    const bool flat = 1;
    if (term == "EMP" || term == "E()")
    {
        extended_flat_automaton A;
        A.make_empty();
        return A;
    }
    else
    {
        extended_flat_automaton A;
        std::set<std::string> variable_set;
        bool flag_var_dect = 0;
        bool flag_var_reading = 0;
        bool flag_str = 0;
        std::string current_var = "";
        //
        for (unsigned i = 0; i < term.length(); i++)
        {
            if (flag_var_dect == 0 && (term[i] == 'V' || term[i] == 'S'))
            {
                flag_var_dect = 1;
                if (term[i] == 'S')
                    flag_str = 1;
            }
            else if (flag_var_dect == 1 && term[i] == '(' && flag_var_reading == 1)
                std::cout << "Formula format error!";
            else if (flag_var_dect == 1 && term[i] == '(' && flag_var_reading == 0)
                flag_var_reading = 1;
            else if (flag_var_dect == 1 && term[i] != ')' && flag_var_reading == 1)
                current_var += term[i];
            else if (flag_var_dect == 1 && term[i] == ')' && flag_var_reading == 0)
                std::cout << "Formula format error!";
            else if (flag_var_dect == 1 && term[i] == ')' && flag_var_reading == 1)
            {
                flag_var_dect = 0;
                flag_var_reading = 0;
                // variable part
                if (!flag_str)
                {
                    std::string pre_var = "";
                    while (variable_set.find(current_var) != variable_set.end())
                    {
                        if (flag_var_dect == 0)
                        {
                            flag_var_dect = 1;
                            pre_var = current_var;
                        }
                        current_var += rep;
                    }
                    //
                    if (flag_var_dect == 1)
                    {
                        flag_var_dect = 0;
                        //formula_set.push_back("V(" + current_var + ")=V(" + pre_var + ")");
                        var_equ_var_formluae_with_loop_size_1(current_var, pre_var, num_loop, formula_set);
                    }
                    //
                    variable_set.insert(current_var);

                    extended_flat_automaton B(current_var, flat, num_loop, formula_set);
                    A.concat_and_computing_Parikh_connected_formula(B, formula_set, encoding_len);
                    current_var = "";
                }
                // string part
                else
                {
                    int quo = current_var.length() / encoding_len;
                    int mod = current_var.length() % encoding_len;
                    flag_str = 0;
                    for (unsigned i = 0; i < quo; i++)
                    {
                        std::string pre_var = "";
                        std::string substring = current_var.substr(i * encoding_len, encoding_len);
                        while (variable_set.find(substring) != variable_set.end())
                        {
                            if (flag_var_dect == 0)
                            {
                                flag_var_dect = 1;
                                pre_var = substring;
                            }
                            substring += rep;
                        }
                        if (flag_var_dect == 1)
                            flag_var_dect = 0;
                        else
                            pre_var = substring;
                        variable_set.insert(substring);
                        A.concat_a_string_and_computing_Parikh_connected_formula(substring, pre_var, formula_set, encoding_len);
                    }
                    if (mod != 0)
                    {
                        std::string pre_var = "";
                        std::string substring = current_var.substr(quo * encoding_len, mod);
                        while (variable_set.find(substring) != variable_set.end())
                        {
                            if (flag_var_dect == 0)
                            {
                                flag_var_dect = 1;
                                pre_var = substring;
                            }
                            substring += rep;
                        }
                        if (flag_var_dect == 1)
                            flag_var_dect = 0;
                        else
                            pre_var = substring;
                        variable_set.insert(substring);
                        A.concat_a_string_and_computing_Parikh_connected_formula(substring, pre_var, formula_set, encoding_len);
                    }
                    current_var = "";
                }

            }
        }
        return A;
    }
};

std::string formula_modify::in_or_out_state_edges_sum(std::set < std::tuple <std::string, std::string, std::string>>& edge_set)
{
    bool flag_first = 1;
    std::string edge_sum = "";

    for (std::set < std::tuple <std::string, std::string, std::string>>::iterator it = edge_set.begin(); it != edge_set.end(); it++)
    {
        /*
        if (flag_first)
            flag_first = 0;
        else
            edge_sum += "+";
        edge_sum += num_of + std::get<0>(*it) + LBra + std::get<1>(*it) + space + std::get<2>(*it) + RBra;
        */

        if (flag_first)
        {
            flag_first = 0;
            edge_sum += num_of + std::get<0>(*it) + LBra + std::get<1>(*it) + space + std::get<2>(*it) + RBra;
        }
        else
            edge_sum = "(+ " + edge_sum + " " + num_of + std::get<0>(*it) + LBra + std::get<1>(*it) + space + std::get<2>(*it) + RBra + ")";
    }
    return edge_sum;
};


void formula_modify::in_or_out_edges_sum_of_state(std::string in_or_out,
    std::map < std::string, std::set < std::tuple <std::string, std::string, std::string>>>& state_edge_set,
    std::vector<std::string>& formula_set)
{
    std::transform(in_or_out.begin(), in_or_out.end(), in_or_out.begin(), [](unsigned char c) { return std::tolower(c); });

    for (std::map<std::string, std::set < std::tuple <std::string, std::string, std::string>>>::iterator state_it = state_edge_set.begin(); state_it != state_edge_set.end(); state_it++)
    {
        
        bool flag_first = 1;
        std::string edge_sum = "";
        for (std::set < std::tuple <std::string, std::string, std::string>>::iterator edge_it = (state_it->second).begin(); edge_it != (state_it->second).end(); edge_it++)
        {
            if (flag_first)
            {
                flag_first = 0;
                edge_sum += num_of + std::get<0>(*edge_it) + LBra + std::get<1>(*edge_it) + space + std::get<2>(*edge_it) + RBra;
            }
            else
                edge_sum = "(+ " + edge_sum + " " + num_of + std::get<0>(*edge_it) + LBra + std::get<1>(*edge_it) + space + std::get<2>(*edge_it) + RBra + ")";
        }
        if (in_or_out == "in")
            formula_set.push_back("(= in" + LBra + state_it->first + RBra + " " + edge_sum + ")");
        else if (in_or_out == "out")
            formula_set.push_back("(= out" + LBra + state_it->first + RBra + " " + edge_sum + ")");
    }
    
};

void formula_modify::Parikh_consistent_formula_in_edges_eql_out_edges(std::set<std::string>& Vertex, std::string initial, std::string accepting, std::vector<std::string>& formula_set)
{

    for (std::set < std::string>::iterator it = Vertex.begin(); it != Vertex.end(); it++)
    {
        if (accepting == initial)
            formula_set.push_back("(= in" + LBra + *it + RBra + " out" + LBra + *it + RBra + ")");
        else
        {
            if (*it == initial)
                formula_set.push_back("(= (+ in" + LBra + *it + RBra + " 1) out" + LBra + *it + RBra + ")");
            else if (*it == accepting)
                formula_set.push_back("(= in" + LBra + *it + RBra + " (+ out" + LBra + *it + RBra + " 1))");
            else
                formula_set.push_back("(= in" + LBra + *it + RBra + " out" + LBra + *it + RBra + ")");
        }
    }
};








////////////////////////////////////////////////////////
// Useless for now
std::pair<std::string, std::string> formula_modify::no_repeat(std::string left_term, std::string right_term, std::vector<std::string>& formula_set)
{
	if (left_term == "E()" && right_term == "E()")
		return std::make_pair(left_term, right_term);
    else
    {
        std::string mod_left_term = ""; 
        std::string mod_right_term = "";
        std::set<std::string> variable_set;
        bool flag_var_dect = 0;
        bool flag_var_reading = 0;
        std::string current_var = "";
        // Left-hand side
        for (unsigned i = 0; i < left_term.length(); i++)
        {
            if (flag_var_dect == 0 && left_term[i] == 'V')
                flag_var_dect = 1;
            else if (flag_var_dect == 0)
                mod_left_term += left_term[i];
            else if (flag_var_dect == 1 && left_term[i] == '(' && flag_var_reading == 1)
                std::cout << "Formula format error!";
            else if (flag_var_dect == 1 && left_term[i] == '(' && flag_var_reading == 0)
                flag_var_reading = 1;
            else if (flag_var_dect == 1 && left_term[i] != ')' && flag_var_reading == 1)
                current_var += left_term[i];
            else if (flag_var_dect == 1 && left_term[i] == ')' && flag_var_reading == 0)
                std::cout << "Formula format error!";
            else if (flag_var_dect == 1 && left_term[i] == ')' && flag_var_reading == 1)
            {
                flag_var_dect = 0;
                flag_var_reading = 0;
                std::string pre_var = "";
                while (variable_set.find(current_var) != variable_set.end())
                {
                    if (flag_var_dect == 0)
                    {
                        flag_var_dect = 1;
                        pre_var = current_var;
                    }
                    current_var += "$";
                }
                //
                if (flag_var_dect == 1)
                {
                    flag_var_dect = 0;
                    formula_set.push_back("V(" + current_var + ")=V(" + pre_var + ")");
                }
                //
                variable_set.insert(current_var);
                mod_left_term += "V(" + current_var + ")";
                current_var = "";
            }
                
        }
        // Right-hand side
        for (unsigned i = 0; i < right_term.length(); i++)
        {
            if (flag_var_dect == 0 && right_term[i] == 'V')
                flag_var_dect = 1;
            else if (flag_var_dect == 0)
                mod_right_term += right_term[i];
            else if (flag_var_dect == 1 && right_term[i] == '(' && flag_var_reading == 1)
                std::cout << "Formula format error!";
            else if (flag_var_dect == 1 && right_term[i] == '(' && flag_var_reading == 0)
                flag_var_reading = 1;
            else if (flag_var_dect == 1 && right_term[i] != ')' && flag_var_reading == 1)
                current_var += right_term[i];
            else if (flag_var_dect == 1 && right_term[i] == ')' && flag_var_reading == 0)
                std::cout << "Formula format error!";
            else if (flag_var_dect == 1 && right_term[i] == ')' && flag_var_reading == 1)
            {
                flag_var_dect = 0;
                flag_var_reading = 0;
                std::string pre_var = "";
                while (variable_set.find(current_var) != variable_set.end())
                {
                    if (flag_var_dect == 0)
                    {
                        flag_var_dect = 1;
                        pre_var = current_var;
                    }
                    current_var += "$";
                }
                //
                if (flag_var_dect == 1)
                {
                    flag_var_dect = 0;
                    formula_set.push_back("V(" + current_var + ")=V(" + pre_var + ")");
                }
                //
                variable_set.insert(current_var);
                mod_right_term += "V(" + current_var + ")";
                current_var = "";
            }
        }
        return std::make_pair(mod_left_term, mod_right_term);
    }
};


extended_flat_automaton formula_modify::term_to_automaton_with_loop_size_1(std::string term, std::vector<std::string>& formula_set, unsigned num_loop, const unsigned encoding_len)
{
    std::string rep = "";
    for (unsigned i = 0; i < encoding_len; i++)
        rep += "$";
    const unsigned num_loop_str_automaton = 2;
    const unsigned size_loop_str_automaton = 0;
    const unsigned size_loop = 1;
    const bool flat = 1;
    if (term == "EMP" || term == "E()")
    {
        extended_flat_automaton A;
        A.make_empty();
        return A;
    }
    else
    {
        extended_flat_automaton A;
        std::set<std::string> variable_set;
        bool flag_var_dect = 0;
        bool flag_var_reading = 0;
        bool flag_str = 0;
        std::string current_var = "";
        //
        for (unsigned i = 0; i < term.length(); i++)
        {
            if (flag_var_dect == 0 && (term[i] == 'V' || term[i] == 'S'))
            {
                flag_var_dect = 1;
                if (term[i] == 'S')
                    flag_str = 1;
            }
            else if (flag_var_dect == 1 && term[i] == '(' && flag_var_reading == 1)
                std::cout << "Formula format error!";
            else if (flag_var_dect == 1 && term[i] == '(' && flag_var_reading == 0)
                flag_var_reading = 1;
            else if (flag_var_dect == 1 && term[i] != ')' && flag_var_reading == 1)
                current_var += term[i];
            else if (flag_var_dect == 1 && term[i] == ')' && flag_var_reading == 0)
                std::cout << "Formula format error!";
            else if (flag_var_dect == 1 && term[i] == ')' && flag_var_reading == 1)
            {
                flag_var_dect = 0;
                flag_var_reading = 0;
                // variable part
                if (!flag_str)
                {
                    std::string pre_var = "";
                    while (variable_set.find(current_var) != variable_set.end())
                    {
                        if (flag_var_dect == 0)
                        {
                            flag_var_dect = 1;
                            pre_var = current_var;
                        }
                        current_var += rep;
                    }
                    //
                    if (flag_var_dect == 1)
                    {
                        flag_var_dect = 0;
                        formula_set.push_back("V(" + current_var + ")=V(" + pre_var + ")");
                    }
                    //
                    variable_set.insert(current_var);

                    extended_flat_automaton B(current_var, flat, num_loop, size_loop);
                    A.concat(B, formula_set);
                    current_var = "";
                }
                // string part
                else
                {
                    int quo = current_var.length() / encoding_len;
                    int mod = current_var.length() % encoding_len;
                    flag_str = 0;
                    for (unsigned i = 0; i < quo; i++)
                    {
                        std::string pre_var = "";
                        std::string substring = current_var.substr(i * encoding_len, encoding_len);
                        while (variable_set.find(substring) != variable_set.end())
                        {
                            if (flag_var_dect == 0)
                            {
                                flag_var_dect = 1;
                                pre_var = substring;
                            }
                            substring += rep;
                        }
                        if (flag_var_dect == 1)
                        {
                            flag_var_dect = 0;
                            formula_set.push_back("s<" + substring + "0_" + substring + "1>=s<" + pre_var + "0_" + pre_var + "1>");
                        }
                        else
                        {
                            pre_var = substring;
                            formula_set.push_back("s<" + substring + "0_" + substring + "1>=value_of(" + pre_var + ")");
                        }
                        variable_set.insert(substring);
                        A.concat_a_string(substring, formula_set);
                    }
                    if (mod != 0)
                    {
                        std::string pre_var = "";
                        std::string substring = current_var.substr(quo * encoding_len, mod);
                        while (variable_set.find(substring) != variable_set.end())
                        {
                            if (flag_var_dect == 0)
                            {
                                flag_var_dect = 1;
                                pre_var = substring;
                            }
                            substring += rep;
                        }
                        if (flag_var_dect == 1)
                        {
                            flag_var_dect = 0;
                            formula_set.push_back("s<" + substring + "0_" + substring + "1>=s<" + pre_var + "0_" + pre_var + "1>");
                        }
                        else
                        {
                            pre_var = substring;
                            formula_set.push_back("s<" + substring + "0_" + substring + "1>=value_of(" + pre_var + ")");
                        }
                        variable_set.insert(substring);
                        A.concat_a_string(substring, formula_set);
                    }
                    current_var = "";
                }

            }
        }
        return A;
    }
};

extended_flat_automaton formula_modify::term_to_automaton(std::string term, std::vector<std::string>& formula_set, unsigned num_loop, unsigned size_loop, const unsigned encoding_len)
{
    const unsigned num_loop_str_automaton = 2;
    const unsigned size_loop_str_automaton = 0;
    if (term == "EMP" || term == "E()")
    {
        extended_flat_automaton A;
        A.make_empty();
        return A;
    }
    else
    {
        extended_flat_automaton A;
        std::set<std::string> variable_set;
        bool flag_var_dect = 0;
        bool flag_var_reading = 0;
        bool flag_str = 0;
        std::string current_var = "";
        //
        for (unsigned i = 0; i < term.length(); i++)
        {
            if (flag_var_dect == 0 && (term[i] == 'V' || term[i] == 'S'))
            {
                flag_var_dect = 1;
                if (term[i] == 'S')
                    flag_str = 1;
            }
            else if (flag_var_dect == 1 && term[i] == '(' && flag_var_reading == 1)
                std::cout << "Formula format error!";
            else if (flag_var_dect == 1 && term[i] == '(' && flag_var_reading == 0)
                flag_var_reading = 1;
            else if (flag_var_dect == 1 && term[i] != ')' && flag_var_reading == 1)
                current_var += term[i];
            else if (flag_var_dect == 1 && term[i] == ')' && flag_var_reading == 0)
                std::cout << "Formula format error!";
            else if (flag_var_dect == 1 && term[i] == ')' && flag_var_reading == 1)
            {
                flag_var_dect = 0;
                flag_var_reading = 0;
                // variable part
                if (!flag_str)
                {
                    std::string pre_var = "";
                    while (variable_set.find(current_var) != variable_set.end())
                    {
                        if (flag_var_dect == 0)
                        {
                            flag_var_dect = 1;
                            pre_var = current_var;
                        }
                        current_var += "$";
                    }
                    //
                    if (flag_var_dect == 1)
                    {
                        flag_var_dect = 0;
                        formula_set.push_back("V(" + current_var + ")=V(" + pre_var + ")");
                    }
                    //
                    variable_set.insert(current_var);

                    extended_flat_automaton B(current_var, 1, num_loop, size_loop);
                    A.concat(B, formula_set);
                    current_var = "";
                }
                // string part
                else
                {
                    int quo = current_var.length() / encoding_len;
                    int mod = current_var.length() % encoding_len;
                    flag_str = 0;
                    for (unsigned i = 0; i < quo; i++)
                    {
                        std::string pre_var = "";
                        std::string substring = current_var.substr(i * encoding_len, encoding_len);
                        while (variable_set.find(substring) != variable_set.end())
                        {
                            if (flag_var_dect == 0)
                            {
                                flag_var_dect = 1;
                                pre_var = substring;
                            }
                            substring += "$";
                        }
                        if (flag_var_dect == 1)
                        {
                            flag_var_dect = 0;
                            formula_set.push_back("S(" + substring + "(0,0)," + substring + "(1,0))=S(" + pre_var + "(0,0)," + pre_var + "(1,0))");
                        }
                        else
                        {
                            pre_var = substring;
                            formula_set.push_back("S(" + substring + "(0,0)," + substring + "(1,0))=value_of(" + pre_var + ")");
                        }
                        variable_set.insert(substring);
                        extended_flat_automaton B(substring, 1);
                        A.concat(B, formula_set);
                    }
                    if (mod != 0)
                    {
                        std::string pre_var = "";
                        std::string substring = current_var.substr(quo * encoding_len, mod);
                        while (variable_set.find(substring) != variable_set.end())
                        {
                            if (flag_var_dect == 0)
                            {
                                flag_var_dect = 1;
                                pre_var = substring;
                            }
                            substring += "$";
                        }
                        if (flag_var_dect == 1)
                        {
                            flag_var_dect = 0;
                            formula_set.push_back("S(" + substring + "(0,0)," + substring + "(1,0))=S(" + pre_var + "(0,0)," + pre_var + "(1,0))");
                        }
                        else
                        {
                            pre_var = substring;
                            formula_set.push_back("S(" + substring + "(0,0)," + substring + "(1,0))=value_of(" + pre_var + ")");
                        }
                        variable_set.insert(substring);
                        extended_flat_automaton B(substring, 1);
                        A.concat(B, formula_set);
                    }
                    current_var = "";
                }

            }
        }
        return A;
    }
};