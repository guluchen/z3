#include "smt/theory_str/extended_flat_automaton/extended_flat_automaton.h"




// Initialization Part
extended_flat_automaton::extended_flat_automaton()
{
    name = "EMP";
    flat = 1;
    old = 0;
    num_loop = 0;
    size_loop = 0;
};


unsigned value_of_string_without_considering_IntStrConversion(std::string str, unsigned encoding_len, bool is_emp_str)
{
    if (str == "EMP" && is_emp_str)
        return 0;
    unsigned val_str=0;
    for (unsigned i = 0; i < str.length(); i++)
    {
        val_str += int(str[i]) * std::pow(128, str.length() - i - 1);
    }
    return val_str;
};


extended_flat_automaton::extended_flat_automaton(std::string given_automaton, bool is_flat, unsigned set_num_loop, std::vector<std::string>& formula_set)
{
    std::transform(given_automaton.begin(), given_automaton.end(), given_automaton.begin(), [](unsigned char c) { return std::tolower(c); });
    name = given_automaton;
    flat = is_flat; // 1-> flat
    old = 1;
    num_loop = set_num_loop;
    size_loop = 1;

    if (num_loop < 1)
    {
        std::cout << "Error: num_loop < 1\n";
        return;
    }

    v_0 = name + "0";
    v_f = name + std::to_string(num_loop - 1);

    for (unsigned i = 0; i < num_loop - 1; i++)
    {
        Vertex.insert(name + std::to_string(i));
        Edge.insert(std::make_tuple("t", name + std::to_string(i), name + std::to_string(i)));
        Edge.insert(std::make_tuple("t", name + std::to_string(i), name + std::to_string(i + 1)));
        formula_set.push_back("(= " + num_of + "t" + LBra + name + std::to_string(i) + space + name + std::to_string(i+1) + RBra + " 1)");
    }
    if (num_loop == 1)
    {
        Vertex.insert(name + std::to_string(0));
        Edge.insert(std::make_tuple("t", name + std::to_string(0), name + std::to_string(0)));
    }
    else
    {
        Vertex.insert(name + std::to_string(num_loop - 1));
        Edge.insert(std::make_tuple("t", name + std::to_string(num_loop - 1), name + std::to_string(num_loop - 1)));
    }
};


////////////////////////////




void extended_flat_automaton::info()
{

    std::cout << "<<<Info>>>\nname: " + name + "\n";
    std::cout << "Flat: " << flat << "\n";
    std::cout << "Old: " << old << "\n";
    std::cout << "Number of loops: " << num_loop << "\n";
    std::cout << "Size of each loop: " << size_loop << "\n";
    std::cout << "Initail and final states: " << v_0 << " and " << v_f << "\n\n";
    std::cout << "Vertex: ";
    for (std::set<std::string>::iterator it = Vertex.begin(); it != Vertex.end(); it++)
        std::cout << ' ' << *it;
    std::cout << "\n\n";
    std::cout << "Edge: \n";
    for (std::set<std::tuple <std::string, std::string, std::string>>::iterator it = Edge.begin(); it != Edge.end(); it++)
        std::cout << "Type: " << std::get<0>(*it) << ", 1st node: " << std::get<1>(*it) << ", 2nd node: " << std::get<2>(*it) << "\n";
    std::cout << "\n";
};


void extended_flat_automaton::make_empty()
{
    if (old)
    {
        std::cout << "Unalble to make. (not new)\n";
        return;
    }
    else
    {
        if (name != "EMP")
        {
            std::cout << "Unable to make. (name given)\n";
            return;
        }
        else
        {
            old = 1;
            name = "EMP";
            num_loop = 1;
            v_0 = "x";
            v_f = v_0;
            Vertex.insert(v_0);
        }
    }
        
};



void extended_flat_automaton::concat_and_computing_Parikh_connected_formula(extended_flat_automaton A, std::vector<std::string>& formula_set, unsigned encoding_len)
{
    bool is_emp_str = 1;
    if (name == "EMP" && !old)
    {
        name = A.name;
        flat = A.flat;
        old = A.old;
        num_loop = A.num_loop;
        size_loop = A.size_loop;
        v_0 = A.v_0;
        v_f = A.v_f;
        Vertex = A.Vertex;
        Edge = A.Edge;
    }
    else if (name != "EMP" && A.name != "EMP")
    {
        name += A.name;
        flat = flat && A.flat;
        num_loop = num_loop + A.num_loop;
        size_loop = std::max(size_loop, A.size_loop);

        Vertex.insert(A.Vertex.begin(), A.Vertex.end());
        Edge.insert(A.Edge.begin(), A.Edge.end());
        Edge.insert(std::make_tuple("e", v_f, A.v_0));
        formula_set.push_back("(= e" + LBra + v_f + space + A.v_0 + RBra + " " + std::to_string(value_of_string_without_considering_IntStrConversion("EMP", encoding_len, is_emp_str)) + ")");
        formula_set.push_back("(= " + num_of+ "e" + LBra + v_f + space + A.v_0 + RBra + " 1)");

        //size_loop;
        //v_0 ;
        v_f = A.v_f;
    }
};


void extended_flat_automaton::concat_a_string_and_computing_Parikh_connected_formula(std::string str_var_name, std::string str_value, std::vector<std::string>& formula_set, unsigned encoding_len)
{
    bool is_emp_str = 1;

    if (name == "EMP" && !old)
    {
        name = str_var_name;
        flat = 1;
        old = 1;
        num_loop = 2;
        size_loop = 1;
        v_0 = str_var_name + "0";
        v_f = str_var_name + "1";
        Vertex.insert(v_0);
        Vertex.insert(v_f);
        Edge.insert(std::make_tuple("s", v_0, v_f));
        formula_set.push_back("(= " + num_of + "s" + LBra + v_0 + space + v_f + RBra + " 1)");
        formula_set.push_back("(= s" + LBra + v_0 + space + v_f + RBra + " " + std::to_string(value_of_string_without_considering_IntStrConversion(str_value, encoding_len, !is_emp_str)) + ")");
    }
    else if (name != "EMP")
    {
        name += str_var_name;
        num_loop = num_loop + 1;
        Vertex.insert(str_var_name);
        Edge.insert(std::make_tuple("s", v_f, str_var_name));
        formula_set.push_back("(= " + num_of + "s" + LBra + v_f + space + str_var_name + RBra + " 1)");
        formula_set.push_back("(= s" + LBra + v_f + space + str_var_name + RBra + " " + std::to_string(value_of_string_without_considering_IntStrConversion(str_value, encoding_len, !is_emp_str)) + ")");

        //size_loop;
        //v_0 ;
        v_f = str_var_name;
    }

    
};






void extended_flat_automaton::product_automata_and_computing_in_out_edges_of_states_and_inintial_state_used(extended_flat_automaton A, extended_flat_automaton B, std::vector<std::string>& formula_set,
    std::map<std::string, std::set < std::tuple <std::string, std::string, std::string>>>& state_in_edges,
    std::map<std::string, std::set < std::tuple <std::string, std::string, std::string>>>& state_out_edges, 
    unsigned encoding_len)
{
    bool is_emp_str = 1;

    name = "P" + LBra + A.name + space + B.name + RBra;


    if (A.name == "EMP" || B.name == "EMP")
    {
        if (A.name != "EMP")
        {
            flat = A.flat;
            old = A.old;
            num_loop = A.num_loop;
            size_loop = A.size_loop;
            v_0 = A.v_0;
            v_f = A.v_f;
            Vertex = A.Vertex;
            Edge = A.Edge;
        }
        else if (B.name != "EMP")
        {
            flat = B.flat;
            old = B.old;
            num_loop = B.num_loop;
            size_loop = B.size_loop;
            v_0 = B.v_0;
            v_f = B.v_f;
            Vertex = B.Vertex;
            Edge = B.Edge;
        }
        else
        {
            name = "EMP";
            extended_flat_automaton::make_empty();
            name = "P" + LBra + A.name + space + B.name + RBra;
        }
        for (std::set<std::tuple <std::string, std::string, std::string>>::iterator it = Edge.begin(); it != Edge.end(); ++it)
        {
            state_in_edges[std::get<2>(*it)].insert(*it);
            state_out_edges[std::get<1>(*it)].insert(*it);
        }
        return;
    }

    v_0 = LBra + A.v_0 + space + B.v_0 + RBra;
    v_f = LBra + A.v_f + space + B.v_f + RBra;
    flat = 0;
    old = 0;

    formula_set.push_back("(>= out" + LBra + v_0 + RBra + " 1)");

    for (std::set<std::string>::iterator A_it = A.Vertex.begin(); A_it != A.Vertex.end(); ++A_it)
    {
        for (std::set<std::string>::iterator B_it = B.Vertex.begin(); B_it != B.Vertex.end(); ++B_it)
            Vertex.insert(LBra + *A_it + space + *B_it + RBra);
    }

    
    
    bool flag_first_use = 0;
    std::string num_use_edge = "";
    std::string prod_edge_type_non_non = "nn";
    std::string prod_edge_type_emp_non = "en";
    std::string prod_edge_type_non_emp = "ne";
    
    //
    for (std::set<std::tuple <std::string, std::string, std::string>>::iterator A_it = A.Edge.begin(); A_it != A.Edge.end(); ++A_it)
    {
        flag_first_use = 0;
        num_use_edge = "";

        for (std::set<std::tuple <std::string, std::string, std::string>>::iterator B_it = B.Edge.begin(); B_it != B.Edge.end(); ++B_it)
        {
            std::tuple <std::string, std::string, std::string> temp_edge = std::make_tuple(prod_edge_type_non_non,
                LBra + std::get<1>(*A_it) + space + std::get<1>(*B_it) + RBra,
                LBra + std::get<2>(*A_it) + space + std::get<2>(*B_it) + RBra);
            Edge.insert(temp_edge);
            state_in_edges[std::get<2>(temp_edge)].insert(temp_edge);
            state_out_edges[std::get<1>(temp_edge)].insert(temp_edge);
            if (!flag_first_use)
            {
                flag_first_use = 1;
                num_use_edge += num_of + std::get<0>(temp_edge) + LBra + std::get<1>(temp_edge) + space + std::get<2>(temp_edge) + RBra;
            }
            else
                num_use_edge = "(+ " + num_use_edge + " " + num_of + std::get<0>(temp_edge) + LBra + std::get<1>(temp_edge) + space + std::get<2>(temp_edge) + RBra + ")";
            formula_set.push_back("(or (= " + 
                num_of + std::get<0>(temp_edge) + LBra + std::get<1>(temp_edge) + space + std::get<2>(temp_edge) + RBra + " 0) (= " +
                std::get<0>(*A_it) + LBra + std::get<1>(*A_it) + space + std::get<2>(*A_it) + RBra + " " + std::get<0>(*B_it) + LBra + std::get<1>(*B_it) + space + std::get<2>(*B_it) + RBra + "))");
        }
        if (std::get<0>(*A_it) != "e")
        {
            for (std::set<std::string>::iterator B_it = B.Vertex.begin(); B_it != B.Vertex.end(); ++B_it)
            {
                std::tuple <std::string, std::string, std::string> temp_edge = std::make_tuple(prod_edge_type_non_emp,
                    LBra + std::get<1>(*A_it) + space + *B_it + RBra,
                    LBra + std::get<2>(*A_it) + space + *B_it + RBra);

                Edge.insert(temp_edge);
                state_in_edges[std::get<2>(temp_edge)].insert(temp_edge);
                state_out_edges[std::get<1>(temp_edge)].insert(temp_edge);

                if (!flag_first_use)
                {
                    flag_first_use = 1;
                    num_use_edge += num_of + std::get<0>(temp_edge) + LBra + std::get<1>(temp_edge) + space + std::get<2>(temp_edge) + RBra;
                }
                else
                    num_use_edge = "(+ " + num_use_edge + " " + num_of + std::get<0>(temp_edge) + LBra + std::get<1>(temp_edge) + space + std::get<2>(temp_edge) + RBra + ")";
                if (std::get<0>(*A_it) == "s")
                    formula_set.push_back("(= " + num_of + std::get<0>(temp_edge) + LBra + std::get<1>(temp_edge) + space + std::get<2>(temp_edge) + RBra + " 0)");
                else
                    formula_set.push_back("(or (= " +
                        num_of + std::get<0>(temp_edge) + LBra + std::get<1>(temp_edge) + space + std::get<2>(temp_edge) + RBra + " 0) (= " +
                    std::get<0>(*A_it) + LBra + std::get<1>(*A_it) + space + std::get<2>(*A_it) + RBra + " " + std::to_string(value_of_string_without_considering_IntStrConversion("EMP", encoding_len, is_emp_str)) + "))");
            }
        }
        formula_set.push_back("(= " + num_of + std::get<0>(*A_it) + LBra + std::get<1>(*A_it) + space + std::get<2>(*A_it) + RBra + " " + num_use_edge + ")");
    }
    //
    for (std::set<std::tuple <std::string, std::string, std::string>>::iterator B_it = B.Edge.begin(); B_it != B.Edge.end(); ++B_it)
    {
        flag_first_use = 0;
        num_use_edge = "";

        for (std::set<std::tuple <std::string, std::string, std::string>>::iterator A_it = A.Edge.begin(); A_it != A.Edge.end(); ++A_it)
        {
            std::tuple <std::string, std::string, std::string> temp_edge = std::make_tuple(prod_edge_type_non_non,
                LBra + std::get<1>(*A_it) + space + std::get<1>(*B_it) + RBra,
                LBra + std::get<2>(*A_it) + space + std::get<2>(*B_it) + RBra);
            if (!flag_first_use)
            {
                flag_first_use = 1;
                num_use_edge += num_of + std::get<0>(temp_edge) + LBra + std::get<1>(temp_edge) + space + std::get<2>(temp_edge) + RBra;
            }
            else
                num_use_edge = "(+ " + num_use_edge + " " + num_of + std::get<0>(temp_edge) + LBra + std::get<1>(temp_edge) + space + std::get<2>(temp_edge) + RBra + ")";
        }
        if (std::get<0>(*B_it) != "e")
        {
            for (std::set<std::string>::iterator A_it = A.Vertex.begin(); A_it != A.Vertex.end(); ++A_it)
            {
                std::tuple <std::string, std::string, std::string> temp_edge = std::make_tuple(prod_edge_type_emp_non,
                    LBra + *A_it + space + std::get<1>(*B_it) + RBra,
                    LBra + *A_it + space + std::get<2>(*B_it) + RBra);

                Edge.insert(temp_edge);
                state_in_edges[std::get<2>(temp_edge)].insert(temp_edge);
                state_out_edges[std::get<1>(temp_edge)].insert(temp_edge);

                if (!flag_first_use)
                {
                    flag_first_use = 1;
                    num_use_edge += num_of + std::get<0>(temp_edge) + LBra + std::get<1>(temp_edge) + space + std::get<2>(temp_edge) + RBra;
                }
                else
                    num_use_edge = "(+ " + num_use_edge + " " + num_of + std::get<0>(temp_edge) + LBra + std::get<1>(temp_edge) + space + std::get<2>(temp_edge) + RBra + ")";
                if (std::get<0>(*B_it) == "s")
                    formula_set.push_back("(= " + num_of + std::get<0>(temp_edge) + LBra + std::get<1>(temp_edge) + space + std::get<2>(temp_edge) + RBra + " 0)");
                else
                    formula_set.push_back("(or (= " +
                        num_of + std::get<0>(temp_edge) + LBra + std::get<1>(temp_edge) + space + std::get<2>(temp_edge) + RBra + " 0) (= " +
                    std::get<0>(*B_it) + LBra + std::get<1>(*B_it) + space + std::get<2>(*B_it) + RBra + " " + std::to_string(value_of_string_without_considering_IntStrConversion("EMP", encoding_len, is_emp_str)) + "))");
            }
        }
        formula_set.push_back("(= " + num_of + std::get<0>(*B_it) + LBra + std::get<1>(*B_it) + space + std::get<2>(*B_it) + RBra + " " + num_use_edge + ")");
    }
};





////////////////////////////////////////////////////////////////////////////
// Useless for now
void extended_flat_automaton::concat(extended_flat_automaton A, extended_flat_automaton B, std::vector<std::string>& formula_set)
{
    name = A.get_name() + B.get_name();
    flat = A.is_flat() && B.is_flat();
    num_loop = A.get_num_loop() + B.get_num_loop();
    size_loop = A.get_size_loop();
    v_0 = A.v_0;
    v_f = B.v_f;

    Vertex = A.Vertex;
    Vertex.insert(B.Vertex.begin(), B.Vertex.end());
    Edge = A.Edge;
    Edge.insert(B.Edge.begin(), B.Edge.end());
    Edge.insert(std::make_tuple("e", A.v_f, B.v_0));
    formula_set.push_back("e<" + A.v_f + "_" + B.v_0 + ">=value_of(EMP)");

};

void extended_flat_automaton::hello() {
    std::cout << "\nHello!\n";
};

std::string extended_flat_automaton::get_name()
{
    return name;
};

bool extended_flat_automaton::is_flat()
{
    return flat;
};

unsigned extended_flat_automaton::get_num_loop()
{
    return num_loop;
};

unsigned extended_flat_automaton::get_size_loop()
{
    return size_loop;
};

extended_flat_automaton::extended_flat_automaton(std::string given_automaton, bool is_string)
{
    if (!is_string)
    {
        std::cout << "Error-not a string\n";
        return;
    }
    name = given_automaton;
    flat = 1; // 1-> flat
    old = 1;
    num_loop = 2;
    size_loop = 1;
    v_0 = name + "(0,0)";
    v_f = name + "(" + std::to_string(1) + "," + std::to_string(0) + ")";
    Vertex.insert(v_0);
    Vertex.insert(v_f);
    Edge.insert(std::make_tuple("S", name + "(" + std::to_string(0) + "," + std::to_string(0) + ")", name + "(" + std::to_string(1) + "," + std::to_string(0) + ")"));
};

void extended_flat_automaton::product(extended_flat_automaton A, extended_flat_automaton B, std::vector<std::string>& formula_set)
{
    flat = 0;
    name = "P(" + A.name + "," + B.name + ")";
    v_0 = "(" + A.v_0 + "," + B.v_0 + ")";
    v_f = "(" + A.v_f + "," + B.v_f + ")";
    std::string num_use_edge = "";
    bool flag_first_use = 0;

    for (std::set<std::string>::iterator A_it = A.Vertex.begin(); A_it != A.Vertex.end(); ++A_it)
    {
        for (std::set<std::string>::iterator B_it = B.Vertex.begin(); B_it != B.Vertex.end(); ++B_it)
            Vertex.insert("(" + *A_it + "," + *B_it + ")");
    }

    for (std::set<std::tuple <std::string, std::string, std::string>>::iterator A_it = A.Edge.begin(); A_it != A.Edge.end(); ++A_it)
    {
        flag_first_use = 0;
        num_use_edge = "";
        if (std::get<0>(*A_it) != "E")
        {
            for (std::set<std::tuple <std::string, std::string, std::string>>::iterator B_it = B.Edge.begin(); B_it != B.Edge.end(); ++B_it)
            {
                std::tuple <std::string, std::string, std::string> temp_edge = std::make_tuple("T",
                    "(" + std::get<1>(*A_it) + "," + std::get<1>(*B_it) + ")",
                    "(" + std::get<2>(*A_it) + "," + std::get<2>(*B_it) + ")");
                Edge.insert(temp_edge);
                if (!flag_first_use)
                    flag_first_use = 1;
                else
                    num_use_edge += "+";
                num_use_edge += "#" + std::get<0>(temp_edge) + "(" + std::get<1>(temp_edge) + "," + std::get<2>(temp_edge) + ")";
                formula_set.push_back("#" + std::get<0>(temp_edge) + "(" + std::get<1>(temp_edge) + "," + std::get<2>(temp_edge) + ")=0 or " +
                    std::get<0>(*A_it) + "(" + std::get<1>(*A_it) + "," + std::get<2>(*A_it) + ")=" + std::get<0>(*B_it) + "(" + std::get<1>(*B_it) + "," + std::get<2>(*B_it) + ")");
            }
            if (B.size_loop > 1)
            {
                for (std::set<std::string>::iterator B_it = B.Vertex.begin(); B_it != B.Vertex.end(); ++B_it)
                {
                    std::tuple <std::string, std::string, std::string> temp_edge = std::make_tuple("E",
                        "(" + std::get<1>(*A_it) + "," + *B_it + ")",
                        "(" + std::get<2>(*A_it) + "," + *B_it + ")");
                    Edge.insert(temp_edge);
                    if (!flag_first_use)
                        flag_first_use = 1;
                    else
                        num_use_edge += "+";
                    num_use_edge += "#" + std::get<0>(temp_edge) + "(" + std::get<1>(temp_edge) + "," + std::get<2>(temp_edge) + ")";
                    formula_set.push_back("#" + std::get<0>(temp_edge) + "(" + std::get<1>(temp_edge) + "," + std::get<2>(temp_edge) + ")=0 or " +
                        std::get<0>(*A_it) + "(" + std::get<1>(*A_it) + "," + std::get<2>(*A_it) + ")=value_of(EMP)");
                }
            }
            formula_set.push_back("#" + std::get<0>(*A_it) + "(" + std::get<1>(*A_it) + "," + std::get<2>(*A_it) + ")=" + num_use_edge);
        }
    }
    for (std::set<std::tuple <std::string, std::string, std::string>>::iterator B_it = B.Edge.begin(); B_it != B.Edge.end(); ++B_it)
    {
        flag_first_use = 0;
        num_use_edge = "";
        if (std::get<0>(*B_it) != "E")
        {
            for (std::set<std::tuple <std::string, std::string, std::string>>::iterator A_it = A.Edge.begin(); A_it != A.Edge.end(); ++A_it)
            {
                std::tuple <std::string, std::string, std::string> temp_edge = std::make_tuple("T",
                    "(" + std::get<1>(*A_it) + "," + std::get<1>(*B_it) + ")",
                    "(" + std::get<2>(*A_it) + "," + std::get<2>(*B_it) + ")");
                Edge.insert(temp_edge);
                if (!flag_first_use)
                    flag_first_use = 1;
                else
                    num_use_edge += "+";
                num_use_edge += "#" + std::get<0>(temp_edge) + "(" + std::get<1>(temp_edge) + "," + std::get<2>(temp_edge) + ")";
                formula_set.push_back("#" + std::get<0>(temp_edge) + "(" + std::get<1>(temp_edge) + "," + std::get<2>(temp_edge) + ")=0 or " +
                    std::get<0>(*A_it) + "(" + std::get<1>(*A_it) + "," + std::get<2>(*A_it) + ")=" + std::get<0>(*B_it) + "(" + std::get<1>(*B_it) + "," + std::get<2>(*B_it) + ")");
            }
            if (A.size_loop > 1)
            {
                for (std::set<std::string>::iterator A_it = A.Vertex.begin(); A_it != A.Vertex.end(); ++A_it)
                {
                    std::tuple <std::string, std::string, std::string> temp_edge = std::make_tuple("E",
                        "(" + *A_it + "," + std::get<1>(*B_it) + ")",
                        "(" + *A_it + "," + std::get<2>(*B_it) + ")");
                    Edge.insert(temp_edge);
                    if (!flag_first_use)
                        flag_first_use = 1;
                    else
                        num_use_edge += "+";
                    num_use_edge += "#" + std::get<0>(temp_edge) + "(" + std::get<1>(temp_edge) + "," + std::get<2>(temp_edge) + ")";
                    formula_set.push_back("#" + std::get<0>(temp_edge) + "(" + std::get<1>(temp_edge) + "," + std::get<2>(temp_edge) + ")=0 or " +
                        std::get<0>(*B_it) + "(" + std::get<1>(*B_it) + "," + std::get<2>(*B_it) + ")=value_of(EMP)");
                }
            }
            formula_set.push_back("#" + std::get<0>(*B_it) + "(" + std::get<1>(*B_it) + "," + std::get<2>(*B_it) + ")=" + num_use_edge);
        }
    }
};

void extended_flat_automaton::concat(extended_flat_automaton A, std::vector<std::string>& formula_set)
{
    if (name == "EMP" && !old)
    {
        name = A.name;
        flat = A.flat;
        old = A.old;
        num_loop = A.num_loop;
        size_loop = A.size_loop;
        v_0 = A.v_0;
        v_f = A.v_f;
        Vertex = A.Vertex;
        Edge = A.Edge;
    }
    else if (name != "EMP" && A.name != "EMP")
    {
        name += A.name;
        flat = flat && A.flat;
        num_loop = num_loop + A.num_loop;
        size_loop = std::max(size_loop, A.size_loop);

        Vertex.insert(A.Vertex.begin(), A.Vertex.end());
        Edge.insert(A.Edge.begin(), A.Edge.end());
        Edge.insert(std::make_tuple("e", v_f, A.v_0));
        formula_set.push_back("e<" + v_f + "_" + A.v_0 + ">=value_of(EMP)");

        //size_loop;
        //v_0 ;
        v_f = A.v_f;
    }
};

void extended_flat_automaton::concat_a_string(std::string str, std::vector<std::string>& formula_set)
{



    if (name == "EMP" && !old)
    {
        name = str;
        flat = 1;
        old = 1;
        num_loop = 2;
        size_loop = 1;
        v_0 = str + "0";
        v_f = str + "1";
        Vertex.insert(v_0);
        Vertex.insert(v_f);
        Edge.insert(std::make_tuple("s", v_0, v_f));
    }
    else if (name != "EMP")
    {
        name += str;
        num_loop = num_loop + 1;
        Vertex.insert(str);
        Edge.insert(std::make_tuple("s", v_f, str));

        //size_loop;
        //v_0 ;
        v_f = str;
    }


};

extended_flat_automaton::extended_flat_automaton(std::string given_automaton, bool is_flat, unsigned set_num_loop, unsigned set_size_loop)
{
    std::transform(given_automaton.begin(), given_automaton.end(), given_automaton.begin(), [](unsigned char c) { return std::tolower(c); });
    name = given_automaton;
    flat = is_flat; // 1-> flat
    old = 1;
    num_loop = set_num_loop;
    size_loop = set_size_loop;
    if (num_loop < 1)
    {
        std::cout << "Error: num_loop < 1\n";
        return;
    }
    if (size_loop == 1)
    {
        v_0 = name + "0";
        v_f = name + std::to_string(num_loop - 1);

        for (unsigned i = 0; i < num_loop - 1; i++)
        {
            Vertex.insert(name + std::to_string(i));
            Edge.insert(std::make_tuple("t", name + std::to_string(i), name + std::to_string(i)));
            Edge.insert(std::make_tuple("t", name + std::to_string(i), name + std::to_string(i + 1)));
        }
        if (num_loop == 1)
        {
            Vertex.insert(name + std::to_string(0));
            Edge.insert(std::make_tuple("t", name + std::to_string(0), name + std::to_string(0)));
        }
        else
        {
            Vertex.insert(name + std::to_string(num_loop - 1));
            Edge.insert(std::make_tuple("t", name + std::to_string(num_loop - 1), name + std::to_string(num_loop - 1)));
        }
    }
    else if (size_loop == 0)
    {
        v_0 = name + "0";
        v_f = name + std::to_string(num_loop - 1);

        for (unsigned i = 0; i < num_loop - 1; i++)
        {
            Vertex.insert(name + std::to_string(i));
            Edge.insert(std::make_tuple("t", name + std::to_string(i), name + std::to_string(i + 1)));
        }
        if (num_loop == 1)
            Vertex.insert(name + std::to_string(0));
        else
            Vertex.insert(name + std::to_string(num_loop - 1));
    }
    else if (size_loop > 1)
    {
        v_0 = name + "<0,0>";
        v_f = name + "<" + std::to_string(num_loop - 1) + "," + std::to_string(0) + ">";

        for (unsigned i = 0; i < num_loop; i++)
        {
            for (unsigned j = 0; j < size_loop; j++)
            {
                Vertex.insert(name + "<" + std::to_string(i) + "," + std::to_string(j) + ">");
                if (j + 1 != size_loop)
                    Edge.insert(std::make_tuple("t", name + "<" + std::to_string(i) + "," + std::to_string(j) + ">", name + "<" + std::to_string(i) + "," + std::to_string(j + 1) + ">"));
                else
                    Edge.insert(std::make_tuple("t", name + "<" + std::to_string(i) + "," + std::to_string(j) + ">", name + "<" + std::to_string(i) + "," + std::to_string(0) + ">"));
            }
            if (i + 1 != num_loop)
                Edge.insert(std::make_tuple("t", name + "<" + std::to_string(i) + "," + std::to_string(0) + ">", name + "<" + std::to_string(i + 1) + "," + std::to_string(0) + ">"));
            if (num_loop == 1)
                Vertex.insert(name + "<" + std::to_string(i) + "," + std::to_string(0) + ">");
        }
    }
};

