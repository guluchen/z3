#include "smt/theory_str.h"
#include "util/debug.h"



static void oaut_tst(){
    using namespace smt::str;
    const float One = 0;
    fst::StdVectorFst f;
    f.AddState();   // 1st state will be state 0 (returned by AddState)
    f.AddState();
    f.AddState();
    f.AddState();
    f.AddState();
    f.SetStart(0);
    f.AddArc(0, fst::StdArc('a', 'a', One, 1));
    f.AddArc(0, fst::StdArc('b', 'b', One, 2));
    f.AddArc(1, fst::StdArc('b', 'b', One, 3));
    f.AddArc(2, fst::StdArc('a', 'a', One, 4));
    f.AddArc(3, fst::StdArc('a', 'a', One, 1));
    f.AddArc(4, fst::StdArc('b', 'b', One, 2));
    f.SetFinal(3, One);
    f.SetFinal(4, One);

    std::shared_ptr<oaut> result = std::make_shared<smt::str::oaut>(f);

    fst::StdVectorFst g;
    g.AddState();
    g.AddState();
    g.AddState();
    g.AddState();
    g.AddState();
    g.AddState();
    g.AddState();
    g.SetStart(0);
    g.AddArc(0, fst::StdArc('a', 'a', One, 1));
    g.AddArc(0, fst::StdArc('b', 'b', One, 2));
    g.AddArc(1, fst::StdArc('b', 'b', One, 3));
    g.AddArc(2, fst::StdArc('a', 'a', One, 4));
    g.AddArc(3, fst::StdArc('a', 'a', One, 5));
    g.AddArc(4, fst::StdArc('b', 'b', One, 6));
    g.AddArc(5, fst::StdArc('b', 'b', One, 3));
    g.AddArc(6, fst::StdArc('a', 'a', One, 4));

    g.SetFinal(3, One);
    g.SetFinal(4, One);


    std::shared_ptr<oaut> result2 = std::make_shared<smt::str::oaut>(g);

    bool equivalent_test_result=(*result == *result2);
    std::cout<<"Equalivalent function test: "<<equivalent_test_result<<std::endl;
    ENSURE(equivalent_test_result);

    g.AddArc(1, fst::StdArc('c', 'c', One, 3));
    result2 = std::make_shared<smt::str::oaut>(g);

    bool equivalent_test_result2=(*result != *result2);
    std::cout<<"Equalivalent function test2: "<<equivalent_test_result2<<std::endl;
    ENSURE(equivalent_test_result2);

    bool is_deterministic_test_result=(result->is_deterministic());
    std::cout<<"Is_deterministic function test: "<<is_deterministic_test_result<<std::endl;
    ENSURE(is_deterministic_test_result);

    g.AddArc(1, fst::StdArc('c', 'c', One, 2));
    result2 = std::make_shared<smt::str::oaut>(g);
    bool is_deterministic_test_result2=(!result2->is_deterministic());
    std::cout<<"Is_deterministic function test: "<<is_deterministic_test_result2<<std::endl;
    ENSURE(is_deterministic_test_result2);

    std::shared_ptr<smt::str::automaton> result3=result2->determinize();
    bool clone_and_determinize_test_result = (*result3 == *result2);
    std::cout<<"Clone and determinize functions test: "<<clone_and_determinize_test_result<<std::endl;
    ENSURE(clone_and_determinize_test_result);

    std::shared_ptr<smt::str::automaton> result4 = result3->complement();
    std::shared_ptr<smt::str::automaton> result5 = result4->intersect_with(result3);
    bool complement_intersection_and_is_empty_test_result=result5->is_empty();
    std::cout<<"Complement, intersection, and is_empty functions test: "<<complement_intersection_and_is_empty_test_result<<std::endl;
    ENSURE(complement_intersection_and_is_empty_test_result);

    std::shared_ptr<smt::str::automaton> result6 = result4->union_with(result3);
    std::shared_ptr<smt::str::automaton> result7 = result6->complement();
    bool complement_union_and_is_empty_test_result=result7->is_empty();
    std::cout<<"Complement, union, and is_empty functions test: "<<complement_union_and_is_empty_test_result<<std::endl;
    ENSURE(complement_union_and_is_empty_test_result);

    std::set<smt::str::automaton::state> reachable = (result2->reachable_states(result2->get_init()));
    std::set<smt::str::automaton::state> onestep_reachable = (result2->successors(result2->get_init()));
    std::set<smt::str::automaton::state> onestep_a_reachable = (result2->successors(result2->get_init(), "a"));
    std::set<smt::str::automaton::state> out;
    std::set<smt::str::automaton::state> out2;
    std::set_difference(onestep_reachable.begin(), onestep_reachable.end(),
                        reachable.begin(), reachable.end(),
                        std::inserter(out, out.begin()));
    std::set_difference(reachable.begin(), reachable.end(),
                        onestep_reachable.begin(), onestep_reachable.end(),
                        std::inserter(out2, out2.begin()));
    bool reachable_states_and_successors_test_result1= ((out.empty()) && (!out2.empty()));
    std::cout<<"Reachable_states and successors functions test1: "<<reachable_states_and_successors_test_result1<<std::endl;
    ENSURE(reachable_states_and_successors_test_result1);

    std::set_difference(onestep_a_reachable.begin(), onestep_a_reachable.end(),
                        onestep_reachable.begin(), onestep_reachable.end(),
                        std::inserter(out, out.begin()));
    std::set_difference(onestep_reachable.begin(), onestep_reachable.end(),
                        onestep_a_reachable.begin(), onestep_a_reachable.end(),
                        std::inserter(out2, out2.begin()));
    bool reachable_states_and_successors_test_result2= ((out.empty()) && (!out2.empty()));
    std::cout<<"Reachable_states and successors functions test2: "<<reachable_states_and_successors_test_result2<<std::endl;
    ENSURE(reachable_states_and_successors_test_result2);

    bool split_test_result=(result2->split().size()==result2->reachable_states(result2->get_init()).size());
    std::cout<<"Split function test: "<<split_test_result<<std::endl;
    ENSURE(split_test_result);

    bool remove_prefix_test_result=(result2->remove_prefix("ab").size()==1);
    std::cout<<"Remove_prefix function test: "<<remove_prefix_test_result<<std::endl;
    ENSURE(remove_prefix_test_result);


}

void tst_theory_string() {
    oaut_tst();
}
