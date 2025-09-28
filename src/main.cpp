#include <iostream>
#include "utility/proof/proof.hpp"
#include "utility/proof_system/proof_system.hpp"
#include "utility/text_utils/text_utils.hpp"

int main() {
    // test();
    std::cout << "Hello, World!" << std::endl;

    TermPtr natural_numbers = Term::make_constant("ℕ");
    // ---------------------------
    // Example 1: AND proof
    // ---------------------------
    {
        std::cout << "=== AND Proof ===\n";

        // Assumptions: x = 2, y = 3
        TermPtr x = Term::make_variable("x");
        TermPtr y = Term::make_variable("y");
        TermPtr two = Term::make_constant("2");
        TermPtr three = Term::make_constant("3");

        FormulaPtr x_eq_2 = Formula::make_eq(x, two);
        FormulaPtr y_eq_3 = Formula::make_eq(y, three);

        // Target: (x = 2 OR y = 3)  (using OR as a placeholder for AND rule)
        FormulaPtr target = Formula::make_and(x_eq_2, y_eq_3);

        Proof proof({x_eq_2, y_eq_3}, target);

        proof.add_line_to_proof(x_eq_2, "ASSUMPTION");
        proof.add_line_to_proof(y_eq_3, "ASSUMPTION");
        proof.add_line_to_proof(target, "AND", {0, 1});

        proof.print();

        if (proof.is_valid()) {
            std::cout << "Proof is valid for target: " << target->to_string() << "\n";
        } else {
            std::cout << "Proof is NOT valid.\n";
        }
        std::cout << "\n";
    }

    // ---------------------------
    // Example 2: FORALL proof
    // ---------------------------
    {
        std::cout << "=== FORALL Proof ===\n";

        TermPtr y = Term::make_variable("y");
        TermPtr x = Term::make_variable("x");
        TermPtr five = Term::make_constant("5");
        TermPtr X = Term::make_constant("X");

        // y in X
        FormulaPtr y_in_X = Formula::make_rel("∈", {y, X});

        // forall x in X, x = 5   (represented as ForallFormula)
        FormulaPtr x_eq_5 = Formula::make_eq(x, five);
        FormulaPtr forall_x_eq_5 = Formula::make_forall("x", X, x_eq_5);

        // Target: y = 5
        FormulaPtr y_eq_5 = Formula::make_eq(y, five);

        Proof proof({y_in_X, forall_x_eq_5}, y_eq_5);

        proof.add_line_to_proof(y_in_X, "ASSUMPTION");
        proof.add_line_to_proof(forall_x_eq_5, "ASSUMPTION");
        proof.add_line_to_proof(y_eq_5, "FORALL", {1, 0});

        proof.print();

        if (proof.is_valid()) {
            std::cout << "Proof is valid for target: " << y_eq_5->to_string() << "\n";
        } else {
            std::cout << "Proof is NOT valid.\n";
        }
        std::cout << "\n";
    }

    // ---------------------------
    // Example 3: Induction proof of sum(n) = n
    // ---------------------------
    {
        std::cout << "=== Induction Proof: sum(n) = n ===\n";

        // Terms
        TermPtr n = Term::make_variable("n");
        TermPtr k = Term::make_variable("k");
        TermPtr zero = Term::make_constant("0");
        TermPtr one = Term::make_constant("1");

        // sum(…) as a function symbol
        auto sum_fn = [](TermPtr t) { return Term::make_function("sum", {t}); };

        // Base axiom: sum(0) = 0
        FormulaPtr sum_axiom_base = Formula::make_eq(sum_fn(zero), zero);

        // Recursive axiom: forall k, sum(k+1) = sum(k) + 1
        TermPtr k_plus_1 = Term::make_function("+", {k, one});
        TermPtr sum_k_plus_1 = sum_fn(k_plus_1);
        TermPtr sum_k_plus_1_def = Term::make_function("+", {sum_fn(k), one});
        FormulaPtr recursive_axiom_inner = Formula::make_eq(sum_k_plus_1, sum_k_plus_1_def);
        FormulaPtr sum_axiom_recursive = Formula::make_forall("k", natural_numbers, recursive_axiom_inner);

        // Induction step: forall k, sum(k) = k -> sum(k+1) = k+1
        FormulaPtr sum_k_eq_k = Formula::make_eq(sum_fn(k), k);
        FormulaPtr sum_k1_eq_k1 = Formula::make_eq(sum_fn(k_plus_1), k_plus_1);
        FormulaPtr step_inner = Formula::make_implies(sum_k_eq_k, sum_k1_eq_k1);
        FormulaPtr step = Formula::make_forall("k", natural_numbers, step_inner);

        // Target: forall n, sum(n) = n
        FormulaPtr target = Formula::make_forall("n", natural_numbers, Formula::make_eq(sum_fn(n), n));

        // Now the proof assumptions include the definition of sum
        Proof proof({sum_axiom_base, sum_axiom_recursive, step}, target);
        proof.register_rule("INDUCTION", induction_rule);

        // 0. Base case (can be derived from sum_axiom_base)
        proof.add_line_to_proof(sum_axiom_base, "ASSUMPTION");

        // 1. Recursive axiom
        proof.add_line_to_proof(sum_axiom_recursive, "ASSUMPTION");

        // 2. Step assumption
        proof.add_line_to_proof(step, "ASSUMPTION");

        // 3. Apply induction
        proof.add_line_to_proof(target, "INDUCTION", {0, 2});

        proof.print();

        if (proof.is_valid()) {
            std::cout << "Proof is valid for target: " << target->to_string() << "\n";
        } else {
            std::cout << "Proof is NOT valid.\n";
        }
        std::cout << "\n";
    }

    // ---------------------------
    // Example 4: Excluded Middle proof
    // ---------------------------
    {
        std::cout << "=== Excluded Middle Proof ===\n";

        // Term: x
        TermPtr x = Term::make_variable("x");

        // Formula: P(x)
        FormulaPtr Px = Formula::make_rel("P", {x});

        // Formula: not P(x)
        FormulaPtr not_Px = Formula::make_not(Px);

        // Target: P(x) or not P(x)
        FormulaPtr target = Formula::make_or(Px, not_Px);

        // No assumptions needed for LEM
        Proof proof({}, target);
        proof.register_rule("LEM", excluded_middle_rule);

        // 0. Apply LEM directly
        proof.add_line_to_proof(target, "LEM");

        proof.print();

        if (proof.is_valid()) {
            std::cout << "Proof is valid for target: " << target->to_string() << "\n";
        } else {
            std::cout << "Proof is NOT valid.\n";
        }
        std::cout << "\n";
    }
    {
        // Terms
        TermPtr x = Term::make_variable("x");

        // Formulas
        FormulaPtr Px = Formula::make_rel("P", {x});
        FormulaPtr not_Px = Formula::make_not(Px);
        FormulaPtr Qx = Formula::make_rel("Q", {x});

        // Implications
        FormulaPtr imp1 = Formula::make_implies(Px, Qx);
        FormulaPtr imp2 = Formula::make_implies(not_Px, Qx);

        // Target
        FormulaPtr target = Qx;

        // Proof proof({imp1, imp2}, target);
        Proof proof({imp1, imp2}, target);
        proof.register_rule("CASES", cases_rule);

        // 0. Assume f -> t
        proof.add_line_to_proof(imp1, "ASSUMPTION");

        // 1. Assume ¬f -> t
        proof.add_line_to_proof(imp2, "ASSUMPTION");

        // 2. Apply cases
        proof.add_line_to_proof(target, "CASES", {0, 1});

        proof.print();

        if (proof.is_valid()) {
            std::cout << "Proof is valid for target: " << target->to_string() << "\n";
        }
    }
    {
        std::cout << "=== Induction Proof (modification rules): sum(n) = n ===\n";

        // Terms
        TermPtr n = Term::make_variable("n");
        TermPtr k = Term::make_variable("k");
        TermPtr zero = Term::make_constant("0");
        TermPtr one = Term::make_constant("1");

        auto sum_fn = [](TermPtr t) { return Term::make_function("sum", {t}); };

        // base axiom: sum(0) = 0
        FormulaPtr sum_axiom_base = Formula::make_eq(sum_fn(zero), zero);

        // recursive axiom: forall k, sum(k+1) = sum(k) + 1
        TermPtr k_plus_1 = Term::make_function("+", {k, one});
        TermPtr sum_k_plus_1 = sum_fn(k_plus_1);
        TermPtr sum_k_plus_1_def = Term::make_function("+", {sum_fn(k), one});
        FormulaPtr recursive_axiom_inner = Formula::make_eq(sum_k_plus_1, sum_k_plus_1_def);
        FormulaPtr sum_axiom_recursive = Formula::make_forall("k", natural_numbers, recursive_axiom_inner);

        // step: forall k, sum(k) = k -> sum(k+1) = k+1
        FormulaPtr sum_k_eq_k = Formula::make_eq(sum_fn(k), k);
        FormulaPtr sum_k1_eq_k1 = Formula::make_eq(sum_fn(k_plus_1), k_plus_1);
        FormulaPtr step_inner = Formula::make_implies(sum_k_eq_k, sum_k1_eq_k1);
        FormulaPtr step = Formula::make_forall("k", natural_numbers, step_inner);

        // target: forall n, sum(n) = n
        FormulaPtr target = Formula::make_forall("n", natural_numbers, Formula::make_eq(sum_fn(n), n));

        Proof proof({sum_axiom_base, sum_axiom_recursive}, target);

        proof.instantiate_induction();
        proof.add_line_to_proof(sum_axiom_base, "ASSUMPTION");
        proof.add_line_to_proof(sum_axiom_recursive, "ASSUMPTION");
        proof.instantiate_forall();

        proof.add_line_to_proof(Formula::make_rel(text_utils::element_of, {k, natural_numbers}), "ASSUMPTION");

        proof.instantiate_implication(); // assumes sum(k) = k, goal becomes sum(k+1) = k+1

        proof.add_line_to_proof(recursive_axiom_inner, "FORALL", {1, 2});

        proof.rewrite_target_using_equality(3);
        proof.add_line_to_proof(Formula::make_eq(sum_fn(k), k), "ASSUMPTION");

        proof.rewrite_target_using_equality(4);

        auto k_plus_one = Term::make_function(text_utils::plus, {k, one});

        proof.add_line_to_proof(Formula::make_eq(k_plus_one, k_plus_one), "EQ");

        if (proof.is_valid()) {
            std::cout << "Proof is valid for target: " << target->to_string() << "\n";
        } else {
            std::cout << "Proof is NOT valid.\n";
        }
        std::cout << "\n";
    }
    {
        std::cout << "=== Variable Reassignment (Swap) Proof ===\n";

        // Terms
        TermPtr x = Term::make_constant("x");
        TermPtr y = Term::make_constant("y");
        TermPtr temp = Term::make_constant("temp");
        TermPtr zero = Term::make_constant("0");
        TermPtr one = Term::make_constant("1");
        TermPtr two = Term::make_constant("2");
        TermPtr three = Term::make_constant("3");

        TermPtr va_x_0 = Term::make_function("va", {x, zero});
        TermPtr va_x_1 = Term::make_function("va", {x, one});
        TermPtr va_x_2 = Term::make_function("va", {x, two});
        TermPtr va_x_3 = Term::make_function("va", {x, three});

        TermPtr va_y_0 = Term::make_function("va", {y, zero});
        TermPtr va_y_1 = Term::make_function("va", {y, one});
        TermPtr va_y_2 = Term::make_function("va", {y, two});
        TermPtr va_y_3 = Term::make_function("va", {y, three});

        TermPtr va_temp_1 = Term::make_function("va", {temp, one});
        TermPtr va_temp_2 = Term::make_function("va", {temp, two});
        TermPtr va_temp_3 = Term::make_function("va", {temp, three});

        std::vector<TermPtr> vas = {
            va_x_0, va_x_1, va_x_2, va_x_3, va_y_0, va_y_1, va_y_2, va_y_3, va_temp_1, va_temp_2, va_temp_3,
        };

        // Assumptions
        FormulaPtr va_x_0_eq_va_x_1 = Formula::make_eq(va_x_0, va_x_1);
        FormulaPtr va_x_2_eq_va_x_3 = Formula::make_eq(va_x_2, va_x_3);

        FormulaPtr va_y_0_eq_va_y_1 = Formula::make_eq(va_y_0, va_y_1);
        FormulaPtr va_y_1_eq_va_y_2 = Formula::make_eq(va_y_1, va_y_2);

        FormulaPtr va_temp_1_eq_va_temp_2 = Formula::make_eq(va_temp_1, va_temp_2);
        FormulaPtr va_temp_2_eq_va_temp_3 = Formula::make_eq(va_temp_2, va_temp_3);

        FormulaPtr va_temp_1_eq_va_x_1 = Formula::make_eq(va_temp_1, va_x_1);
        FormulaPtr va_x_2_eq_va_y_2 = Formula::make_eq(va_x_2, va_y_2);
        FormulaPtr va_y_3_eq_va_temp_3 = Formula::make_eq(va_y_3, va_temp_3);

        // element of natural assumptiosn (bad)
        auto make_el_of_nat = [&](TermPtr el) {
            return Formula::make_rel(text_utils::element_of, {el, natural_numbers});
        };

        std::vector<FormulaPtr> my_chidern;
        for (const auto &va : vas) {
            my_chidern.push_back(make_el_of_nat(va));
        }

        // transitivity
        TermPtr a = Term::make_variable("a");
        TermPtr b = Term::make_variable("b");
        TermPtr c = Term::make_variable("c");

        FormulaPtr a_eq_b = Formula::make_eq(a, b);
        FormulaPtr b_eq_c = Formula::make_eq(b, c);
        FormulaPtr a_eq_c = Formula::make_eq(a, c);
        FormulaPtr a_eq_b_and_b_eq_c = Formula::make_and(a_eq_b, b_eq_c);
        FormulaPtr a_eq_b_and_b_eq_c_implies_a_eq_c = Formula::make_implies(a_eq_b_and_b_eq_c, a_eq_c);

        FormulaPtr forall_c = Formula::make_forall("c", natural_numbers, a_eq_b_and_b_eq_c_implies_a_eq_c);
        FormulaPtr forall_b = Formula::make_forall("b", natural_numbers, forall_c);
        FormulaPtr forall_a = Formula::make_forall("a", natural_numbers, forall_b);
        FormulaPtr transitivity = forall_a;

        // Target: va_x_3 = va_y_0 and va_y_3 = va_x_0
        FormulaPtr va_x_3_eq_va_y_0 = Formula::make_eq(va_x_3, va_y_0);
        FormulaPtr va_x_0_eq_va_y_3 = Formula::make_eq(va_y_3, va_x_0);
        FormulaPtr swapped = Formula::make_and(va_x_3_eq_va_y_0, va_x_0_eq_va_y_3);

        std::vector<FormulaPtr> assumptions = {
            va_x_0_eq_va_x_1,       va_x_2_eq_va_x_3,    va_y_0_eq_va_y_1, va_y_1_eq_va_y_2,    va_temp_1_eq_va_temp_2,
            va_temp_2_eq_va_temp_3, va_temp_1_eq_va_x_1, va_x_2_eq_va_y_2, va_y_3_eq_va_temp_3, transitivity};

        for (const auto &chidern : my_chidern) {
            assumptions.push_back(chidern);
        }

        Proof proof(assumptions, swapped);

        for (const FormulaPtr &assumption : assumptions) {
            proof.add_line_to_proof(assumption, "ASSUMPTION");
        }

        // a replaced by va_x_3
        // forall b, forall c, (...)
        auto son = substitute_term_in_formula(forall_b, a, va_x_3);
        proof.add_line_to_proof(son, "FORALL", {9, 13});

        proof.print();

        // a replaced by va_x_2
        // forall c, (...)
        auto my_god = std::get_if<ForallFormula>(&son->data)->inner;
        auto my_b = substitute_term_in_formula(my_god, b, va_x_2);
        proof.add_line_to_proof(my_b, "FORALL", {21, 12});

        auto hello_world = std::get_if<ForallFormula>(&my_b->data)->inner;
        auto my_hello = substitute_term_in_formula(hello_world, c, va_y_2);
        proof.add_line_to_proof(my_hello, "FORALL", {22, 16});

        proof.print();

        // proof.add_line_to_proof(y_in_X, );
        // proof.add_line_to_proof(y_eq_5, "FORALL", {1, 0});
        //
        // proof.print();

        // if (proof.is_valid()) {
        //     std::cout << "Proof is valid for target: " << y_eq_5->to_string() << "\n";
        // } else {
        //     std::cout << "Proof is NOT valid.\n";
        // }
        std::cout << "\n";
    }

    return 0;
}
