#include "proof.hpp"
#include <iostream>
#include <sstream>

Proof::Proof(std::vector<FormulaPtr> assumptions, FormulaPtr target) : assumptions(std::move(assumptions)) {
    targets.push_back(std::move(target));

    register_rule("ASSUMPTION", [this](const std::vector<FormulaPtr> &, FormulaPtr claimed) {
        for (auto &a : this->assumptions) {
            if (a->to_string() == claimed->to_string()) {
                return claimed;
            }
        }
        throw std::invalid_argument("Invalid assumption: " + claimed->to_string());
    });

    register_rule("FORALL", forall_rule);
    register_rule("EQ", eq_rule);
    register_rule("AND", and_rule);
}

void Proof::register_rule(const std::string &name, LineRule rule) { rules[name] = rule; }

void Proof::add_line_to_proof(FormulaPtr claimed, const std::string &rule_name, const std::vector<int> &deps) {
    // Check the rule exists
    if (!rules.count(rule_name)) {
        throw std::invalid_argument("Unknown rule: " + rule_name);
    }

    // Gather dependency statements
    std::vector<FormulaPtr> dep_statements;
    for (int idx : deps) {
        if (idx < 0 || idx >= (int)lines.size()) {
            throw std::invalid_argument("Invalid dependency index");
        }
        dep_statements.push_back(lines[idx].statement);
    }

    // Apply the rule to derive the formula
    FormulaPtr derived = rules[rule_name](dep_statements, claimed);

    // Check claimed formula matches derived
    if (derived->to_string() != claimed->to_string()) {
        throw std::invalid_argument("Claimed statement " + claimed->to_string() + " does not match derived " +
                                    derived->to_string());
    }

    // Add the line to the proof
    lines.push_back({claimed, rule_name, deps});

    // --- Check if this line completes any targets ---
    for (size_t i = 0; i < targets.size(); ++i) {
        if (targets[i]->to_string() == claimed->to_string()) {
            // Remove the completed target
            targets.erase(targets.begin() + i);

            // Adjust active_goal if necessary
            if (active_target_idx >= i && active_target_idx > 0) {
                --active_target_idx;
            }
            break; // Assuming one target per line
        }
    }
}

void Proof::instantiate_forall(std::optional<TermPtr> requested_variable) {
    // Ensure there is an active goal
    if (targets.empty())
        throw std::invalid_argument("No active goals to instantiate");

    FormulaPtr current_goal = targets[active_target_idx];
    auto forall_ptr = std::get_if<ForallFormula>(&current_goal->data);
    if (!forall_ptr) {
        throw std::invalid_argument("instantiate_forall: active goal is not a forall formula");
    }

    // Determine which variable to instantiate
    TermPtr arbitrary_variable =
        requested_variable.has_value() ? requested_variable.value() : Term::make_variable(forall_ptr->v);

    // Add assumption that variable belongs to ℕ
    TermPtr N = Term::make_constant("ℕ");
    FormulaPtr membership_assumption = Formula::make_rel("∈", {arbitrary_variable, N});
    assumptions.push_back(membership_assumption);

    // Substitute var → chosen variable in the forall body
    TermPtr bound_var = Term::make_variable(forall_ptr->v);
    FormulaPtr new_goal = substitute_in_formula(forall_ptr->inner, bound_var, arbitrary_variable);

    // Push old targets to history
    target_history.push_back(targets);

    // Update active goal with instantiated formula
    targets[active_target_idx] = new_goal;
}

void Proof::instantiate_implication() {
    // Ensure there is an active goal
    if (targets.empty())
        throw std::invalid_argument("No active goals to instantiate");

    FormulaPtr current_goal = targets[active_target_idx];
    auto impl_ptr = std::get_if<ImpliesFormula>(&current_goal->data);
    if (!impl_ptr) {
        throw std::invalid_argument("instantiate_implication: active goal is not an implication formula");
    }

    // Add the antecedent A to assumptions
    assumptions.push_back(impl_ptr->l);

    // Save old targets to history for backtracking
    target_history.push_back(targets);

    // Update active goal to the consequent B
    targets[active_target_idx] = impl_ptr->r;
}

void Proof::instantiate_induction() {
    // Grab the current active goal
    FormulaPtr current_goal = get_active_target();
    auto forall = std::get_if<ForallFormula>(&current_goal->data);
    if (!forall) {
        throw std::invalid_argument("instantiate_induction: active goal is not a forall formula");
    }

    std::string var = forall->v;
    FormulaPtr Pn = forall->inner;

    // -----------------------------
    // Base case: P(0)
    // -----------------------------
    TermPtr zero_term = Term::make_constant("0");
    TermPtr var_term = Term::make_variable(var);
    FormulaPtr P0 = substitute_in_formula(Pn, var_term, zero_term);

    // -----------------------------
    // Step case: ∀k (P(k) → P(k+1))
    // -----------------------------
    TermPtr k_term = Term::make_variable("k");
    TermPtr succ_term = Term::make_function("+", {k_term, Term::make_constant("1")});
    FormulaPtr Pk = substitute_in_formula(Pn, var_term, k_term);
    FormulaPtr Psucc = substitute_in_formula(Pn, var_term, succ_term);
    FormulaPtr step_impl = Formula::make_implies(Pk, Psucc);

    TermPtr natural_numbers = Term::make_constant("ℕ");
    FormulaPtr step_forall = Formula::make_forall("k", natural_numbers, step_impl);

    // -----------------------------
    // Update goal history and replace active goal
    // -----------------------------
    target_history.push_back(targets);

    // Replace current active goal with base case
    targets[active_target_idx] = P0;

    // Add the step case as a new goal
    targets.push_back(step_forall);

    // Keep focus on base case (active_goal unchanged)
}

void Proof::rewrite_target_using_equality(int equality_proof_line) {
    // Ensure there is an active goal
    if (targets.empty())
        throw std::invalid_argument("No active goals to rewrite");

    if (equality_proof_line < 0 || equality_proof_line >= (int)lines.size())
        throw std::invalid_argument("Invalid equality line index");

    // Get the equality formula from the proof line
    FormulaPtr equality_formula = lines[equality_proof_line].statement;
    auto eq_ptr = std::get_if<EqualityFormula>(&equality_formula->data);
    if (!eq_ptr)
        throw std::invalid_argument("Selected line is not an equality");

    TermPtr lhs = eq_ptr->l;
    TermPtr rhs = eq_ptr->r;

    TermPtr term_to_substitute = lhs;

    // Current active goal
    FormulaPtr current_goal = targets[active_target_idx];

    // Perform substitution: replace term_to_substitute with rhs
    FormulaPtr new_goal = substitute_term_in_formula(current_goal, term_to_substitute, rhs);

    // Save old targets to history for backtracking
    target_history.push_back(targets);

    // Update active goal with rewritten formula
    targets[active_target_idx] = new_goal;
}

FormulaPtr Proof::get_active_target() const {
    if (active_target_idx >= targets.size()) {
        throw std::logic_error("Active goal index out of range");
    }
    return targets[active_target_idx];
}

bool Proof::is_valid() const {
    // A proof is valid if all targets have been completed
    return targets.empty();
}

void Proof::print() const {
    std::cout << "===== Proof State =====\n";

    // Assumptions
    std::cout << "Assumptions:\n";
    for (size_t i = 0; i < assumptions.size(); ++i) {
        std::cout << "  [" << i << "] " << assumptions[i]->to_string() << "\n";
    }

    // Proof lines
    std::cout << "Proof Lines:\n";
    for (size_t i = 0; i < lines.size(); ++i) {
        const auto &line = lines[i];
        std::cout << "  (" << i << ") " << line.statement->to_string() << "    [" << line.justification;
        if (!line.dependencies.empty()) {
            std::cout << " deps:";
            for (int d : line.dependencies) {
                std::cout << " " << d;
            }
        }
        std::cout << "]\n";
    }

    // Active goal and remaining targets
    std::cout << "Targets (" << targets.size() << " remaining):\n";
    for (size_t i = 0; i < targets.size(); ++i) {
        std::cout << "  [" << i << "] " << targets[i]->to_string();
        if (i == active_target_idx) {
            std::cout << "   <-- active goal";
        }
        std::cout << "\n";
    }
    if (targets.empty()) {
        std::cout << "  <all targets completed>\n";
    }

    std::cout << "=======================\n";
}

// --- Example rules ---
FormulaPtr assumption_rule(const std::vector<FormulaPtr> &, FormulaPtr claimed) { return claimed; }

FormulaPtr and_rule(const std::vector<FormulaPtr> &inputs, FormulaPtr claimed) {
    if (inputs.size() != 2)
        throw std::invalid_argument("AND rule needs 2 inputs");

    auto expected = Formula::make_and(inputs[0], inputs[1]);

    if (expected->to_string() != claimed->to_string())
        throw std::invalid_argument("Claimed does not match AND result");

    return claimed;
}

FormulaPtr eq_rule(const std::vector<FormulaPtr> &inputs, FormulaPtr claimed) {
    // This rule takes no inputs
    if (!inputs.empty())
        throw std::invalid_argument("EQ_SIMPLIFY rule takes no inputs");

    // Must be an equality formula
    auto eq_ptr = std::get_if<EqualityFormula>(&claimed->data);
    if (!eq_ptr)
        throw std::invalid_argument("Claimed formula is not an equality");

    // Check that lhs and rhs are equal (using to_string for structural equality)
    if (eq_ptr->l->to_string() != eq_ptr->r->to_string())
        throw std::invalid_argument("Left and right sides of equality are not equal");

    return claimed;
}

FormulaPtr implication_intro_rule(const std::vector<FormulaPtr> &inputs, FormulaPtr current_target) {
    // Check that the target is an implication
    auto impl_ptr = std::get_if<ImpliesFormula>(&current_target->data);
    if (!impl_ptr) {
        throw std::invalid_argument("implication_intro: target is not an implication A -> B");
    }

    // Add the antecedent (A) as a new assumption
    // (Assumptions live in Proof, so we'll need a hook there — see below)
    // For now, just return the consequent (B) as the new target
    return impl_ptr->r;
}

FormulaPtr forall_rule(const std::vector<FormulaPtr> &inputs, FormulaPtr claimed) {
    if (inputs.size() != 2)
        throw std::invalid_argument("FORALL rule requires 2 inputs: a forall and a term membership fact");

    // First input must be a forall formula
    auto forall_ptr = std::get_if<ForallFormula>(&inputs[0]->data);
    if (!forall_ptr)
        throw std::invalid_argument("First input must be a forall formula");

    // Second input must be a membership fact: element ∈ domain
    auto membership_ptr = std::get_if<RelationFormula>(&inputs[1]->data);
    if (!membership_ptr || membership_ptr->args.size() != 2 || membership_ptr->R != "∈")
        throw std::invalid_argument("Second input must be a membership relation (element ∈ domain)");

    TermPtr elem = membership_ptr->args[0];
    TermPtr fact_domain = membership_ptr->args[1];

    // Check that the forall domain matches the membership domain
    if (forall_ptr->domain->to_string() != fact_domain->to_string()) {
        throw std::invalid_argument("Element's domain does not match forall domain");
    }

    // Substitute the forall variable with the element in the inner formula
    TermPtr var_term = Term::make_variable(forall_ptr->v);
    FormulaPtr instantiated = substitute_in_formula(forall_ptr->inner, var_term, elem);

    // Check that the claimed formula matches the instantiated one
    if (instantiated->to_string() != claimed->to_string()) {
        throw std::invalid_argument("Claimed formula " + claimed->to_string() + " does not match derived formula " +
                                    instantiated->to_string());
    }

    return claimed;
}

FormulaPtr excluded_middle_rule(const std::vector<FormulaPtr> &inputs, FormulaPtr claimed) {
    if (!inputs.empty())
        throw std::invalid_argument("LEM requires no inputs");

    // The claimed formula must be an OR
    auto or_formula = std::get_if<OrFormula>(&claimed->data);
    if (!or_formula)
        throw std::invalid_argument("LEM: claimed formula is not an OR");

    // Right side must be a NOT
    auto not_formula = std::get_if<NotFormula>(&or_formula->r->data);
    if (!not_formula)
        throw std::invalid_argument("LEM: right-hand side is not a NOT");

    // Check that left side == inner of NOT
    if (or_formula->l->to_string() != not_formula->inner->to_string()) {
        throw std::invalid_argument("LEM: must be of the form (P ∨ ¬P)");
    }

    return claimed;
}

FormulaPtr cases_rule(const std::vector<FormulaPtr> &inputs, FormulaPtr claimed) {
    if (inputs.size() != 2)
        throw std::invalid_argument("CASES requires 2 inputs: (f -> t) and (¬f -> t)");

    // Input 0 must be implication
    auto imp1 = std::get_if<ImpliesFormula>(&inputs[0]->data);
    if (!imp1)
        throw std::invalid_argument("CASES: first input must be an implication");

    // Input 1 must be implication
    auto imp2 = std::get_if<ImpliesFormula>(&inputs[1]->data);
    if (!imp2)
        throw std::invalid_argument("CASES: second input must be an implication");

    // Extract f and t
    FormulaPtr f = imp1->l;
    FormulaPtr t1 = imp1->r;
    FormulaPtr left2 = imp2->l;
    FormulaPtr t2 = imp2->r;

    // Check right sides match claimed
    if (t1->to_string() != claimed->to_string() || t2->to_string() != claimed->to_string()) {
        throw std::invalid_argument("CASES: both implications must derive the claimed formula");
    }

    // Check second premise has form ¬f
    auto not_formula = std::get_if<NotFormula>(&left2->data);
    if (!not_formula)
        throw std::invalid_argument("CASES: second implication must have ¬f on the left side");

    if (not_formula->inner->to_string() != f->to_string()) {
        throw std::invalid_argument("CASES: mismatched f and ¬f assumptions");
    }

    return claimed;
}

FormulaPtr induction_rule(const std::vector<FormulaPtr> &inputs, FormulaPtr claimed) {
    if (inputs.size() != 2)
        throw std::invalid_argument("INDUCTION requires 2 inputs: base P(0) and step ∀k(P(k) → P(k+1))");

    // -----------------------------
    // Base: should be some P(0)
    // -----------------------------
    FormulaPtr base = inputs[0];

    // -----------------------------
    // Step: must be forall k ( P(k) → P(k+1) )
    // -----------------------------
    auto forall = std::get_if<ForallFormula>(&inputs[1]->data);
    if (!forall)
        throw std::invalid_argument("Step must be a forall formula");

    std::string var = forall->v;
    auto implies = std::get_if<ImpliesFormula>(&forall->inner->data);
    if (!implies)
        throw std::invalid_argument("Step must be an implication (P(k) → P(k+1))");

    TermPtr var_term = Term::make_variable(var);
    TermPtr succ_term = Term::make_function("+", {var_term, Term::make_constant("1")});
    TermPtr zero_term = Term::make_constant("0");

    // -----------------------------
    // Extract schema P(x) from step
    // -----------------------------
    FormulaPtr Pk = implies->l; // take the premise as P(k)

    // Verify base matches: P(k)[k := 0] == base
    FormulaPtr P0 = substitute_in_formula(Pk, var_term, zero_term);
    if (P0->to_string() != base->to_string()) {
        std::ostringstream ss;
        ss << "Base mismatch: expected " << base->to_string() << " but got " << P0->to_string() << " when substituting "
           << var << " := 0 in " << Pk->to_string();
        throw std::invalid_argument(ss.str());
    }

    // Verify step matches: RHS == P(k+1)
    FormulaPtr Psucc = substitute_in_formula(Pk, var_term, succ_term);
    if (implies->r->to_string() != Psucc->to_string()) {
        std::ostringstream ss;
        ss << "Step conclusion mismatch:\n"
           << "  Expected: " << Psucc->to_string() << "\n"
           << "  Got:      " << implies->r->to_string();
        throw std::invalid_argument(ss.str());
    }

    // -----------------------------
    // Construct final ∀n P(n)
    // -----------------------------
    TermPtr n_term = Term::make_variable("n");
    FormulaPtr Pn = substitute_in_formula(Pk, var_term, n_term);

    // TODO: don't do this.
    TermPtr natural_numbers = Term::make_constant("ℕ");
    FormulaPtr result = Formula::make_forall("n", natural_numbers, Pn);

    if (claimed->to_string() != result->to_string()) {
        throw std::invalid_argument("Claimed " + claimed->to_string() + " does not match derived " +
                                    result->to_string());
    }

    return claimed;
}
