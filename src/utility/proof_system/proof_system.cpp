#include "proof_system.hpp"

#include <cctype>
#include <iostream>
#include <memory>
#include <set>
#include <sstream>
#include <string>
#include <variant>
#include <vector>
#include <unordered_set>

// ---------- Helpers for our fixed mathematical language ----------

// Variables: v1, v2, ...
bool is_variable(const std::string &s) {
    if (s.empty() || s[0] != 'v')
        return false;
    for (size_t i = 1; i < s.size(); ++i)
        if (!std::isdigit(static_cast<unsigned char>(s[i])))
            return false;
    return s.size() > 1;
}

// Constants: "0", "1"
bool is_constant(const std::string &s) { return s == "0" || s == "1"; }

// Function symbols: succ (1-ary), + (2-ary), * (2-ary)
bool is_function(const std::string &s, int arity) {
    return (s == "succ" && arity == 1) || (s == "+" && arity == 2) || (s == "*" && arity == 2);
}

// Relation symbols: < (2-ary)
bool is_relation(const std::string &s, int arity) { return (s == "<" && arity == 2); }

// ---------- Terms ----------

TermPtr Term::make_variable(const std::string &v) { return std::make_shared<Term>(Term{VariableTerm{v}}); }
TermPtr Term::make_constant(const std::string &c) { return std::make_shared<Term>(Term{ConstantTerm{c}}); }
TermPtr Term::make_function(const std::string &f, std::vector<TermPtr> args) {
    return std::make_shared<Term>(Term{FunctionTerm{f, std::move(args)}});
}
TermPtr Term::make_tuple(std::vector<TermPtr> args) { return std::make_shared<Term>(Term{TupleTerm{std::move(args)}}); }

std::string Term::to_string() const {
    if (auto p = std::get_if<VariableTerm>(&data))
        return p->var;
    if (auto p = std::get_if<ConstantTerm>(&data))
        return p->c;
    if (auto p = std::get_if<FunctionTerm>(&data)) {
        std::unordered_set<std::string> infix_operators = {"+", "*", "∈"};
        std::ostringstream ss;
        if (infix_operators.count(p->f) && p->args.size() == 2) {
            ss << "(" << p->args[0]->to_string() << " " << p->f << " " << p->args[1]->to_string() << ")";
        } else {
            ss << p->f << "(";
            for (size_t i = 0; i < p->args.size(); ++i) {
                ss << p->args[i]->to_string();
                if (i + 1 < p->args.size())
                    ss << ", ";
            }
            ss << ")";
        }
        return ss.str();
    }
    if (auto p = std::get_if<TupleTerm>(&data)) {
        std::ostringstream ss;
        ss << "(";
        for (size_t i = 0; i < p->args.size(); ++i) {
            ss << p->args[i]->to_string();
            if (i + 1 < p->args.size())
                ss << ", ";
        }
        ss << ")";
    }
    return "?";
}

bool Term::is_well_formed(std::string *err) const {
    if (auto p = std::get_if<VariableTerm>(&data)) {
        if (!is_variable(p->var)) {
            if (err)
                *err = "bad var";
            return false;
        }
        return true;
    }
    if (auto p = std::get_if<ConstantTerm>(&data)) {
        if (!is_constant(p->c)) {
            if (err)
                *err = "bad const";
            return false;
        }
        return true;
    }
    if (auto p = std::get_if<FunctionTerm>(&data)) {
        if (!is_function(p->f, (int)p->args.size())) {
            if (err)
                *err = "bad function/arity";
            return false;
        }
        for (auto &a : p->args)
            if (!a->is_well_formed(err))
                return false;
        return true;
    }
    return false;
}

// ---------- Formulas ----------

FormulaPtr Formula::make_eq(TermPtr a, TermPtr b) { return std::make_shared<Formula>(Formula{EqualityFormula{a, b}}); }
FormulaPtr Formula::make_rel(const std::string &R, std::vector<TermPtr> args) {
    return std::make_shared<Formula>(Formula{RelationFormula{R, std::move(args)}});
}
FormulaPtr Formula::make_not(FormulaPtr f) { return std::make_shared<Formula>(Formula{NotFormula{f}}); }
FormulaPtr Formula::make_or(FormulaPtr a, FormulaPtr b) { return std::make_shared<Formula>(Formula{OrFormula{a, b}}); }
FormulaPtr Formula::make_and(FormulaPtr a, FormulaPtr b) {
    return std::make_shared<Formula>(Formula{AndFormula{a, b}});
}
FormulaPtr Formula::make_implies(FormulaPtr a, FormulaPtr b) {
    return std::make_shared<Formula>(Formula{ImpliesFormula{a, b}});
}
FormulaPtr Formula::make_forall(const std::string &v, TermPtr domain, FormulaPtr inner) {
    return std::make_shared<Formula>(Formula{ForallFormula{v, domain, inner}});
}
FormulaPtr Formula::make_exists(const std::string &v, TermPtr domain, FormulaPtr inner) {
    return std::make_shared<Formula>(Formula{ExistsFormula{v, domain, inner}});
}

std::string Formula::to_string() const {
    if (auto p = std::get_if<EqualityFormula>(&data)) {
        return "(" + p->l->to_string() + " = " + p->r->to_string() + ")";
    }
    if (auto p = std::get_if<RelationFormula>(&data)) {
        std::unordered_set<std::string> infix_relations = {"=", "∈", "<", "≤", ">"};
        std::ostringstream ss;

        if (infix_relations.count(p->R) && p->args.size() == 2) {
            // Treat as infix
            ss << "(" << p->args[0]->to_string() << " " << p->R << " " << p->args[1]->to_string() << ")";
        } else {
            // Regular function-style relation
            ss << p->R << "(";
            for (size_t i = 0; i < p->args.size(); ++i) {
                if (i > 0)
                    ss << ", ";
                ss << p->args[i]->to_string();
            }
            ss << ")";
        }
        return ss.str();
    }
    if (auto p = std::get_if<NotFormula>(&data)) {
        return "(¬" + p->inner->to_string() + ")";
    }
    if (auto p = std::get_if<OrFormula>(&data)) {
        return "(" + p->l->to_string() + " ∨ " + p->r->to_string() + ")";
    }
    if (auto p = std::get_if<AndFormula>(&data)) {
        return "(" + p->l->to_string() + " ∧ " + p->r->to_string() + ")";
    }
    if (auto p = std::get_if<ImpliesFormula>(&data)) {
        return "(" + p->l->to_string() + " → " + p->r->to_string() + ")";
    }
    if (auto p = std::get_if<ForallFormula>(&data)) {
        return "(∀" + p->v + " ∈ " + p->domain->to_string() + ")(" + p->inner->to_string() + ")";
    }
    if (auto p = std::get_if<ExistsFormula>(&data)) {
        return "(∃" + p->v + " ∈ " + p->domain->to_string() + ")(" + p->inner->to_string() + ")";
    }
    return "?";
}

bool Formula::is_well_formed(std::string *err) const {
    if (auto p = std::get_if<EqualityFormula>(&data)) {
        return p->l->is_well_formed(err) && p->r->is_well_formed(err);
    }
    if (auto p = std::get_if<RelationFormula>(&data)) {
        if (!is_relation(p->R, (int)p->args.size())) {
            if (err)
                *err = "bad relation/arity";
            return false;
        }
        for (auto &a : p->args)
            if (!a->is_well_formed(err))
                return false;
        return true;
    }
    if (auto p = std::get_if<NotFormula>(&data))
        return p->inner->is_well_formed(err);
    if (auto p = std::get_if<OrFormula>(&data)) {
        return p->l->is_well_formed(err) && p->r->is_well_formed(err);
    }
    if (auto p = std::get_if<AndFormula>(&data)) {
        return p->l->is_well_formed(err) && p->r->is_well_formed(err);
    }
    if (auto p = std::get_if<ImpliesFormula>(&data)) {
        return p->l->is_well_formed(err) && p->r->is_well_formed(err);
    }
    // NOTE: we don't check if the domain is well formed, should we do that?
    if (auto p = std::get_if<ForallFormula>(&data)) {
        if (!is_variable(p->v)) {
            if (err)
                *err = "bad forall var";
            return false;
        }
        return p->inner->is_well_formed(err);
    }
    if (auto p = std::get_if<ExistsFormula>(&data)) {
        if (!is_variable(p->v)) {
            if (err)
                *err = "bad exists var";
            return false;
        }
        return p->inner->is_well_formed(err);
    }
    return false;
}

// ---------- Helper: check if variable occurs in a term ----------
bool occurs_in_term(const std::string &v, TermPtr t) {
    if (!t)
        return false;
    if (auto p = std::get_if<VariableTerm>(&t->data))
        return p->var == v;
    if (auto p = std::get_if<ConstantTerm>(&t->data))
        return false;
    if (auto p = std::get_if<FunctionTerm>(&t->data)) {
        for (auto &arg : p->args) {
            if (occurs_in_term(v, arg))
                return true;
        }
    }
    if (auto p = std::get_if<TupleTerm>(&t->data)) {
        for (auto &arg : p->args) {
            if (occurs_in_term(v, arg))
                return true;
        }
    }
    return false;
}

// ---------- Free variable check ----------
bool is_free_in(const std::string &v, FormulaPtr f) {
    if (!f)
        return false;

    if (auto p = std::get_if<EqualityFormula>(&f->data)) {
        return occurs_in_term(v, p->l) || occurs_in_term(v, p->r);
    }
    if (auto p = std::get_if<RelationFormula>(&f->data)) {
        for (auto &arg : p->args)
            if (occurs_in_term(v, arg))
                return true;
        return false;
    }
    if (auto p = std::get_if<NotFormula>(&f->data)) {
        return is_free_in(v, p->inner);
    }
    if (auto p = std::get_if<OrFormula>(&f->data)) {
        return is_free_in(v, p->l) || is_free_in(v, p->r);
    }
    if (auto p = std::get_if<AndFormula>(&f->data)) {
        return is_free_in(v, p->l) || is_free_in(v, p->r);
    }
    if (auto p = std::get_if<ImpliesFormula>(&f->data)) {
        return is_free_in(v, p->l) || is_free_in(v, p->r);
    }
    if (auto p = std::get_if<ForallFormula>(&f->data)) {
        if (p->v == v)
            return false; // bound by this quantifier
        return is_free_in(v, p->inner);
    }
    if (auto p = std::get_if<ExistsFormula>(&f->data)) {
        if (p->v == v)
            return false; // bound by this quantifier
        return is_free_in(v, p->inner);
    }
    return false;
}

// ---------- Helper: collect all variables in a term ----------
void collect_vars_in_term(TermPtr t, std::set<std::string> &vars) {
    if (!t)
        return;
    if (auto p = std::get_if<VariableTerm>(&t->data)) {
        vars.insert(p->var);
    } else if (auto p = std::get_if<FunctionTerm>(&t->data)) {
        for (auto &arg : p->args)
            collect_vars_in_term(arg, vars);
    } else if (auto p = std::get_if<TupleTerm>(&t->data)) {
        for (auto &arg : p->args)
            collect_vars_in_term(arg, vars);
    }
}

// ---------- Helper: collect all variables in a formula ----------
void collect_vars_in_formula(FormulaPtr f, std::set<std::string> &vars) {
    if (!f)
        return;
    if (auto p = std::get_if<EqualityFormula>(&f->data)) {
        collect_vars_in_term(p->l, vars);
        collect_vars_in_term(p->r, vars);
    } else if (auto p = std::get_if<RelationFormula>(&f->data)) {
        for (auto &arg : p->args)
            collect_vars_in_term(arg, vars);
    } else if (auto p = std::get_if<NotFormula>(&f->data)) {
        collect_vars_in_formula(p->inner, vars);
    } else if (auto p = std::get_if<OrFormula>(&f->data)) {
        collect_vars_in_formula(p->l, vars);
        collect_vars_in_formula(p->r, vars);
    } else if (auto p = std::get_if<AndFormula>(&f->data)) {
        collect_vars_in_formula(p->l, vars);
        collect_vars_in_formula(p->r, vars);
    } else if (auto p = std::get_if<ImpliesFormula>(&f->data)) {
        collect_vars_in_formula(p->l, vars);
        collect_vars_in_formula(p->r, vars);
    } else if (auto p = std::get_if<ForallFormula>(&f->data)) {
        collect_vars_in_formula(p->inner, vars);
    } else if (auto p = std::get_if<ExistsFormula>(&f->data)) {
        collect_vars_in_formula(p->inner, vars);
    }
}

// ---------- Check if formula is a sentence ----------
bool is_sentence(FormulaPtr f) {
    std::set<std::string> vars;
    collect_vars_in_formula(f, vars);
    for (const auto &v : vars) {
        if (is_free_in(v, f))
            return false;
    }
    return true;
}

// ---------- Substitute all occurrences of 'pattern' with 'replacement' in term 'u' ----------
TermPtr substitute_term_in_term(TermPtr u, TermPtr pattern, TermPtr replacement) {
    if (!u)
        return nullptr;

    // If the current term matches the pattern, replace it
    if (u->to_string() == pattern->to_string()) {
        return replacement;
    }

    if (auto p = std::get_if<FunctionTerm>(&u->data)) {
        std::vector<TermPtr> new_args;
        for (auto &arg : p->args) {
            new_args.push_back(substitute_term_in_term(arg, pattern, replacement));
        }
        return Term::make_function(p->f, new_args);
    }

    if (auto p = std::get_if<TupleTerm>(&u->data)) {
        std::vector<TermPtr> new_args;
        for (auto &arg : p->args) {
            new_args.push_back(substitute_term_in_term(arg, pattern, replacement));
        }
        return Term::make_tuple(new_args);
    }

    // Variables and constants that do not match pattern remain unchanged
    if (auto p = std::get_if<VariableTerm>(&u->data)) {
        return Term::make_variable(p->var);
    }

    if (auto p = std::get_if<ConstantTerm>(&u->data)) {
        return Term::make_constant(p->c);
    }

    return nullptr;
}

// ---------- Substitute term 'pattern' with 'replacement' in formula 'phi' ----------
FormulaPtr substitute_term_in_formula(FormulaPtr phi, TermPtr pattern, TermPtr replacement) {
    if (!phi)
        return nullptr;

    if (auto p = std::get_if<EqualityFormula>(&phi->data)) {
        auto new_l = substitute_term_in_term(p->l, pattern, replacement);
        auto new_r = substitute_term_in_term(p->r, pattern, replacement);
        return Formula::make_eq(new_l, new_r);
    }

    if (auto p = std::get_if<RelationFormula>(&phi->data)) {
        std::vector<TermPtr> new_args;
        for (auto &arg : p->args) {
            new_args.push_back(substitute_term_in_term(arg, pattern, replacement));
        }
        return Formula::make_rel(p->R, new_args);
    }

    if (auto p = std::get_if<NotFormula>(&phi->data)) {
        return Formula::make_not(substitute_term_in_formula(p->inner, pattern, replacement));
    }

    if (auto p = std::get_if<OrFormula>(&phi->data)) {
        auto new_l = substitute_term_in_formula(p->l, pattern, replacement);
        auto new_r = substitute_term_in_formula(p->r, pattern, replacement);
        return Formula::make_or(new_l, new_r);
    }

    if (auto p = std::get_if<AndFormula>(&phi->data)) {
        auto new_l = substitute_term_in_formula(p->l, pattern, replacement);
        auto new_r = substitute_term_in_formula(p->r, pattern, replacement);
        return Formula::make_and(new_l, new_r);
    }

    if (auto p = std::get_if<ImpliesFormula>(&phi->data)) {
        auto new_l = substitute_term_in_formula(p->l, pattern, replacement);
        auto new_r = substitute_term_in_formula(p->r, pattern, replacement);
        return Formula::make_implies(new_l, new_r);
    }

    if (auto p = std::get_if<ForallFormula>(&phi->data)) {
        return Formula::make_forall(p->v, p->domain, substitute_term_in_formula(p->inner, pattern, replacement));
    }

    if (auto p = std::get_if<ExistsFormula>(&phi->data)) {
        return Formula::make_exists(p->v, p->domain, substitute_term_in_formula(p->inner, pattern, replacement));
    }

    return nullptr;
}

// ---------- Substitute variable var with term t in term u ----------
TermPtr substitute_in_term(TermPtr u, TermPtr var, TermPtr t) {
    if (!u)
        return nullptr;

    if (auto p = std::get_if<VariableTerm>(&u->data)) {
        if (var && p->var == std::get<VariableTerm>(var->data).var)
            return t; // matched variable
        else
            return Term::make_variable(p->var); // not the variable to replace
    }

    if (auto p = std::get_if<ConstantTerm>(&u->data)) {
        return Term::make_constant(p->c); // constant stays
    }

    if (auto p = std::get_if<FunctionTerm>(&u->data)) {
        std::vector<TermPtr> new_args;
        for (auto &arg : p->args) {
            new_args.push_back(substitute_in_term(arg, var, t)); // recurse
        }
        return Term::make_function(p->f, new_args);
    }

    return nullptr;
}

// ---------- Substitute variable 'var' with term 't' in formula 'phi'
// ----------

FormulaPtr substitute_in_formula(FormulaPtr phi, TermPtr var, TermPtr t) {
    if (!phi)
        return nullptr;

    if (auto p = std::get_if<EqualityFormula>(&phi->data)) {
        auto new_l = substitute_in_term(p->l, var, t);
        auto new_r = substitute_in_term(p->r, var, t);
        return Formula::make_eq(new_l, new_r);
    }

    if (auto p = std::get_if<RelationFormula>(&phi->data)) {
        std::vector<TermPtr> new_args;
        for (auto &arg : p->args) {
            new_args.push_back(substitute_in_term(arg, var, t));
        }
        return Formula::make_rel(p->R, new_args);
    }

    if (auto p = std::get_if<NotFormula>(&phi->data)) {
        return Formula::make_not(substitute_in_formula(p->inner, var, t));
    }

    if (auto p = std::get_if<OrFormula>(&phi->data)) {
        auto new_l = substitute_in_formula(p->l, var, t);
        auto new_r = substitute_in_formula(p->r, var, t);
        return Formula::make_or(new_l, new_r);
    }

    if (auto p = std::get_if<AndFormula>(&phi->data)) {
        auto new_l = substitute_in_formula(p->l, var, t);
        auto new_r = substitute_in_formula(p->r, var, t);
        return Formula::make_and(new_l, new_r);
    }

    if (auto p = std::get_if<ImpliesFormula>(&phi->data)) {
        auto new_l = substitute_in_formula(p->l, var, t);
        auto new_r = substitute_in_formula(p->r, var, t);
        return Formula::make_implies(new_l, new_r);
    }

    if (auto p = std::get_if<ForallFormula>(&phi->data)) {
        // If the bound variable is the same as the variable we want to replace,
        // stop
        if (var && p->v == std::get<VariableTerm>(var->data).var)
            return phi; // x is bound here, do not substitute
        return Formula::make_forall(p->v, p->domain, substitute_in_formula(p->inner, var, t));
    }

    if (auto p = std::get_if<ExistsFormula>(&phi->data)) {
        if (var && p->v == std::get<VariableTerm>(var->data).var)
            return phi; // x is bound here, do not substitute
        return Formula::make_exists(p->v, p->domain, substitute_in_formula(p->inner, var, t));
    }

    return nullptr;
}

// ---------- Check if term t is substitutable for variable var in formula phi
// ----------
bool is_substitutable(FormulaPtr phi, TermPtr var, TermPtr t) {
    if (!phi || !var || !t)
        return false;

    // Atomic formulas: always safe
    if (auto p = std::get_if<EqualityFormula>(&phi->data)) {
        return true;
    }
    if (auto p = std::get_if<RelationFormula>(&phi->data)) {
        return true;
    }

    // Negation: recurse
    if (auto p = std::get_if<NotFormula>(&phi->data)) {
        return is_substitutable(p->inner, var, t);
    }

    // Disjunction: recurse both sides
    if (auto p = std::get_if<OrFormula>(&phi->data)) {
        return is_substitutable(p->l, var, t) && is_substitutable(p->r, var, t);
    }

    if (auto p = std::get_if<AndFormula>(&phi->data)) {
        return is_substitutable(p->l, var, t) && is_substitutable(p->r, var, t);
    }

    if (auto p = std::get_if<ImpliesFormula>(&phi->data)) {
        return is_substitutable(p->l, var, t) && is_substitutable(p->r, var, t);
    }

    // Universal quantifier: (∀y)(α)
    if (auto p = std::get_if<ForallFormula>(&phi->data)) {
        std::string x_name = std::get<VariableTerm>(var->data).var;
        std::string y_name = p->v;

        if (!is_free_in(x_name, phi))
            return true;                // condition 4(a)
        if (!occurs_in_term(y_name, t)) // condition 4(b)
            return is_substitutable(p->inner, var, t);
        return false;
    }

    // Existential quantifier: same logic as ∀
    if (auto p = std::get_if<ExistsFormula>(&phi->data)) {
        std::string x_name = std::get<VariableTerm>(var->data).var;
        std::string y_name = p->v;

        if (!is_free_in(x_name, phi))
            return true;
        if (!occurs_in_term(y_name, t))
            return is_substitutable(p->inner, var, t);
        return false;
    }

    return false;
}

// ---------- Demo ----------

void test() {

    TermPtr natural_numbers = Term::make_constant("ℕ");
    {
        auto v1 = Term::make_variable("v1");
        auto v2 = Term::make_variable("v2");
        auto zero = Term::make_constant("0");
        auto one = Term::make_constant("1");

        auto sum = Term::make_function("+", {v1, one});   // v1 + 1
        auto prod = Term::make_function("*", {v1, v2});   // v1 * v2
        auto succ_v1 = Term::make_function("succ", {v1}); // succ(v1)

        auto phi1 = Formula::make_eq(sum, prod);                       // (v1 + 1 = v1 * v2)
        auto phi2 = Formula::make_rel("<", {zero, succ_v1});           // (0 < succ(v1))
        auto phi3 = Formula::make_forall("v1", natural_numbers, phi2); // ∀v1 (0 < succ(v1))
        auto phi4 = Formula::make_exists("v2", natural_numbers, phi1); // ∃v2 (v1 + 1 = v1 * v2)

        std::cout << phi3->to_string() << "\n";
        std::cout << phi4->to_string() << "\n";

        std::string err;
        if (!phi4->is_well_formed(&err))
            std::cout << "Error: " << err << "\n";
    }
    {
        auto v1 = Term::make_variable("v1");
        auto v2 = Term::make_variable("v2");
        auto v3 = Term::make_variable("v3");
        auto zero = Term::make_constant("0");

        auto s_v2 = Term::make_function("succ", {v2});                         // S(v2)
        auto eq1 = Formula::make_eq(v1, s_v2);                                 // v1 = S(v2)
        auto eq2 = Formula::make_eq(v3, v2);                                   // v3 = v2
        auto disj = Formula::make_or(eq1, eq2);                                // (v1 = S(v2) ∨ v3 = v2)
        auto forall_v3 = Formula::make_forall("v3", natural_numbers, disj);    // ∀v3(...)
        auto not_phi = Formula::make_not(forall_v3);                           // ¬∀v3(...)
        auto forall_v2 = Formula::make_forall("v2", natural_numbers, not_phi); // ∀v2 ¬∀v3(...)

        std::cout << forall_v2->to_string() << "\n";

        std::cout << "v1 free? " << is_free_in("v1", forall_v2) << "\n";
        std::cout << "v2 free? " << is_free_in("v2", forall_v2) << "\n";
        std::cout << "v3 free? " << is_free_in("v3", forall_v2) << "\n";
    }
    {
        // Example: ∀v1∀v2(v1 + v2 = 0) ∨ v1 = succ(0)
        auto v1 = Term::make_variable("v1");
        auto v2 = Term::make_variable("v2");
        auto zero = Term::make_constant("0");

        auto sum = Term::make_function("+", {v1, v2});
        auto eq1 = Formula::make_eq(sum, zero); // v1 + v2 = 0
        auto forall_v2 = Formula::make_forall("v2", natural_numbers, eq1);
        auto forall_v1 = Formula::make_forall("v1", natural_numbers, forall_v2); // ∀v1∀v2(v1+v2=0)

        auto succ0 = Term::make_function("succ", {zero});
        auto eq2 = Formula::make_eq(v1, succ0);       // v1 = S(0)
        auto disj = Formula::make_or(forall_v1, eq2); // (∀v1∀v2(v1+v2=0)) ∨ v1=S(0)

        std::cout << disj->to_string() << "\n";

        std::cout << "Is sentence? " << (is_sentence(disj) ? "Yes" : "No") << "\n";
    }
    {
        auto v1 = Term::make_variable("v1");
        auto v2 = Term::make_variable("v2");
        auto zero = Term::make_constant("0");
        auto one = Term::make_constant("1");

        // v1 + v2 = 0
        auto sum = Term::make_function("+", {v1, v2});
        auto eq1 = Formula::make_eq(sum, zero);

        // v1 * v2 = 1
        auto prod = Term::make_function("*", {v1, v2});
        auto eq2 = Formula::make_eq(prod, one);

        // (v1 + v2 = 0) ∨ (v1 * v2 = 1)
        auto disj = Formula::make_or(eq1, eq2);

        // ∀v2 (...)
        auto forall_v2 = Formula::make_forall("v2", natural_numbers, disj);

        // ∀v1 ∀v2 (...)
        auto forall_v1 = Formula::make_forall("v1", natural_numbers, forall_v2);

        std::cout << forall_v1->to_string() << "\n";

        std::cout << "Is sentence? " << (is_sentence(forall_v1) ? "Yes" : "No") << "\n";
    }

    {
        auto v1 = Term::make_variable("v1");
        auto v2 = Term::make_variable("v2");
        auto one = Term::make_constant("1");

        // Term: (v1 + v2)
        auto sum = Term::make_function("+", {v1, v2});
        std::cout << "Original term: " << sum->to_string() << "\n";

        // Substitute v1 by 1
        auto new_term = substitute_in_term(sum, v1, one);
        std::cout << "After substituting v1 by 1: " << new_term->to_string() << "\n";

        // Substitute v2 by v1
        auto new_term2 = substitute_in_term(sum, v2, v1);
        std::cout << "After substituting v2 by v1: " << new_term2->to_string() << "\n";
    }
    {
        auto x = Term::make_variable("x");
        auto y = Term::make_variable("y");
        auto z = Term::make_variable("z");
        auto c = Term::make_constant("c");

        auto g_c = Term::make_function("g", {c});
        auto h_x = Term::make_function("h", {x});
        auto g_x = Term::make_function("g", {x});

        // Q(g(x), z)
        auto Q_gx_z = Formula::make_rel("Q", {g_x, z});
        auto forall_x_Q = Formula::make_forall("x", natural_numbers, Q_gx_z); // ∀x Q(g(x), z)

        // R(x, h(x))
        auto R_x_hx = Formula::make_rel("R", {x, h_x});
        auto forall_y_R = Formula::make_forall("y", natural_numbers, R_x_hx); // ∀y R(x, h(x))

        // P(x, y)
        auto P_xy = Formula::make_rel("P", {x, y});

        // φ = P(x,y) ∨ [∀x Q(g(x), z) ∨ ∀y R(x, h(x))]
        auto inner_disj = Formula::make_or(forall_x_Q, forall_y_R);
        auto phi = Formula::make_or(P_xy, inner_disj);

        std::cout << "Original φ: " << phi->to_string() << "\n";

        // Substitute x by g(c)
        auto phi_subst = substitute_in_formula(phi, x, g_c);
        std::cout << "After substituting x by g(c): " << phi_subst->to_string() << "\n";
    }
    {

        auto x = Term::make_variable("x");
        auto y = Term::make_variable("y");
        auto z = Term::make_variable("z");
        auto c = Term::make_constant("c");

        auto g_c = Term::make_function("g", {c});
        auto h_x = Term::make_function("h", {x});
        auto g_x = Term::make_function("g", {x});

        // φ = ∀y (R(x, h(x)))
        auto R_x_hx = Formula::make_rel("R", {x, h_x});
        auto forall_y_R = Formula::make_forall("y", natural_numbers, R_x_hx);

        std::cout << "Formula: " << forall_y_R->to_string() << "\n";

        // Check if g(c) is substitutable for x
        bool safe = is_substitutable(forall_y_R, x, g_c);
        std::cout << "Is g(c) substitutable for x? " << (safe ? "Yes" : "No") << "\n";

        // Example where substitution is unsafe:
        // φ = ∀y (R(y, x)), try to substitute t = y
        auto R_y_x = Formula::make_rel("R", {y, x});
        auto forall_y_R2 = Formula::make_forall("y", natural_numbers, R_y_x);
        bool safe2 = is_substitutable(forall_y_R2, x, y);
        std::cout << "Formula: " << forall_y_R2->to_string() << "\n";
        std::cout << "Is y substitutable for x? " << (safe2 ? "Yes" : "No") << "\n";
    }
}
