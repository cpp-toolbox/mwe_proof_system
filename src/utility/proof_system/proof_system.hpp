#ifndef PROOF_SYSTEM_HPP
#define PROOF_SYSTEM_HPP

#include <memory>
#include <set>
#include <string>
#include <variant>
#include <vector>

// ---------- Helpers for our fixed mathematical language ----------
bool is_variable(const std::string &s);
bool is_constant(const std::string &s);
bool is_function(const std::string &s, int arity);
// bool is_tuple(std::string &s, int arity);
bool is_relation(const std::string &s, int arity);

// ---------- Terms ----------
struct Term;
using TermPtr = std::shared_ptr<Term>;

struct VariableTerm {
    std::string var;
};
struct ConstantTerm {
    std::string c;
};
struct FunctionTerm {
    std::string f;
    std::vector<TermPtr> args;
};
struct TupleTerm {
    std::vector<TermPtr> args;
};

/**
 * @brief terms are like objects which evaluate to something, or are variables, but don't have an inherit truth or
 * falsity to them
 */
struct Term {
    using variant_t = std::variant<VariableTerm, ConstantTerm, FunctionTerm, TupleTerm>;
    variant_t data;

    static TermPtr make_variable(const std::string &v);
    static TermPtr make_constant(const std::string &c);
    static TermPtr make_function(const std::string &f, std::vector<TermPtr> args);
    static TermPtr make_tuple(std::vector<TermPtr> args);

    std::string to_string() const;
    bool is_well_formed(std::string *err = nullptr) const;
};

struct Formula;
using FormulaPtr = std::shared_ptr<Formula>;

struct EqualityFormula {
    TermPtr l, r;
};
struct RelationFormula {
    std::string R;
    std::vector<TermPtr> args;
};
struct NotFormula {
    FormulaPtr inner;
};
struct OrFormula {
    FormulaPtr l, r;
};
struct AndFormula {
    FormulaPtr l, r;
};
struct ImpliesFormula {
    FormulaPtr l, r;
};
struct ForallFormula {
    std::string v;
    TermPtr domain; // e.g., "N" or any set term
    FormulaPtr inner;
};
struct ExistsFormula {
    std::string v;
    TermPtr domain;
    FormulaPtr inner;
};

/**
 * @brief a formula something that might be able to have a truth value so long as there are no free variables (aka a
 * sentence)
 *
 * a formula can still be x > 1 which doesn't have a truth value as x is not assigned, but if we said forall x in N, x >
 * 1, then it would become false, as now x is bound.
 *
 */
struct Formula {
    using variant_t = std::variant<EqualityFormula, RelationFormula, NotFormula, OrFormula, AndFormula, ImpliesFormula,
                                   ForallFormula, ExistsFormula>;
    variant_t data;

    static FormulaPtr make_eq(TermPtr a, TermPtr b);
    static FormulaPtr make_rel(const std::string &R, std::vector<TermPtr> args);
    static FormulaPtr make_not(FormulaPtr f);
    static FormulaPtr make_or(FormulaPtr a, FormulaPtr b);
    static FormulaPtr make_and(FormulaPtr a, FormulaPtr b);
    static FormulaPtr make_implies(FormulaPtr a, FormulaPtr b);
    static FormulaPtr make_forall(const std::string &v, TermPtr domain, FormulaPtr inner);
    static FormulaPtr make_exists(const std::string &v, TermPtr domain, FormulaPtr inner);

    std::string to_string() const;
    bool is_well_formed(std::string *err = nullptr) const;
};

// ---------- Term & Formula helpers ----------
bool occurs_in_term(const std::string &v, TermPtr t);
bool is_free_in(const std::string &v, FormulaPtr f);
void collect_vars_in_term(TermPtr t, std::set<std::string> &vars);
void collect_vars_in_formula(FormulaPtr f, std::set<std::string> &vars);
bool is_sentence(FormulaPtr f);

// ---------- Substitution ----------

TermPtr substitute_term_in_term(TermPtr u, TermPtr pattern, TermPtr replacement);
FormulaPtr substitute_term_in_formula(FormulaPtr phi, TermPtr pattern, TermPtr replacement);

// probably depcrecated...
TermPtr substitute_in_term(TermPtr u, TermPtr var, TermPtr t);
FormulaPtr substitute_in_formula(FormulaPtr phi, TermPtr var, TermPtr t);

bool is_substitutable(FormulaPtr phi, TermPtr var, TermPtr t);

void test();

#endif // PROOF_SYSTEM_HPP
