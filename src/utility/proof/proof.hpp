#ifndef PROOF_HPP
#define PROOF_HPP

#include "../proof_system/proof_system.hpp"
#include <functional>
#include <optional>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <vector>

// Represents a single line in the proof
struct ProofLine {
    FormulaPtr statement;
    std::string justification;
    std::vector<int> dependencies;
};

using LineRule = std::function<FormulaPtr(const std::vector<FormulaPtr> &, FormulaPtr)>;

// Forward-declare Proof so TargetRule can reference it
class Proof;

/**
 * @brief can mutate the Proof (add assumptions, set a new goal, etc.).
 * Inputs are TermPtr (makes instantiate_forall natural).
 */
using ProofModificationRule = std::function<void(Proof &, const std::vector<TermPtr> &)>;

class Proof {
  public:
    /// Note that it only takes in one target, which is fine, but internally it can hold a list of targets
    Proof(std::vector<FormulaPtr> assumptions, FormulaPtr target);

    void register_rule(const std::string &name, LineRule rule);

    void register_modification_rule(const std::string &name, ProofModificationRule rule);

    void add_line_to_proof(FormulaPtr claimed_statement, const std::string &rule_name,
                           const std::vector<int> &deps = {});

    void instantiate_forall(std::optional<TermPtr> requested_varaible = std::nullopt);
    void instantiate_implication();
    void instantiate_induction();

    void rewrite_target_using_equality(int equality_proof_line);

    FormulaPtr get_active_target() const;

    bool is_valid() const;
    void print() const;

  private:
    std::vector<ProofLine> lines;
    std::vector<FormulaPtr> assumptions;

    // things that have to be proven, during the course of this proof.
    std::vector<FormulaPtr> targets;
    // an index into the above
    size_t active_target_idx = 0;

    // Stack of old goals (so we can inspect or implement backtracking)
    std::vector<std::vector<FormulaPtr>> target_history;

    std::unordered_map<std::string, LineRule> rules;
    std::unordered_map<std::string, ProofModificationRule> target_rules;
};

// ---------- Example built-in rules ----------
FormulaPtr assumption_rule(const std::vector<FormulaPtr> &, FormulaPtr claimed);
FormulaPtr and_rule(const std::vector<FormulaPtr> &inputs, FormulaPtr claimed);
FormulaPtr forall_rule(const std::vector<FormulaPtr> &inputs, FormulaPtr claimed);
FormulaPtr eq_rule(const std::vector<FormulaPtr> &inputs, FormulaPtr claimed);
FormulaPtr induction_rule(const std::vector<FormulaPtr> &inputs, FormulaPtr claimed);
FormulaPtr excluded_middle_rule(const std::vector<FormulaPtr> &inputs, FormulaPtr claimed);
FormulaPtr cases_rule(const std::vector<FormulaPtr> &inputs, FormulaPtr claimed);

#endif // PROOF_HPP
