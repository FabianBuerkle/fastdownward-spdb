#ifndef PDBS_SYMBOLIC_PATTERN_DATABASE_H
#define PDBS_SYMBOLIC_PATTERN_DATABASE_H

#include "types.h"
#include "pattern_database.h"
#include "../task_proxy.h"

#include "../symbolic/sym_variables.h"
#include <utility>
#include <vector>

using namespace symbolic;

namespace pdbs {
/*class SymbolicOperator : public AbstractOperator {
  private:
    SymVariables *sV;
    //BDD for progression effects and prevail conditions. 
    BDD effects;
    //BDD storing preconditions of progression operators.
    BDD preconditions;
  public:
    SymbolicOperator(SymVariables *sVars, const std::vector<FactPair> &prev_pairs,
        	     const std::vector<FactPair> &pre_pairs, const std::vector<FactPair> &eff_pairs,
		     int cost, const std::vector<size_t> &hash_multipliers);
};*/

/* Implementation of a Symbolic Pattern Database. Derived from Explicit Pattern
 * Database, since some of the methods for Explicit Pattern Database generation
 * apply also to SPDB construction. These Methods are likely multiply_out,
 * build_abstract_operator,
 * */
class SymbolicPatternDatabase /*: public PatternDatabase*/ {
    // SymVariables are needed for some BDD operations
    SymVariables *sV; 
    // Pattern which is used to Abstract the planning Task
    Pattern pattern;
    // The symbolic search creates Sets of States. These are represented as 
    // BDDs. All var-value pairs are used to generate the BDD for a reached Set of States.
    // These obtained BDDs are saved in a vector for each step. The
    // index of this vector represents the heuristic value of this Set of
    // States.
    std::vector<std::vector<BDD>> heuristicValueBuckets;
    // size of the PDB (MAYBE: the number of state Sets)
    std::size_t num_states;

    /*
      final h-values for abstract-states (MAYBE: h values for a StateSet).
      dead-ends are represented by numeric_limits<int>::max()
    */
    std::vector<int> distances;

    // multipliers for each variable for perfect hash function
    std::vector<std::size_t> hash_multipliers;

    //LIKELY METHODS (multiply_out, build_abstract_operators, is_goal_state) that can be used from parent class
    //METHOD which needs the most Change for proper SPDB
    void create_spdb(
        const TaskProxy &task_proxy,
        const std::vector<int> &operator_costs = std::vector<int>());

    /*
      The given concrete state is used to calculate the index of the
      according abstract state. This is only used for table lookup
      (distances) during search.
    */
    std::size_t hash_index(const State &state) const;
public:
    /*
      Important: It is assumed that the pattern (passed via Options) is
      sorted, contains no duplicates and is small enough so that the
      number of abstract states is below numeric_limits<int>::max()
      Parameters:
       dump:           If set to true, prints the construction time.
       operator_costs: Can specify individual operator costs for each
       operator. This is useful for action cost partitioning. If left
       empty, default operator costs are used.
    */
    SymbolicPatternDatabase(SymVariables *sV, const TaskProxy &task_proxy, const Pattern &pattern,bool dump = false,
		   	    const std::vector<int> &operator_costs = std::vector<int>());
    ~SymbolicPatternDatabase() = default;

    int get_value(const State &state) const;

    // Returns the pattern (i.e. all variables used) of the PDB
    const Pattern &get_pattern() const {
        return pattern;
    }

    // Returns the size (number of abstract states) of the PDB
    int get_size() const {
        return num_states;
    }

    /*
      Returns the average h-value over all states, where dead-ends are
      ignored (they neither increase the sum of all h-values nor the
      number of entries for the mean value calculation). If all states
      are dead-ends, infinity is returned.
      Note: This is only calculated when called; avoid repeated calls to
      this method!
    */
    double compute_mean_finite_h() const;

    // Returns true iff op has an effect on a variable in the pattern.
    bool is_operator_relevant(const OperatorProxy &op) const;
};
}

#endif
