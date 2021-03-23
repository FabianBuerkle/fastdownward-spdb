#ifndef PDBS_SYMBOLIC_PATTERN_DATABASE_H
#define PDBS_SYMBOLIC_PATTERN_DATABASE_H

#include "types.h"
#include "pattern_database.h"
#include "../task_proxy.h"

#include "../symbolic/sym_variables.h"
#include <utility>
#include <vector>

using namespace symbolic;
using namespace std;

namespace pdbs {

/* Implementation of a Symbolic Pattern Database.*/
class SPDB /*: public PatternDatabase*/ {
    // SymVariables are needed for some BDD operations
    SymVariables *sV; 
    // Pattern which is used to Abstract the planning Task
    Pattern pattern;
    // The symbolic search creates Sets of States. These are represented as 
    // BDDs. All var-value pairs are used to generate the BDD for a reached Set of States.
    // These obtained BDDs are saved in a vector for each step. The
    // index of this vector represents the heuristic value of this Set of
    // States.
    vector<vector<BDD>> heuristicValueBuckets;
    vector<BDD> closedList;

    void create_spdb(const TaskProxy &task_proxy,
                     const vector<int> &operator_costs = vector<int>());

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
    SPDB(SymVariables *sV, const TaskProxy &task_proxy, 
         const Pattern &pattern,bool dump = false,
		   	 const std::vector<int> &operator_costs = std::vector<int>());
    
    ~SPDB() = default;

    BDD initial;
    int initialHVal;
    mutable int bestH;
    ADD heuristic;

    int get_value(const State &state) const;

    int compute_value(const BDD &state) const;
    
    // Returns the pattern (i.e. all variables used) of the SPDB
    const Pattern &get_pattern() const {
        return pattern;
    }

    /*
    // Returns the size (number of abstract states) of the PDB
    int get_size() const {
        return num_states;
    }*/

    /*
      Returns the average h-value over all states, where dead-ends are
      ignored (they neither increase the sum of all h-values nor the
      number of entries for the mean value calculation). If all states
      are dead-ends, infinity is returned.
      Note: This is only calculated when called; avoid repeated calls to
      this method!
    *//*
    double compute_mean_finite_h() const;

    // Returns true iff op has an effect on a variable in the pattern.
    bool is_operator_relevant(const OperatorProxy &op) const;*/
};
}

#endif
