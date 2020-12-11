#include "symbolic_pattern_database.h"

#include "../symbolic/transition_relation.h"

#include "match_tree.h"

#include "../algorithms/priority_queues.h"
#include "../task_utils/task_properties.h"
#include "../utils/collections.h"
#include "../utils/logging.h"
#include "../utils/math.h"
#include "../utils/timer.h"

#include <algorithm>
#include <cassert>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <string>
#include <vector>

using namespace std;
using namespace symbolic;

namespace pdbs {

SymbolicPatternDatabase::SymbolicPatternDatabase(SymVariables *sVars,
	       					 const TaskProxy &task_proxy,
	       					 const Pattern &pattern,
						 bool dump,
						 const vector<int> &operator_costs)
       	:sV(sVars), pattern(pattern) { 
  task_properties::verify_no_axioms(task_proxy);
  task_properties::verify_no_conditional_effects(task_proxy);
  assert(operator_costs.empty() ||
         operator_costs.size() == task_proxy.get_operators().size());
  assert(utils::is_sorted_unique(pattern));
  utils::Timer timer;
  create_spdb(task_proxy, operator_costs);//not implemented yet
  if (dump)
    cout << "SPDB construction time: " << timer << endl;
}

void SymbolicPatternDatabase::create_spdb(
  const TaskProxy &task_proxy, const vector<int> &operator_costs) {
  VariablesProxy variables = task_proxy.get_variables();
  vector<int> variable_to_index(variables.size(), -1);
  for (size_t i = 0; i < pattern.size(); ++i) {
    variable_to_index[pattern[i]] = i;
  }

  // used for effective storing of the TR for operators of same cost.
  std::vector<std::vector<TransitionRelation> > costSortedTR;
  for (OperatorProxy op : task_proxy.get_operators()) {
    int op_cost;
    if (operator_costs.empty()) {
      op_cost = op.get_cost();
      costSortedTR.resize(op.get_cost() + 1);
    } else {
      op_cost = operator_costs[op.get_id()];
    }
    OperatorID opID(op.get_id());
    TransitionRelation t = TransitionRelation(sV, opID, op_cost);
    t.init();
    costSortedTR[op_cost].emplace_back(t);
  }
  for (VariableProxy vari : task_proxy.get_variables()) {
    cout << "id: "<< vari.get_id() <<  ", domain size:" << vari.get_domain_size()<< endl;
    for (int a = 0; a < vari.get_domain_size(); a++) {
      cout << tasks::g_root_task->get_fact_name(FactPair(vari.get_id(), a))<<endl;
    }
    cout << endl;
  }
  // compute abstract goal var-val pairs
  vector<std::pair<int,int>> goalVarVal;
  for (FactProxy goal : task_proxy.get_goals()) {
    int var_id = goal.get_variable().get_id();
    int val = goal.get_value();
    cout << var_id << " " << val << endl;
    cout << sV->vars_index_pre(var_id) << "  " << val << endl;
    goalVarVal.emplace_back(std::make_pair(var_id, val));
  }
  std::vector<BDD> heuristicValueBubble;
  heuristicValueBubble.push_back(sV->getPartialStateBDD(goalVarVal));
  heuristicValueBuckets.push_back(heuristicValueBubble);
  BDD regressed = sV->oneBDD();
  int i = 0;// Variable to take care of actual heuristic Value for Set of States(h=i)
  BDD actualState = sV->getPartialStateBDD(goalVarVal);
  do {
    std::cout << "HEURISTIC VALUE BUCKET DESCRIPTION " << i << ": " << endl;
    std::cout << heuristicValueBuckets[i]  << std::endl;
    /*for (size_t j = 0; j <= heuristicValueBuckets[i].size() - 1; j++) {
      actualState = heuristicValueBuckets[i][j];
      std::string filename = "actualState" + std::to_string(i) + ".txt";
      sV->bdd_to_dot(actualState, filename);
      for (size_t a = 0; a < costSortedTR.size(); a++) {
	      for (size_t b = 0; b < costSortedTR[a].size(); b++) {
		      regressed = costSortedTR[a][b].preimage(actualState);
          std::string filename1 = "regressed" + std::to_string((int)b) +".txt";
          sV->bdd_to_dot(regressed, filename1);
          // Check, whether state has changed due to transition relation and add BDD into actual
          // Heuristic Bucket. If it is added, we also have to adjust the number of State Sets 
          // with the same cost
          *//* 
          if (regressed != actualState){
            //heuristicValueBuckets[a].push_back(regressed);
          }
        }
      }
    }*/
    i++;
  } while (i < heuristicValueBuckets.size());
}

int SymbolicPatternDatabase::get_value(const State &state) const {
    return 0;
}

}
