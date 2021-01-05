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
  create_spdb(task_proxy, operator_costs);
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
  std::vector<std::vector<TransitionRelation *> > costSortedTR;
  for (OperatorProxy op : task_proxy.get_operators()) {
    int op_cost;
    if (operator_costs.empty()) {
      op_cost = op.get_cost();
      costSortedTR.resize(op.get_cost() + 1);
    } else {
      op_cost = operator_costs[op.get_id()];
    }
    OperatorID opID(op.get_id());
    TransitionRelation *t = new TransitionRelation(sV, opID, op_cost);
    t->init();
    costSortedTR[op_cost].emplace_back(t);
  }

  BDD goals = sV->oneBDD();
  for (FactProxy goal : task_proxy.get_goals()) {
    int var_id = goal.get_variable().get_id();
    int val = goal.get_value();
    goals *= sV->preBDD(var_id, val);
  } 
  
  heuristicValueBuckets.resize(costSortedTR.size()-1);
  heuristicValueBuckets[0].push_back(goals);
  int i = 0;// Variable to take care of actual heuristic Value for Set of States(h=i)
  //cout << i << endl;
  BDD actualState;
  int debug = 0; 
  do {
    for (size_t j = 0; j <= heuristicValueBuckets[i].size() - 1; j++) {
      actualState = heuristicValueBuckets[i][j];
      //vector<int> preimagesTR;
      //vector<int> preimagesNoImprovement;
      //bool alreadyCreatedPred = 0;
      
      for (size_t a = 0; a < costSortedTR.size(); a++) {
	if (heuristicValueBuckets.size() - 1 < i + a) {
	  heuristicValueBuckets.resize(i + a + 1);
	} 
	for (size_t b = 0; b < costSortedTR[a].size(); b++) {
	  BDD regressed = (costSortedTR[a][b])->preimage(actualState);
	  // Check, whether state has changed due to transition relation and add BDD into actual
          // Heuristic Bucket. If it is added, we also have to adjust the number of State Sets 
          // with the same cost
          if (regressed != actualState && regressed != sV->zeroBDD()) {
	    //preimagesTR.push_back(b);
	    bool not_improved = 0;
	    for (int c = heuristicValueBuckets.size()-1; c > -1; c--) {
	      vector<BDD> found = heuristicValueBuckets[c];
	      for (size_t d = 0; d < found.size(); d++) {
	        if (found[d] * !regressed == sV->zeroBDD() or found[d] * regressed == regressed) {
		  //if (c > i) {
		  //  alreadyCreatedPred = 1;
		  //}
		  not_improved = 1;
		  break;
		} 
	      }
  	      if (not_improved) {
		//preimagesNoImprovement.push_back(b);
		break;
	      }
	    }
	    if (not_improved) {
	      continue;
	    } 
	    /*
	    if (debug == 1) {
	      std::string filename1 = "regressed" + std::to_string((int)i) + 
	      "_" + std::to_string((int)j) +  "_" + std::to_string((int)b) +".gv";
              sV->bdd_to_dot(regressed, filename1);
              cout <<"REGRESSION DUE TO TR #" << b << ": " << endl;
	    }
	    */
	    heuristicValueBuckets[i+a].push_back(regressed);
	  }
        }
      }
      /*vector<int> improvingTR;
      for (size_t w = 0; w < preimagesTR.size(); w++) {
      	bool commonTR = 0;
        for (size_t x = 0; x < preimagesNoImprovement.size(); x++) {
	  if (preimagesTR[w] == preimagesNoImprovement[x]) {
	    commonTR = 1;
	  } 
	}
	if (commonTR == 0) {
	  improvingTR.push_back(preimagesTR[w]);
	} 	
      }
      if (improvingTR.size() == 0) {
	if (!alreadyCreatedPred) {
	  heuristicValueBuckets[i].erase(heuristicValueBuckets[i].begin()+j);
	  if (j >= 1) { j--;}
	  else {j = 0;}
	}
      }*/
    }
    //cout << "AFTER PRUNING: states = "<< heuristicValueBuckets[i].size() << endl;
    i++;
    if(heuristicValueBuckets[i].size() == 0) {break;}
  } while (i <= heuristicValueBuckets.size()); 
  /*
  if (debug == 1) {
    for (int h = 0; h < heuristicValueBuckets.size(); h++) {
      for (int e = 0; e < heuristicValueBuckets[h].size(); e++) {
        string fileGV = "actualState" + to_string(int(h)) + "_" + to_string(int(e)) + ".gv";
        sV->bdd_to_dot(heuristicValueBuckets[h][e], fileGV);
      }
    }
  } 
  */
}

int SymbolicPatternDatabase::get_value(const State &state) const {
  BDD stateBDD = sV->oneBDD();
  int hValue = -1;
  for (size_t w = 0; w < pattern.size(); w++) {
    int var_id = state[pattern[w]].get_variable().get_id();
    int val = state[pattern[w]].get_value();
    stateBDD *= sV->preBDD(var_id, val);
  }
  for (int h = 0; h < heuristicValueBuckets.size(); h++) {
    vector<BDD> bucket = heuristicValueBuckets[h];
    bool found = 0;
    for (size_t s = 0; s < bucket.size(); s++) {
      if ((bucket[s] * stateBDD) == stateBDD) {
        found = 1;
        break;	
      }
    }
    if (found) return h;
  }
}

}
