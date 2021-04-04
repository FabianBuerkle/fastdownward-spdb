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
    cout << "SymbolicPatternDatabase construction time: " << timer << endl;
}

void SymbolicPatternDatabase::create_spdb(const TaskProxy &task_proxy,
                                          const vector<int> &operator_costs) {
BDD one = sV->oneBDD();
  BDD zero = sV->zeroBDD();
  BDD cube = one;
  bool abstract = 0;
  bool debug = 0;  
  VariablesProxy variables = task_proxy.get_variables();
  varEval.resize(variables.size());
  for (auto var : variables) {
    for (int i = 0; i < var.get_domain_size(); i++) {
      BDD varVal = sV->preBDD(var.get_id(), i);
      varEval[var.get_id()].push_back(varVal);
    }
  }
  
  if (variables.size() > pattern.size()) {
    abstract = 1;
    for (auto var : variables) {
      auto it = find(pattern.begin(), pattern.end(), var.get_id());
      if (it == pattern.end()) {
        for(int index : sV->vars_index_pre(var.get_id())) {
          cube *= sV->bddVar(index);
        }
      }
    }
  }
  // used for effective storing of the TR for operators of same cost.
  std::vector<TransitionRelation *> mergedTR;
  for (OperatorProxy op : task_proxy.get_operators()) {
    int op_cost;
    if (operator_costs.empty()) {
      op_cost = op.get_cost();
    } else {
      op_cost = operator_costs[op.get_id()];
    }
    OperatorID opID(op.get_id());
    TransitionRelation *t = new TransitionRelation(sV, opID, op_cost);
    t->init();
    if (mergedTR.size() < op_cost) {
      mergedTR.resize(op_cost + 1);
      mergedTR[op_cost] = t;
    } else {
      mergedTR[op_cost]->merge(*t, numeric_limits<int>::max());
    }
  }

  State initialState = task_proxy.get_initial_state();
  BDD initBDD = one;
  for (size_t v = 0; v < pattern.size(); v++) {
    int var_id = initialState[pattern[v]].get_variable().get_id();
    int val = initialState[pattern[v]].get_value();
    initBDD *= varEval[var_id][val];
  }
  initial = initBDD;

  BDD goals = one;
  int varCount = 0;

  for (FactProxy goal : task_proxy.get_goals()) {
    int var_id = goal.get_variable().get_id();
    int val = goal.get_value();
    auto it = find(pattern.begin(), pattern.end(), var_id);    
    if (it != pattern.end()) {
      goals *= varEval[var_id][val];
      varCount++;
    }
  }
  if (debug) {
    sV->bdd_to_dot(initial, "initialState.gv");
    sV->bdd_to_dot(goals, "goalState.gv");
  }
  bool allGoal = 0;
  if (varCount == pattern.size()) {
    allGoal = 1;
  }

  int i = 0;
  BDD actState = goals;
  BDD vis = goals;
  closed.emplace_back(goals);
  while (i < closed.size()){
//    cout << "i = " << i << endl;
    for (int a = 0; a < mergedTR.size(); a++) {
      if (mergedTR[a] == 0) { continue; }
      BDD regression = mergedTR[a]->preimage(actState);
      BDD abs_regression = regression.ExistAbstract(cube, 0);
      regression = abs_regression;
      if (regression == zero) {continue;}
      if (closed.size() <= i + a) {
        closed.resize(i + a + 1, zero);
        closed[i + a] = regression * !vis;
      } else {
        closed[i + a] |= regression;
      }
      closed[i + a] *= !vis;
    }
    i++;
    if (i >= closed.size()) {break;}
    //if ((closed[i] *= !vis) == zero) {closed.resize(i); break;}
    closed[i] *= !vis; 
    actState = closed[i];
    vis |= actState;
  }
  ADD heuristicValue = zero.Add();
  heuristic = zero.Add();
  for (int i = 0; i < closed.size(); i++) {
    ADD value = sV->get_manager()->constant(i);
    heuristicValue = (closed[i].Add() * value);    
    heuristic += heuristicValue;
  }
}

int SymbolicPatternDatabase::get_value(const State &state) const {
  BDD stateBDD = sV->oneBDD();
  for (size_t w = 0; w < pattern.size(); w++) {
    int var_id = state[pattern[w]].get_variable().get_id();
    int val = state[pattern[w]].get_value();
    BDD st = sV->preBDD(var_id, val);
    stateBDD *= st;
  }
  return Cudd_V((stateBDD.Add() * heuristic).FindMax().getNode());
}

}
