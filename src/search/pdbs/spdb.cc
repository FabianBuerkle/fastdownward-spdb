#include "spdb.h"

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

SPDB::SPDB(SymVariables *sVars, const TaskProxy &task_proxy,
           const Pattern &pattern, bool dump,
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

void SPDB::create_spdb(const TaskProxy &task_proxy,
                       const vector<int> &operator_costs) {
  BDD one = sV->oneBDD();
  BDD zero = sV->zeroBDD();
  BDD cube = one;
  bool abstract = 0;
  bool debug = 0;  
  VariablesProxy variables = task_proxy.get_variables();
  initialHVal = numeric_limits<int>::max();

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
  std::vector<TransitionRelation *> costSortedTR;
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
    costSortedTR.emplace_back(t);
  }
  State initialState = task_proxy.get_initial_state();
  BDD initBDD = one;
  for (size_t v = 0; v < pattern.size(); v++) {
    int var_id = initialState[pattern[v]].get_variable().get_id();
    int val = initialState[pattern[v]].get_value();
    initBDD *= sV->preBDD(var_id, val);
  }
  initial = initBDD;
  BDD goals = one;
  int varCount = 0;
  for (FactProxy goal : task_proxy.get_goals()) {
    int var_id = goal.get_variable().get_id();
    int val = goal.get_value();
    auto it = find(pattern.begin(), pattern.end(), var_id);    
    if (it != pattern.end()) {
      goals *= sV->preBDD(var_id, val);
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
  // Variable to take care of actual heuristic Value for Set of States
  int h = 0;  
  BDD actualState = goals;
  BDD visited = goals;
  BDD explored = zero;
  closedList.emplace_back(goals);
  while (h < closedList.size()) {
    for (size_t t = 0; t < costSortedTR.size(); t++) {
      BDD regressed = costSortedTR[t]->preimage(actualState);
      int cost = costSortedTR[t]->getCost();
      if (regressed == zero) {continue;}
      if (abstract == 1) {
        BDD abstracted = regressed.ExistAbstract(cube, 0);
        regressed = abstracted;
      }
      if (regressed *!visited == zero) {
        continue;
      }

      explored |= regressed;
      int hVal = compute_value(regressed);

      if (hVal == numeric_limits<int>::max() or (allGoal and hVal != numeric_limits<int>::max())) {
        hVal = h + cost;
        if (closedList.size() <= hVal) {
          closedList.resize(hVal + 1, zero);
          closedList[hVal] = regressed * !visited;
        } else {
          closedList[hVal] |= regressed * !visited;
        }
      } else {
        if (closedList[hVal] <= regressed) {
          closedList[hVal] = regressed * !visited;
        }
      }
    }
    if (debug == 1) {
      sV->bdd_to_dot(closedList[h] , "state" + to_string((int)h) + ".gv");
    }
    h++;
    if (h >= closedList.size()) {break;}
    actualState = closedList[h];
    visited |= (explored | actualState);
    if (debug == 1) {
      sV->bdd_to_dot(closedList[h] , "state" + to_string((int)h) + ".gv");
    }
  }
  ADD heuristicValue = zero.Add();
  heuristic = zero.Add();
  for (int i = 0; i < closedList.size(); i++) {
    ADD value = sV->get_manager()->constant(i);
    heuristicValue = (closedList[i].Add() * value);
    heuristic += heuristicValue;
  }
}

int SPDB::get_value(const State &state) const {
  BDD stateBDD = sV->oneBDD();
  for (size_t w = 0; w < pattern.size(); w++) {
    int var_id = state[pattern[w]].get_variable().get_id();
    int val = state[pattern[w]].get_value();
    BDD st = sV->preBDD(var_id, val);
    stateBDD *= st;
  }
  ADD hval = (stateBDD.Add() * heuristic);
  return Cudd_V(hval.FindMax().getNode());
}

int SPDB::compute_value(const BDD &state) const {
  for (int h = 0; h < closedList.size(); h++) {
    if (state <= closedList[h]) { return h; }
    if (closedList[h] <= state) { return h; }
  }
  return numeric_limits<int>::max();
}

}
