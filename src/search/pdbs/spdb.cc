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

SPDB::SPDB(SymVariables *sVars, 
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

void SPDB::create_spdb(const TaskProxy &task_proxy,
                                          const vector<int> &operator_costs) {
  BDD one = sV->oneBDD();
  BDD zero = sV->zeroBDD();
  BDD cube = one;
  bool abstract = 0;
  bool debug = 0;  
  VariablesProxy variables = task_proxy.get_variables();
  initialHVal = numeric_limits<int>::max();

  vector<BDD> varEval;
  for (auto var : variables) {  
    ADD varValue = zero.Add();    
    for (int v = 0; v < var.get_domain_size(); v++) {
      BDD fact = sV->get_axiom_compiliation()->get_primary_representation(var.get_id(), v);
      ADD value = sV->get_manager()->constant(v);
      varValue += (fact.Add() * value);
      //cout << "fact: " << fact << endl;
    }
///*  
    double maxVarVal = Cudd_V(varValue.FindMax().getNode());
    double minVarVal = Cudd_V(varValue.FindMin().getNode());
//*/
    for (int val = 0; val <= maxVarVal; val++) {
      BDD showing = varValue.BddInterval(val, val);
      //cout << "vars: " << showing << endl;
      varEval.emplace_back(showing);
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
      } else {
        //cout << " PATTERN VAR ";
      }
      //cout << endl;
    }
    //cout <<"ABSTRACTION_PATTERN: " << cube << endl;    
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
//  ADD add_utility = zero.Add();
  for (FactProxy goal : task_proxy.get_goals()) {
    int var_id = goal.get_variable().get_id();
    int val = goal.get_value();
    auto it = find(pattern.begin(), pattern.end(), var_id);    
    if (it != pattern.end()) {
      goals *= sV->preBDD(var_id, val);
    }
  }
///*
  if (debug) {
    sV->bdd_to_dot(initial, "initialState.gv");
    sV->bdd_to_dot(goals, "goalState.gv");
  }
  //cout << "INIT:" << initial << endl;
  //cout << "GOAL:" << goals << endl;
  bool allGoal = 0;
  if (varCount == pattern.size()) {
    cout << "PATTERN CONTAINS EXACTLY ALL GOAL VARS" << endl;
    allGoal = 1;
  }
//*/
  //heuristicValueBuckets.resize(1);
  //heuristicValueBuckets[0].emplace_back(goals);
  int h = 0;// Variable to take care of actual heuristic Value for Set of States
  BDD actualState = goals;
  BDD visited = goals;
  BDD explored = zero;
  closedList.emplace_back(goals);
  while (h < closedList.size()) {
    //cout << "\nh = " << h << endl;
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
      if (initial <= regressed or regressed <= initial) {
        if (initialHVal == numeric_limits<int>::max()) {
          initialHVal = h + cost;
          bestH = initialHVal;
        }
      }
      int hVal = compute_value(regressed);
      if (hVal == numeric_limits<int>::max()) {
        hVal = h + cost;
        if (closedList.size() <= hVal) {
          closedList.emplace_back(regressed);
        } else {
          closedList[hVal] |= regressed;
        }
      } else {
        if (regressed <= closedList[hVal]) {
          closedList[hVal] |= regressed;
          continue;          
        } else if (closedList[hVal] <= regressed) {
          closedList[hVal] = regressed;
        }
      }
    }
    if (debug == 1) {
      sV->bdd_to_dot(closedList[h] , "state" + to_string((int)h) + ".gv");
    }
    h++;
    if (h >= closedList.size()) {break;}
    if (closedList[h] >= initial) {
      if (initialHVal == numeric_limits<int>::max()) {      
        initialHVal = h;
        bestH = initialHVal;
      }
    }
    closedList[h] *= !visited;
    actualState = closedList[h];
    visited |= (explored | actualState);
  }
  ADD heuristicValue = zero.Add();
  heuristic = zero.Add();
  for (int i = 0; i < closedList.size(); i++) {
    ADD value = sV->get_manager()->constant(i);
    heuristicValue = (closedList[i].Add() * value);    
    heuristic += heuristicValue;
  }
  //cout << Cudd_V(heuristic.FindMin().getNode()) << "   " << Cudd_V(heuristic.FindMax().getNode()) << endl; 
}

int SPDB::get_value(const State &state) const {
  BDD stateBDD = sV->oneBDD();
  for (size_t w = 0; w < pattern.size(); w++) {
    int var_id = state[pattern[w]].get_variable().get_id();
    int val = state[pattern[w]].get_value();
    BDD st = sV->preBDD(var_id, val);
    stateBDD *= st;
  }
  //return compute_value(stateBDD);
  //cout << stateBDD << endl;
  ADD hval = (stateBDD.Add() * heuristic);
  //cout << Cudd_V(hval.FindMax().getNode()) << endl;
  return Cudd_V(hval.FindMax().getNode());
}

int SPDB::compute_value(const BDD &state) const {
  for (int h = 0; h < closedList.size(); h++) {
    if (state <= closedList[h]) { return h; }
    //if (state >= closedList[h]) { return h; }
  }
  return numeric_limits<int>::max();
}

}
