#include "symbolic_pdb_heuristic.h"
#include "../symbolic/sym_variables.h"

#include "pattern_generator.h"

#include "../option_parser.h"
#include "../plugin.h"
#include "../task_proxy.h"

#include <limits>
#include <memory>

using namespace std;
using namespace symbolic;

namespace pdbs {
SymbolicPatternDatabase symbolic_pdb_options_creator(const shared_ptr<AbstractTask> &task,
                                     const Options &opts) {
	shared_ptr<PatternGenerator> pattern_generator =
	       	opts.get<shared_ptr<PatternGenerator>>("pattern");
	Pattern pattern = pattern_generator->generate(task);
    	TaskProxy task_proxy(*task);
   	SymVariables *sv = new SymVariables(opts);
   	sv->init();
   	return SymbolicPatternDatabase(sv, task_proxy, pattern, true);
}

SymbolicPDBHeuristic::SymbolicPDBHeuristic(const Options &opts)
    : Heuristic(opts), spdb(symbolic_pdb_options_creator(task, opts)) {
}

int SymbolicPDBHeuristic::compute_heuristic(const GlobalState &global_state) {
    State state = convert_global_state(global_state);
    return compute_heuristic(state);
}

int SymbolicPDBHeuristic::compute_heuristic(const State &state) const {
    int h = spdb.get_value(state);
    if (h == numeric_limits<int>::max())
        return DEAD_END;
    return h;
}

static shared_ptr<Heuristic> _parse(OptionParser &parser) {
    parser.document_synopsis("Symbolic Pattern database heuristic", "TODO");
    parser.document_language_support("action costs", "supported");
    parser.document_language_support("conditional effects", "not supported");
    parser.document_language_support("axioms", "not supported");
    parser.document_property("admissible", "yes");
    parser.document_property("consistent", "yes");
    parser.document_property("safe", "yes");
    parser.document_property("preferred operators", "no");

    parser.add_option<shared_ptr<PatternGenerator>>(
        "pattern",
        "pattern generation method",
        "greedy()");
    Heuristic::add_options_to_parser(parser);

    Options opts = parser.parse();
    if (parser.dry_run())
        return nullptr;

    return make_shared<SymbolicPDBHeuristic>(opts);
}

static Plugin<Evaluator> _plugin("symbolic_pdb", _parse, "heuristics_pdb");
}
