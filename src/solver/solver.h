#ifndef L2S_SOLVER_H
#define L2S_SOLVER_H

#include <iostream>
#include "context_maintainer.h"
#include "specification.h"
#include "minimal_context_graph.h"

typedef std::vector<DataList> StateValue;


struct VSANode;
struct VSAEdge {
    Semantics* semantics;
    std::vector<VSANode*> v;
    double w, rule_w;
    VSAEdge(const std::vector<VSANode*>& _v, Semantics* _semantics, double _rule_w): semantics(_semantics), rule_w(_rule_w), v(_v) {
        updateW();
    }
    double updateW();
    void print();
};

struct VSANode {
    std::vector<VSAEdge*> edge_list;
    std::vector<Program*> edge_supporters;
    int state;
    StateValue value;
    Program* best_program;
    VSANode *l, *r;
    double p;
    bool is_build_edge;
    VSANode(int _state, const StateValue& _value, double _p):
        state(_state), value(_value), best_program(nullptr), p(_p), is_build_edge(false), l(nullptr), r(nullptr) {}
    VSANode(int _state, const StateValue& _value, VSANode* _l, VSANode* _r, double _p):
            state(_state), value(_value), best_program(nullptr), p(_p), is_build_edge(false), l(_l), r(_r) {}
    double updateP() {
        if (!is_build_edge) {
            return p = std::min(l->p, r->p);
        }
        p = -1e100;
        for (auto *edge: edge_list) p = std::max(p, edge->updateW());
        if (l) {
            p = std::min(std::min(l->p, r->p), p);
        }
        return p;
    }
    void print();
};

// The main solver. It does not use any domain knowledge, and thus this part remains unchanged for different domains.
class SynthesisTask {

private:
    std::vector<Example*> example_list;
    std::vector<ParamInfo*> param_info_list;
    std::unordered_map<std::string, VSANode*> combined_node_map;
    std::vector<std::unordered_map<std::string, VSANode*>> single_node_map;

    Program* synthesisProgramFromExample();
    Program* getBestProgramWithoutOup(int state);
    void verifyResult(int start_state, VSANode *result);
    void verifyExampleResult(VSANode* node, int example_id);
    bool getBestProgramWithOup(VSANode* node, int example_id, double limit);
    VSANode* initNode(int state, const StateValue& value, int example_id);
    void buildEdge(VSANode* node, int example_id);
public:
    void addNewExample(Example* example);
    void enumeratePrograms(int example_id, int prog_size);
    void enumerateNodes(int pos, const std::vector<int>& v, std::vector<VSANode*>& curr, std::vector<std::vector<VSANode*>>& ret, int prog_size);
    void printEnumSize();
    void printEnums();
    void clearEnumPool();
public:
    MinimalContextGraph* graph;
    Specification* spec;
    double value_limit;

    double calculateProbability(int state, Program* program);
    SynthesisTask(MinimalContextGraph* _graph, Specification* _spec);

    Program* solve();
};
#endif //L2S_SOLVER_H
