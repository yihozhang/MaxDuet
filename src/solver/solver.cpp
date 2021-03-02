#include "solver.h"

#include <iostream>
#include <cmath>
#include <config.h>
#include <glog/logging.h>

namespace {
    std::string encodeStateValue(const StateValue& oup) {
        if (oup.size() == 0) return "{}";
        std::string result = "{";
        for (auto& data_list: oup) {
            result += util::dataList2String(data_list) + ",";
        }
        result[result.length() - 1] = '}';
        return result;
    }

    ParamInfo* example2ParamInfo(Example* example) {
        return new ParamInfo(example->inp);
    }

    std::string encodeFeature(const int& state, const StateValue& oup) {
        return std::to_string(state) + encodeStateValue(oup);
    }
}

double SynthesisTask::calculateProbability(int state, Program* program) {
    double result = 0.0;
    MinimalContextGraph::Edge* current_edge = nullptr;
    auto& node = graph->minimal_context_list[state];
    for (auto* edge: graph->minimal_context_list[state].edge_list) {
        if (edge->rule->semantics->name == program->semantics->name) {
            assert(current_edge == nullptr);
            current_edge = edge;
        }
    }
    assert(current_edge != nullptr);
    result += current_edge->w;
    assert(current_edge->v.size() == program->sub_list.size());
    for (int i = 0; i < current_edge->v.size(); ++i) {
        result += calculateProbability(current_edge->v[i], program->sub_list[i]);
    }
    return result;
}

void SynthesisTask::verifyResult(int start_state, VSANode *result) {
    ContextMaintainer* maintainer = graph->maintainer;
    maintainer->partial_program = new Program(result->best_program);
    PathInfo path = {};
    double probability = calculateProbability(start_state, result->best_program);
    assert(std::fabs(probability - result->p) < 1e-6);
    maintainer->clear();
}

void SynthesisTask::addNewExample(Example *example) {
    example_list.push_back(example);
    param_info_list.push_back(example2ParamInfo(example));
    single_node_map.emplace_back();
}

Program* SynthesisTask::getBestProgramWithoutOup(int state) {
    auto graph_node = graph->minimal_context_list[state];
    MinimalContextGraph::Edge* best_edge = nullptr;
    double best_cost = -1e100;
    for (auto* edge: graph_node.edge_list) {
        double current_w = edge->w;
        for (int next_node: edge->v) {
            current_w += graph->minimal_context_list[next_node].upper_bound;
        }
        if (current_w > best_cost) {
            best_cost = current_w;
            best_edge = edge;
        }
    }
    std::vector<Program*> sub_program;
    for (int next_node: best_edge->v) {
        sub_program.push_back(getBestProgramWithoutOup(next_node));
    }
    return new Program(sub_program, best_edge->rule->semantics);
}

void SynthesisTask::buildEdge(VSANode *node, int example_id) {
    node->is_build_edge = true;
    if (example_id <= 0) {
        auto& graph_node = graph->minimal_context_list[node->state];
        for (auto* graph_edge: graph_node.edge_list) {
            GlobalInfo* info = nullptr;
            if (global::spec_type == S_PBE) {
                global::string_info->setInp(example_list[-example_id]->inp);
                info = global::string_info;
            } else info = param_info_list[-example_id];
            auto result = graph_edge->rule->semantics->witnessFunction(node->value[0], info);
#ifdef DEBUG
            checkWitness(graph_edge->rule->semantics, result, node->value[0], info);
#endif
            for (auto& result_term: result) {
                std::vector<VSANode*> sub_node_list;
#ifdef DEBUG
                assert(result_term.size() == graph_edge->rule->param_list.size());
#endif
                std::vector<VSANode*> sub_node;
                for (int i = 0; i < result_term.size(); ++i) {
                    sub_node.push_back(initNode(graph_edge->v[i], {result_term[i]}, example_id));
                }
                node->edge_list.push_back(new VSAEdge(sub_node, graph_edge->rule->semantics, graph_edge->w));
            }
        }
    } else {
        VSANode *l = node->l, *r = node->r;
        if (!l->is_build_edge) buildEdge(l, example_id - 1);
        if (!r->is_build_edge) buildEdge(r, -example_id);
        std::unordered_map<std::string, std::pair<std::vector<VSAEdge*>, std::vector<VSAEdge*>>> edge_info;
        for (auto* edge: l->edge_list) {
            edge_info[edge->semantics->name].first.push_back(edge);
        }
        for (auto* edge: r->edge_list) {
            edge_info[edge->semantics->name].second.push_back(edge);
        }
        for (auto info: edge_info) {
            // for all instantiation of the production rule valid for ex 1..n-1
            for (auto* l_edge: info.second.first) {
                // for all instantiation of the production rule valid for ex n
                for (auto* r_edge: info.second.second) {
                    std::vector<VSANode*> v;
#ifdef DEBUG
                    assert(l_edge->v.size() == r_edge->v.size());
#endif
                    // for each argument of this instantiation, add the example from the right
                    for (int i = 0; i < l_edge->v.size(); ++i) {
#ifdef DEBUG
                        assert(l_edge->v[i]->state == r_edge->v[i]->state);
#endif
                        StateValue value = l_edge->v[i]->value;
                        value.push_back(r_edge->v[i]->value[0]);
                        v.push_back(initNode(l_edge->v[i]->state, value, example_id));
                    }
                    bool is_invalid = false;
                    for (auto* sub_node: v) {
                        if (sub_node == node) {
                            is_invalid = true;
                            break;
                        }
                    }
                    if (!is_invalid) {
                        node->edge_list.push_back(new VSAEdge(v, l_edge->semantics, l_edge->rule_w));
                    }
                }
            }
        }
    }
}

void VSAEdge::print() {
    std::cout << "Edge " << semantics->name << " " << rule_w << " " << updateW() << std::endl;
    for (auto* node: v) std::cout << encodeFeature(node->state, node->value) << " "; std::cerr << std::endl;
}

void VSANode::print() {
    std::cout << "Node " << encodeFeature(state, value) << std::endl;
    // for (auto* edge: edge_list) edge->print();
}

#define TRIVIAL_BOUND(node) (graph->minimal_context_list[node->state].upper_bound)

bool SynthesisTask::getBestProgramWithOup(VSANode* node, int example_id, double limit) {
    static int ts = 0;
    // std::cout << "visit " << encodeFeature(node->state, node->value) << std::endl;
    // if (enum_node_map[node->state].count(encodeFeature(node->state, node->value))) {
    //     std::cout << "HIT" << std::endl;
    // }
    if (node->best_program != nullptr) return true;
    if (node->p < limit) return false;
    if (node->l != nullptr) {
        if (!getBestProgramWithOup(node->l, example_id - 1, limit) || !getBestProgramWithOup(node->r, -example_id, limit)) {
            node->updateP();
            return false;
        }
        auto *candidate = node->l->best_program;
        if (util::checkInOupList(candidate->run(example_list[example_id]->inp), node->value[example_id])) {
            node->best_program = candidate;
            node->p = node->l->p;
            return true;
        }
    }
    if (!node->is_build_edge) {
        buildEdge(node, example_id);
    }
    if (node->updateP() < limit) return false;
    std::vector<VSAEdge*> possible_edge;
    // scan through possible edges
    double _limit = limit;
    for (auto* edge: node->edge_list) {
        if (edge->w >= limit) {
            bool is_finished = true;
            for (auto* sub_node: edge->v) {
                if (sub_node->best_program == nullptr) {
                    is_finished = false;
                    break;
                }
            }
            if (is_finished) {
                limit = std::max(edge->w, limit);
            } else {
                possible_edge.push_back(edge);
            }
        }
    }
    int b = ++ts;
    while (true) {
        VSAEdge* best_edge = nullptr;
        // try to find the best edge among all possible edges according to a creteria
        double best_remain = 0;
        for (auto *edge: possible_edge) {
            if (edge->w <= limit) continue;
            int unfinished_num = 0;
            for (auto *sub_node: edge->v) {
                if (sub_node->best_program == nullptr) ++unfinished_num;
            }
            if (unfinished_num == 0) continue;
            if ((limit - edge->w) / unfinished_num < best_remain) {
                best_remain = (limit - edge->w) / unfinished_num;
                best_edge = edge;
            }
        }
        if (best_edge == nullptr) break;

        // the p value of each node from the best edge
        std::vector<double> remain_list;
        for (auto* sub_node: best_edge->v) {
            remain_list.push_back(sub_node->p);
        }
        for (int i = 0; i < remain_list.size(); ++i) {
            VSANode* sub_node = best_edge->v[i];
            // if successfully find programs for a  node
            if (sub_node->best_program == nullptr && getBestProgramWithOup(sub_node, example_id,remain_list[i] + best_remain)) {
                break;
            }
        }
        // shrink possible edges and update limit
        int now = 0;
        node->p = limit;
        for (auto* edge: possible_edge) {
            if (edge->updateW() < limit) continue;
            bool is_finished = true;
            for (auto* sub_node: edge->v) {
                if (sub_node->best_program == nullptr) {
                    is_finished = false;
                    break;
                }
            }
            if (is_finished) {
                limit = std::max(limit, edge->w);
            } else {
                possible_edge[now++] = edge;
            }
            node->p = std::max(node->p, edge->updateW());
        }
        if (node->l) node->p = std::min(node->p, std::min(node->l->p, node->r->p));
        possible_edge.resize(now);
    }
    node->updateP();
    VSAEdge* best_edge = nullptr;
    for (auto* edge: node->edge_list) {
        if (fabs(edge->w - limit) > 1e-8) continue;
        bool is_finished = true;
        for (auto* node: edge->v) {
            if (node->best_program == nullptr) {
                is_finished = false;
                break;
            }
        }
        if (is_finished) {best_edge = edge; break;}
    }
#ifdef DEBUG
    if (fabs(limit - _limit) > 1e-8) {
        if (best_edge == nullptr) {
            std::cout << limit << " " << _limit << std::endl;
            node->print();
        }
        assert(best_edge);
    }
#endif
    if (best_edge != nullptr) {
        std::vector<Program*> sub_program;
        for (auto* sub_node: best_edge->v) {
            sub_program.push_back(new Program(sub_node->best_program));
        }
        node->best_program = new Program(sub_program, best_edge->semantics);

        verifyExampleResult(node, example_id);
        return true;
    }
#ifdef DEBUG
    //std::cout << node->p << " " << _limit << " " << limit << std::endl;
    // node->print();
    assert(node->p <= _limit);
#endif
    return false;
}

void SynthesisTask::verifyExampleResult(VSANode *node, int example_id) {
    int l = 0, r = 0;
    if (example_id <= 0) {
        l = r = -example_id;
    } else {
        r = example_id;
    }
    for (int i = l; i <= r; ++i) {
        auto oup = node->best_program->run(example_list[i]->inp);
        if (!util::checkInOupList(oup, node->value[i - l])) {
            std::cout << graph->minimal_context_list[node->state].minimal_context->encodeContext() << " " << graph->minimal_context_list[node->state].symbol->name << " " << encodeFeature(node->state, node->value) << std::endl;
            node->best_program->print();
            std::cout << util::dataList2String(node->value[i - l]) << " " << example_list[i]->toString() << std::endl;
            std::cout << oup.toString() << " " << example_id << std::endl;

            assert(0);
        }
    }
}

VSANode* SynthesisTask::initNode(int state, const StateValue& value, int example_id) {
    std::string feature = encodeFeature(state, value);
    auto& cache = example_id > 0 ? combined_node_map : single_node_map[-example_id];
    auto*& result = cache[feature];
    if (result != nullptr) return result;
    auto& graph_node = graph->minimal_context_list[state];
    if (example_id <= 0) {
        return result = new VSANode(state, value, graph_node.upper_bound);
    } else {
        auto* r = initNode(state, {value[value.size() - 1]}, -example_id);
        auto _value = value; _value.pop_back();
        auto* l = initNode(state, _value, example_id - 1);
        return result = new VSANode(state, value, l, r, std::min(l->p, r->p));
    }
}

Program* SynthesisTask::synthesisProgramFromExample() {
    StateValue value;
    for (auto* example: example_list) {
        value.push_back({example->oup});
    }
    VSANode* node = initNode(0, value, example_list.size() - 1);
    int enum_prog_size = 1;
    for (int i = 1; i <= 3; i++) enumeratePrograms(example_list.size() - 1, enum_prog_size++);
    // enumeratePrograms(example_list.size() - 1, enum_prog_size++);
    printEnumSize();
    // {
    //     const auto& maps = enum_node_map;
    //     std::cout << "enum1" << std::endl;
    //     for (int i = 0; i < maps.size(); i++) {
    //         std::cout << "state: " << i << std::endl;
    //         for (auto& entry: maps[i]) {
    //             std::cout << entry.first << " " << entry.second->state << " ";
    //             entry.second->best_program->print();
    //             // std::cout <<  " ";
    //             // entry.second->print();
    //             // std::cout << std::endl;
    //         }
    //     }
    // }
    while (!getBestProgramWithOup(node, example_list.size() - 1, value_limit)) {
        // enumeratePrograms(example_list.size() - 1, enum_prog_size++);
        std::cerr << "start enumerating" << std::endl;
        value_limit -= 3;
        if (value_limit < -1000) {
            LOG(INFO) << "No valid program found" << std::endl;
            exit(0);
        }
        LOG(INFO) << "Relaxed the global lowerbound to " << value_limit << std::endl;
    }
    return node->best_program;
}

Program * SynthesisTask::solve() {
#ifdef DEBUG
    std::cout << "Start synthesis" << std::endl;
#endif
    addNewExample(spec->example_space[0]);
    LOG(INFO) << "New example: " << spec->example_space[0]->toString() << std::endl;
    while (1) {
        Program* result = synthesisProgramFromExample();
        LOG(INFO) << "Program: " << result->toString() << "; Log-prob: " << calculateProbability(0, result) << std::endl;
        for (int i = 0; i < example_list.size(); ++i) {
#ifdef DEBUG
            std::cout << util::dataList2String(example_list[i]->inp) << " " << example_list[i]->oup.toString() << " " << result->run(example_list[i]->inp).toString() << std::endl;
#endif
            assert(result->run(example_list[i]->inp) == example_list[i]->oup);
        }
        Example* counter_example = nullptr;
        if (spec->verify(result, counter_example)) {
            return result;
        }
#ifdef DEBUG
        assert(counter_example != nullptr);
#endif
        addNewExample(counter_example);
        LOG(INFO) << "New example: " << counter_example->toString() << std::endl;
    }
}

void SynthesisTask::enumerateNodes(
    int pos, const std::vector<int>& v, std::vector<VSANode*>& curr, 
    std::vector<std::vector<VSANode*>>& ret,
    int prog_size
) {

    if (pos == v.size()) {
        ret.push_back(std::vector<VSANode*>(curr));
    } else {
        int state = v[pos];
        for (int curr_size = 1; curr_size <= prog_size - (((int) v.size()) - pos - 1); curr_size++) {
            // std::cout << curr_size << std::endl;
            // for (const auto& entry: enum_node_map[state][curr_size]) {
            for (auto node: global::string_info->node_pool[state][curr_size]) {
                curr[pos] = node;
                enumerateNodes(pos + 1, v, curr, ret, prog_size - curr_size);
            }
        }
    }
}

void SynthesisTask::enumeratePrograms(int example_id, int prog_size) {
    auto& enum_node_map = global::string_info->enum_node_map;
    auto& node_pool = global::string_info->node_pool;
    std::vector<std::unordered_map<std::string, VSANode*>> delta_enum_node_map(enum_node_map.size());
    for (int i = 0; i < graph->minimal_context_list.size(); i++) {
        // add a new entry for size=prog_size to the pool;
        node_pool[i].emplace_back();
        const auto& node = graph->minimal_context_list[i];
        for (const auto& edge: node.edge_list) {
            auto& v = edge->v;
            std::vector<std::vector<VSANode*>> all_nodes;
            auto _unused = std::vector<VSANode*>(v.size());
            // minus 1 to account for the size of op
            enumerateNodes(0, v, _unused, all_nodes, prog_size - 1);
            // std::cerr << all_nodes.size() << std::endl;
            for (auto subnodes: all_nodes) {
                Semantics* semantics = edge->rule->semantics;
                std::vector<Program*> subprograms(subnodes.size());
                for (int j = 0; j < subnodes.size(); j++) {
                    subprograms[j] = subnodes[j]->best_program;
                }
                Program* program = new Program(subprograms, semantics);

                StateValue sv;
                for (int j = 0; j <= example_id; j++) {
                    Data oup = program->run(example_list[j]->inp);
                    sv.push_back({oup});
                }
                std::string feature = encodeFeature(i, sv);
                if (!combined_node_map.count(feature)) {
                    combined_node_map[feature] = new VSANode(i, sv, node.upper_bound);
                }
                VSANode* vsanode = combined_node_map[feature];
                // otherwise there's already an *optimal* program
                if (vsanode->best_program == nullptr) {
                    vsanode->best_program = program;
                    vsanode->edge_list.clear();
                    vsanode->edge_list.push_back(new VSAEdge(subnodes, semantics, edge->w));
                    vsanode->is_build_edge = true;
                    vsanode->updateP();
                }
                delta_enum_node_map[i][feature] = vsanode;
                if (!enum_node_map[i].count(feature)) {
                    node_pool[i][prog_size].push_back(vsanode);
                }
            }
            // std::cerr << std::endl;
        }
    }

    for (int i = 0; i < delta_enum_node_map.size(); i++) {
        enum_node_map[i].insert(delta_enum_node_map[i].begin(), delta_enum_node_map[i].end());
    }

    int tot = 0;
    for (auto& nodes: node_pool) {
        for (auto& sized_nodes: nodes) {
            tot += sized_nodes.size();
        }
    }
    LOG(INFO) << "enumerated size = " << tot << " for size " << prog_size << std::endl;
}

SynthesisTask::SynthesisTask(MinimalContextGraph* _graph, Specification* _spec): graph(_graph), spec(_spec), value_limit(-5) {
    global::string_info->enum_node_map.resize(graph->minimal_context_list.size());
    global::string_info->node_pool.resize(graph->minimal_context_list.size());
    for (int i = 0; i < global::string_info->node_pool.size(); i++) {
        global::string_info->node_pool[i].emplace_back();
    }
}


void SynthesisTask::printEnumSize() {
    int tot = 0;
    for (auto& map: global::string_info->enum_node_map) {
        tot += map.size();
    }
    std::cout << "enum size: "  << tot << std::endl;
}

double VSAEdge::updateW() {
    w = rule_w;
    for (auto* sub_node: v) {
        w += sub_node->p;
    }
    return w;
}
