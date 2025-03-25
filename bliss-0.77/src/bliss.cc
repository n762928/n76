#include <cstdlib>
#include <cstdio>
#include <cstring>
#include <cassert>
#include "defs.hh"
#include "graph.hh"
#include "timer.hh"
#include "utils.hh"


#include <iostream>
#include <fstream>
#include <string>
#include <stdio.h>
#include <dirent.h>
#include <unordered_set>
#include <vector>
#include <algorithm>
#include <sstream>
#include <set>
#include <tuple>
#include <sys/stat.h>
#include <sys/types.h>
#include "graph.hh"
#include "defs.hh"
#include "timer.hh"
#include "utils.hh"
#include "digraph.hh"

const std::string DIRECTORY_PATH    = "/tmp/gql/";
const std::string PIPE_NAME         = "my_pipe";
const std::string RESULT_PATH       = "result";
const std::string USER_RULES_PATH   = "user_rules";
const std::string SRC_PATH          = "src/";
const std::string TARGET_GRAPH_FILE = "/tmp/gql/src_graph.txt";

int src_graph_num_edges = 0;


struct equals {
  bool operator()(bliss::Graph* g1, bliss::Graph* g2) const {
    return g1->cmp(*g2) == 0;
  }
};


struct GraphHash {
    std::size_t operator()(bliss::Graph* graph) const {
        return graph->get_hash();
    }
};


struct GraphEqual {
    bool operator()(bliss::Graph* lhs, bliss::Graph* rhs) const {
        return lhs->cmp(*rhs) == 0;
    }
};


std::string read_from_pipe() {
  std::ifstream pipe((DIRECTORY_PATH + PIPE_NAME).c_str());
  if (!pipe.is_open()) {
    std::cerr << "Error opening named pipe for reading." << std::endl;
  }
  std::string line;
  std::getline(pipe, line);
  pipe.close();
  return line;
}


bliss::Graph* create_graph_from_file() {
  bliss::Graph* g = 0;
  FILE* infile = fopen(TARGET_GRAPH_FILE.c_str(), "r");
  g = bliss::Graph::read_dimacs(infile);
  return g;
}


bool graphs_equal(bliss::Graph* g1, bliss::Graph* g2) {
  bliss::Stats stats;
  bliss::Graph* g1_canonical = g1->permute(g1->canonical_form(stats));
  bliss::Graph* g2_canonical = g2->permute(g2->canonical_form(stats));
  if (g1_canonical->cmp(*g2_canonical) == 0) {
    return true;
  }
  else {
    return false;
  }  
}

void send_done_signal() {
  std::string result = "done";
  std::ofstream pipe((DIRECTORY_PATH + PIPE_NAME).c_str());
  if (!pipe.is_open()) {
    std::cerr << "Error opening named pipe for reading." << std::endl;
  }
  pipe << result << std::endl;
  pipe.close();
}

void generate_combinations(const std::vector<std::tuple<int, int>>& elements, size_t n, std::vector<std::tuple<int, int>>& current, size_t index, std::vector<std::vector<std::tuple<int, int>>>& result) {
  if (current.size() == n) {
    result.push_back(current);
    return;
  }

  for (size_t i = index; i < elements.size(); ++i) {
    current.push_back(elements[i]);
    generate_combinations(elements, n, current, i + 1, result);
    current.pop_back();
  }
}

std::set<std::tuple<int, int>> get_edges(std::string target_graph_file) {
  std::ifstream inputFile(target_graph_file);
  std::set<std::tuple<int, int>> edge_set;
  std::string line;
  while (std::getline(inputFile, line)) {
    if (line[0] != 'e')
      continue;

    std::istringstream iss(line);
    char edgeType;
    int vertex1, vertex2;
    iss >> edgeType >> vertex1 >> vertex2;
    edge_set.emplace(vertex1, vertex2);
  }
  return edge_set;
}

std::set<std::tuple<int, int>> get_disconnected_edges() {
  std::ifstream inputFile(TARGET_GRAPH_FILE);
  std::string line;
  int num_nodes;
  if (std::getline(inputFile, line)) {
    std::istringstream iss(line);
    std::string p, edge;
    iss >> p >> edge >> num_nodes >> src_graph_num_edges;
  }   
  std::set<std::tuple<int, int>> edge_set = get_edges(TARGET_GRAPH_FILE);
  std::set<std::tuple<int, int>> disconnected_edge_set;
  for (int i=1; i<=num_nodes; i++) 
    for (int j=i+1; j<=num_nodes; j++) 
      if (edge_set.find({i, j}) == edge_set.end() && edge_set.find({j, i}) == edge_set.end()) 
        if (disconnected_edge_set.find({j, i}) == disconnected_edge_set.end()) 
          disconnected_edge_set.emplace(i, j);
  return disconnected_edge_set;
}

// void generate_new_graph(bliss::Graph* src_graph, std::vector<bliss::Graph*>& graphs, const std::vector<std::vector<std::tuple<int, int>>>& result) {
//   bliss::Stats stats;
//   for (int i=0; i<result.size(); i++) {
//     bliss::Graph* new_graph = src_graph->copy();
//     for (const auto& edge : result[i]) {
//       new_graph->add_edge(std::get<0>(edge) - 1, std::get<1>(edge) - 1);
//     }
//     bliss::Graph* new_graph_canonical = new_graph->permute(new_graph->canonical_form(stats));
//     graphs.push_back(new_graph_canonical);
//   }
// }


void generate_new_graph(bliss::Graph* src_graph, std::vector<bliss::Graph*>& graphs, const std::vector<std::vector<std::tuple<int, int>>>& result) {
  bliss::Stats stats;
  for (int i=0; i<result.size(); i++) {
    bliss::Graph* new_graph = src_graph->copy();
    for (const auto& edge : result[i]) {
      new_graph->add_edge(std::get<0>(edge) - 1, std::get<1>(edge) - 1);
    }
    bliss::Graph* new_graph_canonical = new_graph->permute(new_graph->canonical_form(stats));
    graphs.push_back(new_graph_canonical);
  }
}

std::vector<bliss::Graph*> generate_new_rules(bliss::Graph* src_graph, std::set<std::tuple<int, int>> disconnected_edges_set) {
  std::vector<bliss::Graph*> graphs;
  std::vector<std::tuple<int, int>> disconnected_edges(disconnected_edges_set.begin(), disconnected_edges_set.end());
  for (int i=1; i<=disconnected_edges.size(); i++) {
    std::vector<std::tuple<int, int>> currentCombination;
    std::vector<std::vector<std::tuple<int, int>>> result;
    generate_combinations(disconnected_edges, i, currentCombination, 0, result);
    generate_new_graph(src_graph, graphs, result);
  }
  return graphs;
}

void write_graph_to_file(std::string path, bliss::Graph* target_graph) {
  FILE* out = fopen(path.c_str(), "w");
  target_graph->write_dimacs(out);
  fclose(out);
}

void write_graph_with_permutation_to_file(std::string path, bliss::Graph* target_graph) {
  FILE* out = fopen(path.c_str(), "w");
  target_graph->write_dimacs(out);
  bliss::Stats stats;
  const unsigned int* cl = target_graph->canonical_form(stats);
  unsigned int num_vertices = target_graph->get_nof_vertices();
  for (unsigned int i=0; i<num_vertices; i++) {
    std::string permutation = "perm " + std::to_string(cl[i]) + " " + std::to_string(i) + "\n";
    fprintf(out, permutation.c_str());
  }
  fclose(out);
}


void find_unique_graphs(std::vector<bliss::Graph*> graphs, bliss::Graph* src_graph) {
  std::string directoryPath = DIRECTORY_PATH + RESULT_PATH;
  mkdir(directoryPath.c_str(), 0777);
  bliss::Stats stats;
  for (int i=0; i<graphs.size(); i++) {
    bool unique = true;
    for (int j=i-1; j>=0; j--) {
      if (graphs[i]->cmp(*graphs[j]) == 0) {
        unique = false;
        break;
      }
    }
    if (unique) {
      std::string file_path = directoryPath + "/graph" + std::to_string(i) + ".txt";
      write_graph_to_file(file_path, graphs[i]);
    }
  }
  std::string file_path = directoryPath + "/graph" + std::to_string(graphs.size()) + ".txt";
  write_graph_to_file(file_path, src_graph);
}

void find_coefficient(bliss::Graph* src_graph) {
  std::string directoryPath = DIRECTORY_PATH + RESULT_PATH;
  DIR* dir;
  struct dirent* ent;

  if ((dir = opendir(directoryPath.c_str())) != NULL) {
    while ((ent = readdir(dir)) != NULL) {
      std::string filename = ent->d_name;
      if (filename == "." || filename == "..")
        continue;
      std::string path = directoryPath + "/" + filename;
      std::set<std::tuple<int, int>> edges_set = get_edges(path);
      std::vector<bliss::Graph*> graphs;
      std::vector<std::tuple<int, int>> edges(edges_set.begin(), edges_set.end());
      std::vector<std::tuple<int, int>> currentCombination;
      std::vector<std::vector<std::tuple<int, int>>> result;
      generate_combinations(edges, edges.size() - src_graph_num_edges, currentCombination, 0, result);
      int coefficient = 0;
      for (int i=0; i<result.size();i++) {
        bliss::Graph* graph = new bliss::Graph(src_graph->get_nof_vertices());
        for (const auto& edge: edges) {
          if (std::find(result[i].begin(), result[i].end(), edge) != result[i].end())
            continue;
          graph->add_edge(std::get<0>(edge) - 1, std::get<1>(edge) - 1);
        }
        if (graphs_equal(src_graph, graph))
          coefficient += 1;
      }
      std::ofstream outputFile(path.c_str(), std::ofstream::app);
      outputFile << coefficient <<std::endl;
      outputFile.close();
    } 
    closedir(dir);
  }

}

void write_to_file(std::string path, std::string content) {
  std::ofstream outFile;
  outFile.open(path);
  outFile << content;
  outFile.close();
}

std::vector<std::string> get_nodes_permutation(std::string file_name) {
  std::vector<std::string> nodes_permutation;
  bliss::Stats stats;
  bliss::Graph* g = 0;
  FILE* infile = fopen(file_name.c_str(), "r");
  g = bliss::Graph::read_dimacs(infile);
  const unsigned int* cl = g->canonical_form(stats);
  unsigned int num_vertices = g->get_nof_vertices();
  for (unsigned int i=0; i<num_vertices; i++) {
    std::string permutation = std::to_string(cl[i]) + " " + std::to_string(i);
    nodes_permutation.push_back(permutation);
  }
  return nodes_permutation;
}

void write_permutation_to_file(std::string path, std::vector<std::string> content) {
  std::ofstream outFile;
  outFile.open(path);
  for (int i=0; i<content.size(); i++)
    outFile << content[i] << std::endl;
  outFile.close();
}


void make_input_patterns_canonical(int num_input_patterns) {
  std::string path = DIRECTORY_PATH + SRC_PATH;
  for (int i=0; i<num_input_patterns; i++) {
    std::string file_name = path + std::to_string(i) + ".txt";
    std::vector<std::string> nodes_permutation = get_nodes_permutation(file_name);
    write_permutation_to_file(file_name, nodes_permutation);
  }
}


int main() {
  // bliss::Stats stats;
  // bliss::Graph* g = create_graph_from_file();
  // bliss::Graph* canonical = g->permute(g->canonical_form(stats));
  // FILE* out = fopen("/tmp/gql/can.txt", "w");
  // canonical->write_dimacs(out);
  // fclose(out);

  int num_input_patterns = stoi(read_from_pipe());
  std::string ready_signal = read_from_pipe();
  make_input_patterns_canonical(num_input_patterns);
  send_done_signal();

  std::string result_type = read_from_pipe();
  while (result_type != "done") {
    bliss::Graph* target_graph = create_graph_from_file();
    std::set<std::tuple<int, int>> disconnected_edges = get_disconnected_edges();
    std::vector<bliss::Graph*> graphs = generate_new_rules(target_graph, disconnected_edges);
    find_unique_graphs(graphs, target_graph);
    // if (result_type == "vertex_induced")
    //   find_coefficient(target_graph);
    send_done_signal();
    result_type = read_from_pipe();
  }

}