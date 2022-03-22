#include <chrono>
#include <iomanip>
#include <iostream>
#include <limits>
#include <random>
#include <sstream>
#include <string>
#include <vector>

std::mt19937 RNG(42);
std::uniform_real_distribution<> distribution(0.0, 1.0);

using namespace std;

const double inf = numeric_limits<double>::infinity();

struct linexp {  // a*x+b
  double a, b;
  linexp() {
    a = 0;
    b = 0;
  }
  linexp(double na, double nb) : a(na), b(nb) {}
  double eval(double x) { return a * x + b; }
  linexp operator+(const linexp& other) { return linexp(other.a + a, other.b + b); }
};

struct lmincomp {  // if evaluated at critical_value the value is leq 0 then the minimum is earlier else its later
  linexp earlier, later;
  double critical_value;
  bool check_necessary;
  lmincomp(linexp e1, linexp e2) {
    if (e1.a == e2.a) {
      check_necessary = false;
      if (e1.b < e2.b)
        earlier = later = e1;
      else
        earlier = later = e2;
      critical_value = 0;
    } else {
      critical_value = (e2.b - e1.b) / (e1.a - e2.a);
      earlier = e1;
      later = e2;
      if ((e1.a - e2.a) < 0) swap(earlier, later);
      check_necessary = true;
    }
  }
};

ostream& operator<<(std::ostream& strm, const linexp& l) {
  return strm << l.a << "x+" << l.b;
}

struct edge {
  int dest;
  double cost;
  edge() {
    dest = -1;
    cost = inf;
  }
  edge(int d, double c) : dest(d), cost(c){};
};

struct ledge {  // edge with linexpr cost
  int dest;
  linexp cost;
  ledge(int d, linexp l) : dest(d), cost(l) {}
  edge eval(double x) {
    return edge(dest, cost.eval(x));
  }
};

double shortestpath(vector<vector<edge>>& adj) {  // calculate length of shortest path in topologically sorted DAG given by adjacency list from first vertex to last
  vector<bool> visited(adj.size(), false);
  vector<double> dist(adj.size(), 0);
  for (int v = 0; v < adj.size(); v++) {
    for (auto e : adj[v]) {
      if (!visited[e.dest]) {
        visited[e.dest] = true;
        dist[e.dest] = dist[v] + e.cost;
      } else
        dist[e.dest] = min(dist[e.dest], dist[v] + e.cost);
    }
  }
  return dist[adj.size() - 1];
}

vector<vector<ledge>> readgraph(string s) {  // read graph from edge list starting with #vertices #edges with edges of format start end f g
  stringstream ss(s);
  int vert, edge;
  ss >> vert >> edge;
  vector<vector<ledge>> ret(vert);
  for (int i = 0; i < edge; i++) {
    int start, end;
    double f, g;
    ss >> start >> end >> f >> g;
    ret[start].push_back(ledge(end, linexp(-g, f)));
  }
  return ret;
}

double bruteforce_fracpaths(double& best, const vector<vector<ledge>>& adj, int v = 0, double f = 0, double g = 0) {  // for validation
  if (v == adj.size() - 1) {
    best = min(best, f / g);
    return best;
  }
  for (int i = 0; i < adj[v].size(); i++) {
    auto e = adj[v][i];
    auto discard = bruteforce_fracpaths(best, adj, e.dest, f + e.cost.b, g - e.cost.a);
  }
  return best;
}

void print_bruteforce_fracpaths(vector<int>& path, const vector<vector<ledge>>& adj, int v = 0, double f = 0, double g = 0) {  // for validation
  if (v == adj.size() - 1) {
    cout << "path: \n\t\t\t";
    for (auto x : path) cout << x << " ";
    cout << "\ncost= " << f << "/" << g << "=" << (f / g) << "\n\n"
         << endl;
    return;
  }
  for (int i = 0; i < adj[v].size(); i++) {
    auto e = adj[v][i];
    path.push_back(e.dest);
    print_bruteforce_fracpaths(path, adj, e.dest, f + e.cost.b, g - e.cost.a);
    path.pop_back();
  }
}

linexp random_linexp() {
  double a = -distribution(RNG) * 1000 - 1;
  double b = distribution(RNG) * 1000 + 1;
  return linexp(a, b);
}

double megiddo_solve(vector<vector<ledge>>& adj) {
  double bottom = 0, top = inf;                      // track interval for optimum
  int actual_comparison = 0, dodged_comparison = 0;  // for statistics
  vector<linexp> mindist(adj.size());                // current shortest dist to each visited vertex
  vector<bool> visited(adj.size(), false);
  for (int v = 0; v < adj.size(); v++) {
    for (int i = 0; i < adj[v].size(); i++) {
      ledge& l = adj[v][i];

      // handle minimum of linexps
      if (!visited[l.dest]) {
        visited[l.dest] = true;
        mindist[l.dest] = mindist[v] + l.cost;
      } else {
        dodged_comparison++;
        lmincomp cmp(mindist[l.dest], mindist[v] + l.cost);
        if (!cmp.check_necessary)  // avoid division by zero
          mindist[l.dest] = cmp.earlier;
        else if (cmp.critical_value > top)  // eval isn't necessary
          mindist[l.dest] = cmp.earlier;
        else if (cmp.critical_value < bottom)  // eval isn't necessary
          mindist[l.dest] = cmp.later;
        else {                                       // do eval
          vector<vector<edge>> tmpadj(adj.size());   // setup for eval
          for (int ii = 0; ii < adj.size(); ii++) {  // evaluate to numerical adjacency list
            for (int jj = 0; jj < adj[ii].size(); jj++) {
              tmpadj[ii].push_back(adj[ii][jj].eval(cmp.critical_value));
            }
          }
          dodged_comparison--;
          actual_comparison++;  // statistics bookkeeping

          double eval_crit_val = shortestpath(tmpadj);
          if (eval_crit_val > 0) {
            bottom = cmp.critical_value;
            mindist[l.dest] = cmp.later;
          } else {
            top = cmp.critical_value;
            mindist[l.dest] = cmp.earlier;
          }
        }
      }
    }
  }
  double sol = -mindist[adj.size() - 1].b / mindist[adj.size() - 1].a;  // return from form f-x*g to f/g
  cout << "actual comp: " << actual_comparison << " others: " << dodged_comparison << endl;
  return sol;
}

int main() {
  cout << setprecision(4);
  int vertices = 1000;
  for (int testcase = 0; testcase < 10; testcase++) {
    vector<vector<ledge>> adj(vertices);
    // string graph=R"ip(4 6
    // 0 1 1 2
    // 0 2 3 5
    // 0 3 5 4
    // 1 2 3 1
    // 1 3 2 2
    // 2 3 4 8)ip";
    // adj=readgraph(graph);
    for (int i = 0; i < vertices - 1; i++) {  //add random edges to long path
      for (int j = i + 1; j < vertices; j++) {
        if (j == i + 1 || distribution(RNG) < 0.3) {
          adj[i].push_back(ledge(j, random_linexp()));
          // cout<<i<<" "<<j<<" "<<adj[i][adj[i].size()-1].cost<<endl;
        }
      }
    }

    // find length of shortest path in f/g assuming both are positive
    double sol = megiddo_solve(adj);
    double best = inf;

    // vector<int> path(1,0);
    // path.reserve(4);
    // cout<<"bruteforce best: "<<bruteforce_fracpaths(best,adj);
    cout << sol << endl;  //" "<<bruteforce_fracpaths(best,adj)<<"\n";
  }
  // print_bruteforce_fracpaths(path,adj);
  return 0;
}