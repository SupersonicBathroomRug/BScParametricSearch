#include <chrono>
#include <iomanip>
#include <iostream>
#include <limits>
#include <random>
#include <sstream>
#include <string>
#include <vector>

const bool DBGOP=true;
const bool OPCRITVALS=false;

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

pair<double, double> shortestpath(vector<vector<ledge>>& adj, double delta) {  // returns pair (length of shortest path according to f-delta*g and the corresponding value of f/g)
  vector<bool> visited(adj.size(), false);
  vector<double> dist(adj.size(), 0);
  vector<double> f(adj.size(), 0);
  vector<double> g(adj.size(), 0);
  for (int v = 0; v < adj.size(); v++) {
    for (auto e : adj[v]) {
      if (!visited[e.dest]) {
        visited[e.dest] = true;
        dist[e.dest] = dist[v] + e.cost.eval(delta);
        f[e.dest] = f[v] + e.cost.b;
        g[e.dest] = g[v] - e.cost.a;
      } else {
        double ecost = e.cost.eval(delta);
        if ((ecost + dist[v]) < dist[e.dest]) {
          dist[e.dest] = ecost + dist[v];
          f[e.dest] = f[v] + e.cost.b;
          g[e.dest] = g[v] - e.cost.a;
        }
      }
    }
  }
  return make_pair(dist[adj.size() - 1], f[adj.size() - 1] / g[adj.size() - 1]);
}

pair<double, int> newtonmethod(vector<vector<ledge>>& adj, double precision = 10e-9) {  // finds minimum cost path according to f/g and returns length using Newton's method
  double delta = inf, fdivg = 0;
  int iterations = 0;
  while (abs(delta) > precision) {
    tie(delta, fdivg) = shortestpath(adj, fdivg);
    iterations++;
  }
  return make_pair(fdivg, iterations);
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

tuple<float, int, int> megiddo_solve(vector<vector<ledge>>& adj) {  // finds minimum cost path according to f/g and returns tuple(length of path, actual comparisons, dodged comparisons) using parametric search
  double bottom = 0, top = inf;                                     // track interval for optimum
  int actual_comparison = 0, dodged_comparison = 0;                 // for statistics
  vector<linexp> mindist(adj.size());                               // current shortest dist to each visited vertex
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
        if(OPCRITVALS)cout<<cmp.critical_value<<"\n";
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
            if(DBGOP)cout<<"< ";
          } else {
            top = cmp.critical_value;
            mindist[l.dest] = cmp.earlier;
            if(DBGOP)cout<<"> ";
          }
          if(DBGOP) cout<<"comparison made, cv: "<<cmp.critical_value<<" bottom: "<<bottom<<" top: "<<top<<endl;
        }
      }
    }
  }
  double sol = -mindist[adj.size() - 1].b / mindist[adj.size() - 1].a;  // return from form f-x*g to f/g
  return make_tuple(sol, actual_comparison, dodged_comparison);
}

tuple<float, int, int,int> megiddo_solve_opt1(vector<vector<ledge>>& adj) {  // finds minimum cost path according to f/g and returns tuple(length of path, actual comparisons, dodged comparisons) using parametric search with optimization (halving interval before actual comparison)
  double bottom = 0, top = inf;                                     // track interval for optimum
  int actual_comparison = 0, dodged_comparison = 0, additional_comparison=0;                 // for statistics
  vector<linexp> mindist(adj.size());                               // current shortest dist to each visited vertex
  vector<bool> visited(adj.size(), false);
  for (int v = 0; v < adj.size(); v++) {
    for (int i = 0; i < adj[v].size(); i++) {
      ledge& l = adj[v][i];
      dodged_comparison++;
      if (!visited[l.dest]) {
          visited[l.dest] = true;
          mindist[l.dest] = mindist[v] + l.cost;
      }
      else{ for (int j=0;j<2;j++){
        // handle minimum of linexps
        double mid=(top+bottom)/2;
        lmincomp cmp(mindist[l.dest], mindist[v] + l.cost);
        if(OPCRITVALS)cout<<cmp.critical_value<<" ";
        double perc=(cmp.critical_value-bottom)/(top-bottom);
        if (!cmp.check_necessary){  // avoid division by zero
          mindist[l.dest] = cmp.earlier;
          break;
        }else if (cmp.critical_value > top){  // eval isn't necessary
          mindist[l.dest] = cmp.earlier;
          break;
        }else if (cmp.critical_value < bottom){  // eval isn't necessary
          mindist[l.dest] = cmp.later;
          break;
        }else if(j==0&&top!=inf&&(perc>0.6||perc<0.4)){
          vector<vector<edge>> tmpadj(adj.size());   // setup for eval
          for (int ii = 0; ii < adj.size(); ii++) {  // evaluate to numerical adjacency list
            for (int jj = 0; jj < adj[ii].size(); jj++) {
              tmpadj[ii].push_back(adj[ii][jj].eval(mid));
            }
          }
          additional_comparison++; dodged_comparison--;
          double eval_crit_val = shortestpath(tmpadj);
          if (eval_crit_val > 0)
            bottom = mid;
          else
            top = mid;
          if(DBGOP) cout<<mid<<" -------comparison made, perc: "<<perc<<" bottom: "<<bottom<<" top: "<<top<<endl;
        }
        else {                                       // do eval
          vector<vector<edge>> tmpadj(adj.size());   // setup for eval
          for (int ii = 0; ii < adj.size(); ii++) {  // evaluate to numerical adjacency list
            for (int jj = 0; jj < adj[ii].size(); jj++) {
              tmpadj[ii].push_back(adj[ii][jj].eval(cmp.critical_value));
            }
          }
          if(j==0) dodged_comparison--;
          actual_comparison++;  // statistics bookkeeping

          double eval_crit_val = shortestpath(tmpadj);
          if (eval_crit_val > 0) {
            bottom = cmp.critical_value;
            mindist[l.dest] = cmp.later;
          } else {
            top = cmp.critical_value;
            mindist[l.dest] = cmp.earlier;
          }
          if(DBGOP) cout<<cmp.critical_value<<" comparison made, perc: "<<perc<<" bottom: "<<bottom<<" top: "<<top<<endl;
          break;
        }
      }
    
    }}
  }
  double sol = -mindist[adj.size() - 1].b / mindist[adj.size() - 1].a;  // return from form f-x*g to f/g
  return make_tuple(sol, actual_comparison, dodged_comparison,additional_comparison);
}

int main() {
  if(DBGOP) cout << setprecision(4);
  int vertices = 10000;
  for (int testcase = 0; testcase < 1; testcase++) {
    vector<vector<ledge>> adj(vertices);
    // string graph=R"ip(4 6
    // 0 1 1 2
    // 0 2 3 5
    // 0 3 5 4
    // 1 2 3 1
    // 1 3 2 2
    // 2 3 4 8)ip";
    // adj=readgraph(graph);
    for (int i = 0; i < vertices - 1; i++) {  // add random edges to long path
      for (int j = i + 1; j < vertices; j++) {
        if (j == i + 1 || distribution(RNG) < 0.3) {
          adj[i].push_back(ledge(j, random_linexp()));
          // cout<<i<<" "<<j<<" "<<adj[i][adj[i].size()-1].cost<<endl;
        }
      }
    }

    // find length of shortest path in f/g assuming both are positive
    double sol;
    int actual_comparison, dodged_comparison, newton_iterations,additional_comparison;
    tie(sol, actual_comparison, dodged_comparison) = megiddo_solve(adj);
    if(DBGOP){
      cout << "Megiddo: " << sol << "\n";  //" "<<bruteforce_fracpaths(best,adj)<<"\n";
      cout << "actual comp: " << actual_comparison << " others: " << dodged_comparison << "\n" << endl;
    }
    // tie(sol,actual_comparison,dodged_comparison,additional_comparison)=megiddo_solve_opt1(adj);
    // if(DBGOP){
    //   cout << "OPTIMIZED Megiddo: " << sol << "\n";  //" "<<bruteforce_fracpaths(best,adj)<<"\n";
    //   cout << "actual comp: " << (actual_comparison+additional_comparison) << " others: " << dodged_comparison << " for optimization: "<<additional_comparison<< "\n" << endl;
    // }

    // tie(sol, newton_iterations) = newtonmethod(adj);
    // if(DBGOP){
    //   cout << "Newton: " << sol << "\n";
    //   cout << "iterations: " << newton_iterations << "\n";
    // }


    if(DBGOP) cout<<"\n----------------------------------------"<<endl;

    //BRUTE FORCE FOR TESTING
    // double best = inf;
    // vector<int> path(1,0);
    // path.reserve(4);
    // cout<<"bruteforce best: "<<bruteforce_fracpaths(best,adj);
    // print_bruteforce_fracpaths(path,adj);
    cout<<endl;
  }
  return 0;
}