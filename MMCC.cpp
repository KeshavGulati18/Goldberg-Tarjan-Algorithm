//
// Goldberg-Tarjan's minimum mean cycle canceling algorithm
//
// Description:
//   Given a directed graph G = (V,E) with nonnegative capacity c and cost w.
//   The algorithm find a maximum s-t flow of G with minimum cost.
// 
// Algorithm:
//   Goldberg-Tarjan (Tomizawa (1971)'s algorithm.
//   It first finds a feasible (i.e., maximum) flow. Then it successively
//   finds negative cycles, and cancels them.
//   By finding minimum mean cycle, it finishes in strongly polynomial time.
//
// Complexity:
//   O(n^2 m^2 log(nC), where C is the maximum capacity. 
//   Practically, this is much slower than other algorithms.
// 
// References:
//   A. Goldberg and R. E. Tarjan (1989):
//   Finding minimum-cost circulations by canceling negative cycles.
//   Journal of the ACM, vol. 36, no. 4, pp. 873--886.


#include <iostream>
#include <vector>
#include <queue>
#include <cstdio>
#include <cstdlib>
#include <map>
#include <cmath>
#include <cstring>
#include <functional>
#include <algorithm>
#include <unordered_map>
#define f first
#define s second
const long long INF = 1e9;

using namespace std;

struct graph 
{
  struct edge 
  {
    int source;
    int destination;
    int capacity; 
    int flow;
    int cost;
    unsigned int rev;
  };
  
  int n;
  vector<vector<edge>> adj;
  vector<edge> edges;
  vector<vector<int>> residual_capacity;

  graph(int num)
  {
    n = num;
    adj.resize(num);
  }

  void add_edge(int source, int destination, int capacity, int cost) 
  {
    adj[source].push_back({source, destination, capacity, 0, cost, adj[destination].size()});
    adj[destination].push_back({destination, source, 0,  0, -cost, adj[source].size()-1});
  }
  
  //----------------------------------------------------------------------------------------------------------------------------//
  
  // 1) Find a feasible flow f using ford_fulkerson  ------------   Time Complexity - O(V.E^2)

  int bfs(int source, int target, vector<int>& parent) 
  {
    // Initialize the parent array by -1
    fill(parent.begin(), parent.end(), -1);
    parent[source] = -2;
    queue<pair<int, int>> q;
    q.push({source, INF});

    while (!q.empty()) 
    {
        int current_node = q.front().first;
        int flow = q.front().second;
        q.pop();

        for (auto edge : adj[current_node]) 
        {
            int next_node = edge.destination;
            if (parent[next_node] == -1 && residual_capacity[current_node][next_node]) 
            {
                parent[next_node] = current_node;
                int new_flow = min(flow, residual_capacity[current_node][next_node]);
                if (next_node == target)
                {
                  return new_flow;
                }
                q.push({next_node, new_flow});
            }
        }
    }
    return 0;
  }

  int max_flow_ford_fulkerson(int source, int target) 
  {
    int total_flow = 0, new_flow = 0;
    vector<int> parent(n);
    
    // Initializing residual capacity matrix with initial capacity
    residual_capacity.resize(n, vector<int>(n, 0));
    for (int node = 0; node < n; node++)
    {
      for (auto edge: adj[node]) 
      {
         residual_capacity[node][edge.destination] = edge.capacity;
      }
    }

    // BFS algorithm is used for finding augmenting paths
    // Every time we find an augmenting path, one of the edges becomes saturated
    while(new_flow = bfs(source, target, parent)) 
    {
        total_flow += new_flow;
        int current_node = target;
        while (current_node != source) 
        {
            int previous_node = parent[current_node];
            residual_capacity[previous_node][current_node] -= new_flow;
            residual_capacity[current_node][previous_node] += new_flow;
            current_node = previous_node;
        }
    }
    
    // Updating flows in each edge inside the adjacency list.
    for (int node = 0; node < n; node++)
    {
      for (auto &edge: adj[node]) 
      {
        int flow_in_edge = edge.capacity - residual_capacity[node][edge.destination];     // FLOW = CAPACITY - RESIDUAL_CAPACITY
        if(flow_in_edge>0)  // if flow exists in edge then update
        {
          edge.flow = flow_in_edge;
        }
      }
    }
    return total_flow;
  } 


  //----------------------------------------------------------------------------------------------------------------------------//

  bool minimum_mean_cycle_cancel() 
  {
    vector<vector<int>> dist(n+1, vector<int>(n));
    vector<vector<int>> prev(n+1, vector<int>(n, -1));
    fill(prev[0].begin(), prev[0].end(), 0);

    for (int k = 0; k < n; ++k) 
    {
      for (int u = 0; u < n; ++u) 
      {
        if (prev[k][u] < 0) continue;
        for (auto e: adj[u]) 
        {
          if (e.capacity <= e.flow) continue;
          if (prev[k+1][e.destination] < 0 || dist[k+1][e.destination] > dist[k][u] + e.cost) 
          {
            dist[k+1][e.destination] = dist[k][u] + e.cost;
            prev[k+1][e.destination] = e.rev;
          }
        }
      }
    }
    int num = INF;
    int v, den = 1;
    for (int u = 0; u < n; ++u) 
    {
      int num_u = -INF;
      int den_u = 0;
      for (int k = 0; k < n; ++k) 
      {
        if (prev[k][u] < 0) continue;
        if (num_u * (n-k) < (dist[n][u]-dist[k][u]) * den_u) 
        {
            num_u = (dist[n][u] - dist[k][u]); den_u = n-k;
        }
      }

      if (den_u > 0 && num * den_u > num_u * den) 
      {
        num = num_u; den = den_u; v = u;
      }
    }

    if (num >= 0) return false;
    vector<int> back(n, -1);
    for (int k = n; back[v] < 0; --k) 
    {
      back[v] = prev[k][v];
      edge &r = adj[v][back[v]];
      v = r.destination;
    }

    function<int(int,int)> augment = [&](int u, int cur) 
    {
      if (cur < INF && u == v) return cur;
      edge &r = adj[u][back[u]], &e = adj[r.destination][r.rev];
      int f = augment(r.destination, min(e.capacity - e.flow, cur));
      e.flow += f;
      r.flow -= f;
      return f;
    };
     
    augment(v, INF);
    return true;
  }


  //----------------------------------------------------------------------------------------------------------------------------//

  pair<int, int> min_cost_max_flow(int source, int destination) 
  {
    // 1) Find a feasible flow f (sovle for maximum flow)  ------------   Time Complexity - O(V.E^2)
    int maxflow = max_flow_ford_fulkerson(source, destination);

    // 2) while a negative cost cycle X, exists in graph
    // let X be the minimum mean cycle in residual graph network
    // By finding negative cycles we donot change the amount of flow but only the cost 
    // we find the negative cycle and send a flow equivalent to the capacity of residual network through the cycle
    // we keep doing so untill no such cycle remains in the residual graph
    while(minimum_mean_cycle_cancel());

    int total_cost = 0;
    for(int u = 0; u < n; ++u)
    {
      for (auto &edge: adj[u])
      {
          if(edge.flow > 0) 
          {
             total_cost += edge.flow * edge.cost;
          }
      }
    }

    // since maxflow remains the same and only cost changes 
    return {maxflow, total_cost};
  }


  //----------------------------------------------------------------------------------------------------------------------------//

  void display_edges() 
  {
    for(int node = 0; node < n; node++)
    {
      for (auto edge: adj[node]) 
      {
        cout << "Source - "<<edge.source << "Destination - " << edge.destination << "Capacity - " << edge.capacity << "Flow - " << edge.flow << "Cost - " << edge.cost << "\n";
      }
    }
    
    int total_cost = 0;
    for (int node = 0; node < n; node++)
    { 
      for (auto &edge: adj[node])
      {
        if(edge.flow > 0)
        {
          total_cost += edge.flow * edge.cost;
        }
      }
    }
    cout << "Flow Cost = " << total_cost << endl;
  }
};


  //----------------------------------------------------------------------------------------------------------------------------//

int main() 
{
    cout<<"--------------------------------------------"<<"\n";
    cout<<"Started cycle cancelling algorithm"<<"\n";
    
    // Define the number of nodes for minimum cost flow problem
    int n = 5;
    graph g(n);
    
    int capacity[][5] = { { 0, 3, 1, 0, 3 },
                          { 0, 0, 2, 0, 0 },
                          { 0, 0, 0, 1, 6 },
                          { 0, 0, 0, 0, 2 },
                          { 0, 0, 0, 0, 0 } };
 
    int cost[][5] = { { 0, 1, 0, 0, 2 },
                      { 0, 0, 0, 3, 0 },
                      { 0, 0, 0, 0, 0 },
                      { 0, 0, 0, 0, 1 },
                      { 0, 0, 0, 0, 0 } };

    for(int i = 0; i < n; i++) 
    {
      for (int j = 0; j < n; j++) 
      {
        if (i == j) continue; // if i equals to j then there is a self cycle
        // The self loops are ignored the reason for this is that self loops don't effect on final solution 
        // because when there exists a loop on a vertex, it means a flow from the vertex (with an arbitrary capacity) 
        // goes on pipe that connect to itself, it means the flow doesn't waste, it just return to the vertex. 
        // it's like you connect a water hose from a tank to itself. you don't limit the input flow to the tank or output flow from it.
        // so you can ignore self loops and solve the problem.
        if(capacity[i][j]>0)
        {
          g.add_edge(i, j, capacity[i][j], cost[i][j]);
        }
      } 
    }

    int source = 0, target = n-1;
    auto a = g.min_cost_max_flow(source, target);
    cout << "Maximum flow for min cost -> " << a.f << "\n" << "Min Cost -> " << a.s << " " << "\n";
}
