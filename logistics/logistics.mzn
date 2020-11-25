include "globals.mzn";

int: graph_size;
int: start;
int: n_dests;
array[1..n_dests] of 1..graph_size: dest;
int: n_edges;
array[1..n_edges] of 1..graph_size: from;
array[1..n_edges] of 1..graph_size: to;
array[1..n_edges] of int: cost;

%array[1..graph_size] of int: balance1 = [1, 0, 0, 0, 0, -1];
%array[1..graph_size] of int: balance2 = [2, 0, 0, 0, -1, -1];
array[1..graph_size] of int: balance3 = [2, 0, 0, 0, -1, -1];


% Merge to and from to create an array with all the edges in 2d form.
array[1..2*n_edges] of 1..graph_size: edges1 = [if j = 0 then from[i] else to[i] endif | i in 1..n_edges, j in 0..1];
array[1..2*n_edges] of 1..graph_size: edges2 = [if j = 1 then from[i] else to[i] endif | i in 1..n_edges, j in 0..1];
array[1..2*n_edges, 1..2] of 1..graph_size: final_edges = array2d(1..2*n_edges, 1..2, edges1 ++ edges2);

array[1..2*n_edges] of int: final_cost = cost ++ cost;

array[1..2*n_edges] of var 0..1000: flow;

constraint network_flow(final_edges, balance3, flow);
var int: cost_sum = sum([1 * final_cost[i] | i in 1..2*n_edges where flow[i] > 0]);

solve minimize cost_sum;

output["Edge = \(show(final_edges[i, 1])) -> \(show(final_edges[i, 2]))    Cost = \(show(final_cost[i]))    Flow = \(show(flow[i]))\n" | i in 1..2*n_edges];
output[show(cost_sum)]

