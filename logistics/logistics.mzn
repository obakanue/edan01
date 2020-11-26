include "globals.mzn";

int: graph_size;
int: start;
int: n_dests;
array[1..n_dests] of 1..graph_size: dest;
int: n_edges;
array[1..n_edges] of 1..graph_size: from;
array[1..n_edges] of 1..graph_size: to;
array[1..n_edges] of int: cost;


array[1..graph_size] of int: balance = [if i = 1 then n_dests elseif exists(v in dest)(v == i)
 then -1 else 0 endif | i in 1..graph_size];

% Merge to and from to create an array with all the edges in 2d form.
array[1..2*n_edges] of 1..graph_size: edges = [if j = 0 then from[i] else to[i] endif | i in 1..n_edges, j in 0..1];
array[1..n_edges, 1..2] of 1..graph_size: final_edges = array2d(1..n_edges, 1..2, edges);

array[1..n_edges] of int: final_cost = cost;

array[1..n_edges] of var -1000..1000: flow;

constraint network_flow(final_edges, balance, flow);
var int: cost_sum = sum([1 * final_cost[i] | i in 1..n_edges where flow[i] != 0]);

solve minimize cost_sum;

output["Edge = \(show(final_edges[i, 1])) -> \(show(final_edges[i, 2]))    Cost = \(show(final_cost[i]))    Flow = \(show(flow[i]))\n" | i in 1..n_edges];
output[show(cost_sum)]

