include "globals.mzn";

int: graph_size;
int: n_edges;
int: n_dests;

int: start;
array [1..n_dests] of 1..graph_size : dest;

array [1..n_edges] of 1..graph_size : from;
array [1..n_edges] of 1..graph_size : to;
array [1..n_edges] of int : cost;

int: n_dEdges = 2*n_edges;

array [1..n_dEdges] of 1..graph_size: dFrom = from ++ to;
array [1..n_dEdges] of 1..graph_size: dTo   = to ++ from;

array [1..2*n_dEdges] of 1..graph_size: flatTransposedEdges = dFrom ++ dTo;

array[1..2,1..n_dEdges] of 1..graph_size: transposedEdges = array2d(1..2,1..n_dEdges,flatTransposedEdges);

array[1..2*n_dEdges] of 1..graph_size: flatEdges = [transposedEdges[j,i] | i in 1..n_dEdges, j in 1..2];

array[1..n_dEdges,1..2] of 1..graph_size: edges = array2d(1..n_dEdges,1..2,flatEdges);

%array [1..n_dEdges] of int: indirect_cost =  [ 4,  2,  5,  10, 3,  4, 11, 4,  2,  5,  10, 3,  4,  11];
array [1..n_dEdges] of int: indirect_cost = cost ++ cost;

var int: tot_cost;
array [1..n_dEdges] of var 0..1000000: out_flow;

constraint network_flow_cost (edges, [2, 0, 0, 0, -1, -1], indirect_cost, out_flow, tot_cost);

array [1..n_dEdges] of var 0..1: out_flow_binary;

constraint forall (i in 1..n_dEdges) (if out_flow[i] > 0 then out_flow_binary[i]=1 else out_flow_binary[i] = 0 endif);
%%constraint forall (i in 1..n_dEdges) (out_flow_binary[i] = ( 1 where out_flow[i] > 0 ))

var int: minimized_sum = sum (i in 1..n_dEdges) (out_flow_binary[i]*indirect_cost[i]);

solve minimize minimized_sum;

output [ show(minimized_sum) ];