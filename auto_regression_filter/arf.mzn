include "globals.mzn";
include "jacop.mzn";
include "diff2.mzn";

int: del_add;
int: del_mul;
int: number_add;
int: number_mul;
int: n;
set of int: last;
set of int: add;
set of int: mul;
array[1..n] of set of int: dependencies;
array[1..n] of var 0..100: start_time;
array[1..n] of var 1..2: op_time;
array[1..card(add)] of var 0..100: add_start;
array[1..card(mul)] of var 0..100: mul_start;
var 0..100: final_time;

constraint forall(val in mul)(op_time[val] = del_mul);

constraint forall(val in add)(op_time[val] = del_add);

constraint add_start = [start_time[i] | i in 1..n where i in add];

constraint mul_start = [start_time[i] | i in 1..n where i in mul];

constraint forall(i in 1..n, j in dependencies[i])(start_time[i] + op_time[i] <= start_time[j]);

% constraint
%      let {
%        array[1..card(add)] of var int : start_times = [ start_time[i] | i in add],
%        array[1..card(add)] of var int : number_of_adders = [ number_add | i in add],
%        array[1..card(add)] of var int : operation_time = [ del_add | i in add],
%        array[1..card(add)] of var int : adders_used = [ 1 | i in add]
%      } in diff2(start_times, number_of_adders, operation_time, adders_used);
 
% constraint
%      let {
%        array[1..card(mul)] of var int : start_times = [ start_time[i] | i in mul],
%        array[1..card(mul)] of var int : number_of_multipliers = [ 1..number_add | i in mul],
%        array[1..card(mul)] of var int : operation_time = [ del_mul | i in mul],
%        array[1..card(mul)] of var int : multipliers_used = [ 1 | i in mul]
%      } in diff2(start_times, number_of_multipliers, operation_time, multipliers_used);
 
constraint
     let {
       array[1..card(mul)] of var int : start_times = [ start_time[i] | i in mul],
       array[1..card(mul)] of var int : operation_time = [ del_mul | i in mul],
       array[1..card(mul)] of var int : multipliers_used = [ 1 | i in mul]
     } in cumulative(start_times, operation_time, multipliers_used, number_mul);
 
constraint
     let {
       array[1..card(add)] of var int : start_times = [ start_time[i] | i in add],
       array[1..card(add)] of var int : operation_time = [ del_add | i in add],
       array[1..card(add)] of var int : adders_used = [ 1 | i in add]
     } in cumulative(start_times, operation_time, adders_used, number_add);

constraint final_time = max([start_time[i] + op_time[i] | i in last]);

solve minimize final_time