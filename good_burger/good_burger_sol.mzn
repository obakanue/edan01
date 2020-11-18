int: beef;
int: bun;
int: cheese;
int: onions;
int: pickles;
int: lettuce;
int: ketchup;
int: tomato;

array[beef..tomato] of int: sodium;
array[beef..tomato] of int: fat;
array[beef..tomato] of int: calories;
array[beef..tomato] of int: cost;

% decision variables
array[beef..tomato] of var 1..5: x;
var int: total = sum([x[i]*cost[i] | i in beef..tomato]);

% solve minimize total;
solve maximize total;
%solve satisfy;

constraint
   % sodium < 3000mg, fat < 150g, calories < 3000
     sum([x[i]*sodium[i] | i in beef..tomato]) < 3000
     /\ sum([x[i]*fat[i] | i in 1..tomato]) < 150
     /\ sum([x[i]*calories[i] | i in beef..tomato]) < 3000
;

constraint
    % keep the serving of ketchup and lettuce the same
    x[ketchup] = x[lettuce]
    % keep the servings of pickles and tomatoes the same.
    /\ x[pickles] = x[tomato]
;

output [
  "total   : ", show(total), " cent\n",
  "sodium  : ", show(sum([x[i]*sodium[i] | i in beef..tomato])), " mg\n",
  "fat     : ", show(sum([x[i]*fat[i] | i in beef..tomato])), " g\n",
  "calories: ", show(sum([x[i]*calories[i] | i in beef..tomato])), "\n",
  "x       : ", show(x), "\n",
  "recipes : ", show(x), "\n",
]
++
[
  show(i) ++ ": " ++ show(x[i]) ++ " (" ++ show_int(3,x[i]*cost[i]) ++ " cent)\n"
  | i in beef..tomato
]
;