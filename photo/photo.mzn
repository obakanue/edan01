%%%     Placing people on a photo
%%      Description
% A group of n people wants to take a group photo. Each person can give preferences next to whom he or she wants to be placed in the photo. A person can give any number of preferences and a preference is unidirectional, i.e. if both Per and Vicky wants to stand next to the other placing them next to each other satisfies two preferences.  All people are place on one line, so everyone have two neighbours, with the exception of the people at the ends of the line, which have one neighbour.

% Task 1: Write a program that finds a placement that maximizes the number satisfied preferences, i.e. the cost function counts the number of satisfied preferences. The preferences are provided in a data input file. Two examples are provided bellow.

include "globals.mzn";

%%      Variables

% Number of people
int: n;
% Number of preferences
int: n_prefs;
% Preferences tuple array
array[1..n_prefs, 1..2] of int: prefs;

%%      Model

% Pos array solution
array[1..n] of var 1..n: final_pos;
% Satisfied preferences in solution
var 0..n_prefs: satisfies;
% Array for saving satisifed preferences
array[1..n_prefs] of var bool: satisfies_array;

% Non-negativity constraint
constraint 
  n >= 0 /\ 
  n_prefs >= 0;

% Absolute of a person and his preffered neighbours position is saved to satisfies_array
constraint
  forall (i in 1..n_prefs) (
    let {
      int: person = prefs[i,1],
      int: prefered_neighbour = prefs[i,2]
    } in
    satisfies_array[i] = (abs(final_pos[person]-final_pos[prefered_neighbour]) == 1)
  );

% Variable 'satisfies' has to be the same as the sum of all true values in 'satifies_array' 
constraint
  sum (i in 1..n_prefs) (bool2int(satisfies_array[i])) = satisfies;

% No person sharing a position
constraint
  alldifferent(final_pos);

solve maximize satisfies;

output [
    "pos = ", show(final_pos), "\n",
    "satisifes = ", show(satisfies), "\n"
];