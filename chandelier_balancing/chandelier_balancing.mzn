include "globals.mzn"; 
int: n = 9;

set of 1..n: T = 1..n;

var T: a;
var T: b;
var T: c;
var T: d;
var T: e;
var T: f;
var T: g;
var T: h;
var T: i;
var int: total = a+b+c+d+e+f+g+h+i;

solve satisfy;

constraint
  alldifferent([a,b,c,d,e,f,g,h,i])
  /\
  (2*a = 1*b+2*c) /\
  (2*d+1*e = 1*f) /\
  (2*g+1*h = 3*i) /\
  3*(a+b+c) = 2*(d+e+f)+3*(g+h+i) 

;

output [
  show(["a","b","c","d","e","f","g","h","i"]) ++ "\n" ++
  show([a,b,c,d,e,f,g,h,i])
];