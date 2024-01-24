%***************************************************************************
%
%
% Les trucs a ovomaltine
%
%
% Project:                Cime
% Author(s):             Claude March\'e
%
% File name:        ovo.nc
% Created on:              15 apr 93
% Last modified on: 15 apr 93
%
%***************************************************************************

operators
% entiers
  0,1,2,3,4,5,6,7,8,9 : constant
  s : unary
  eq : binary

% booleens  
  true, false : constant
  and, or : AC

% autres
  +,.,* : AC
  ^ , / : binary
  -   : 1
  X,N : constant
  x,y,z,t,a,b,c : variable

theory 
  ACU(or,false)
  ACU(and,true)

axioms

% booleens
  true or x = true;
  false and x = false;  

% entiers  
  0 eq 0 = true;
  0 eq s(y) = false;
  s(x) eq 0 = false;
  s(x) eq s(y) = x eq y;
  1 = s(0);
  2 = s(1);
  3 = s(2);
  4 = s(3);
  5 = s(4);
  6 = s(5);
  7 = s(6);
  8 = s(7);
  9 = s(8);

  x + 0 = x;
  x + s(y) = s(x+y);

  x*0 = 0;
  x*s(y) = (x*y)+x;

  x*(y+z) = (x*y) + (x*z);

  (x/y)+(z/t) = ((x*t)+(y*z))/(y*t);

% autres

  (x^a).(x^b) = x^(a+b);

order 
  rpo( 9>8>7>6>5>4>3>2>1>s>0,
       eq>or>true>false,
       . > ^ > + > s, 
       * > + > / 
     )

problems
  reduce (x^(c/2)).(N^3).(x^(c/3)).(N^1);

end

