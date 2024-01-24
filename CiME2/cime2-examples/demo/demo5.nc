%***************************************************************************
%
%
% Exemple de specification
%

% Project:                Cime
% Author(s):             Claude March\'e
%
% File name:        demo5.nc
% Created on:              1 avr 93
% Last modified on: 1 avr 93
%
%***************************************************************************

operators

% entiers
  0,1,2,3,4,5,6,7 : constant
  s : unary
  eq : infix binary

% booleens  
  true, false : constant
  and, or : AC

% listes
  nil : constant
  . : infix binary
  mem : binary

% variables
  x,y,z : variable

theory  
  ACU(or,false)
  ACU(and,true)

axioms

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

% booleens
  true or x = true;
  false and x = false;  

% listes    
  mem(x,nil) = false;
  mem(x,y.z) = (x eq y) or (mem(x,z));

order
 rpo( 7>6>5>4>3>2>1>s>0, mem>eq>or>true>false)
 % interactive

problems
  
  reduce mem(7,1.(2.(x.(3.nil)))) ;
  reduce mem(7,1.(2.(x.(3.(y.nil))))) ;

end

