%***************************************************************************
%
%
% Comple'tion modulo CR de l'anneau quotient d\'efini par
%
%   2X^2Y - Y et 3XY^2 -X
%
% Project:                Cime
% Author(s):             Claude March\'e
%
% File name:        grobner1.nc
% Created on:              10 mar 93
% Last modified on: 10 mar 93
%
%***************************************************************************

operators
  +,* : AC
  0,1 : constant
  -   : unary
  X,Y,Z : constant
  x,y,z : variable

axioms
  x+0 = x;
  x*1 = x;
  x+-(x) = 0;
  -(0) = 0;
  -(-(x)) = x;
  -(x+y) = -(x)+-(y);
  x*(y+z) = (x*y)+(x*z);
  x*0 = 0;
  x*-(y) = -(x*y); 
  (X*X*Y) + (X*X*Y) + -(Y) = 0;
  (X*Y*Y) + (X*Y*Y) + (X*Y*Y) + -(X) = 0;
  
order  rpo( Y>X>1>*>- >+>0 ; + mul, * mul )

end

