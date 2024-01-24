%***************************************************************************
%
%
% Calcul de la base standard sur F_5 de l'ideal engendre par
%
%   2X^2Y - Y et 3XY^2 -X
%
% Project:                Cime
% Author(s):             Claude March\'e
%
% File name:        bsf5.nc
% Created on:              15 jul 93
% Last modified on: 15 jul 93
%
%***************************************************************************

operators
  +,* : AC
  0,1 : constant
  -   : unary
  X,Y,Z : constant
  x,y,z : variable

theory  FP(5,+,0,-,*,1)
unification theory ACUN(+,0,5) ACU(*,1)

axioms
  (X*X*Y) + (X*X*Y) + -(Y) = 0;
  (X*Y*Y) + (X*Y*Y) + (X*Y*Y) + -(X) = 0;
  
order rpo( Y>X>1>*>- >0>+ ; + mul, * mul)
 % interactive

end

