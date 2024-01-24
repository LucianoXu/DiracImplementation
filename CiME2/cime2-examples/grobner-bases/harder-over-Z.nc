%***************************************************************************
%
%
% Comple'tion modulo CR de l'anneau quotient d\'efini par
%
%   2X^2YZ - Y , 3XY^2Z -X et XYZ^2 -ZY 
%
%
%***************************************************************************

operators
  +,* : AC
  0,1 : constant
  -   : unary
  X,Y,Z : constant
  x,y,z : variable

theory  CR(+,0,-,*,1)

axioms
  (X*X*Y*Z) + (X*X*Y*Z) + -(Y) = 0;
  (X*Y*Y*Z) + (X*Y*Y*Z) + (X*Y*Y*Z) + -(X) = 0;
  (X*Y*Z*Z) + (X*Y*Z*Z) + -(Z*Y) = 0;
  
order rpo( Z>Y>X>*>1>- >0>+ ; + mul, * mul )

end

