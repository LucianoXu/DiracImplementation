%*******************************************************************
%
% Calcul de la base standard sur F_5 de l'ideal engendre par
%
%   2X^2Y - Y et 3XY^2 -X
%
% $Id: over-f5.nc,v 1.3 1997/05/16 07:57:39 contejea Exp $
%
%*******************************************************************

operators
  +,. : AC
  0,1 : constant
  -   : unary
  X,Y,Z : constant
  x,y,z : variable

theory  FP(5,+,0,-,.,1)

axioms
  (X.X.Y) + (X.X.Y) + -(Y) = 0;
  (X.Y.Y) + (X.Y.Y) + (X.Y.Y) + -(X) = 0;
  
order rpo( Y>X>1>.>- >0>+ ; + mul, . mul)

end

