%***************************************************************
%
%
% Calcul de la base standard sur F_5 de l'ideal engendre par
%
%   2X^2Y - Y et 3XY^2 -X
%
% $Id: over-f5-AC.nc,v 1.3 1997/05/16 07:57:34 contejea Exp $
%
%***************************************************************

operators
  +,. : AC
  0,1 : constant
  -   : unary
  X,Y,Z : constant
  x,y,z : variable


axioms
  x+0 = x;
  x.1 = x;
  x.(y+z) = (x.y)+(x.z);
  x.0 = 0;
  -(x) = x+x+x+x;
  x+x+x+x+x = 0;
  (X.X.Y) + (X.X.Y) + -(Y) = 0;
  (X.Y.Y) + (X.Y.Y) + (X.Y.Y) + -(X) = 0;
  
order rpo( Y>X>1>.>- >+>0 ; + mul, . mul)

end

