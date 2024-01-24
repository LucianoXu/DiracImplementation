%***************************************************************************
%
% Abelian groups theory modulo AC
%
% $Id: Abelian-groups-theory-modulo-AC.nc,v 1.4 1997/07/01 16:14:47 marche Exp $
% 
%***************************************************************************

operators
  + : AC
  0 : constant
  - : unary
  x,y,z : variable

axioms
  x+0    = x;
  x+-(x) = 0;

order 
  rpo( - > 0 > + ; + mul)
%  interactive

end

