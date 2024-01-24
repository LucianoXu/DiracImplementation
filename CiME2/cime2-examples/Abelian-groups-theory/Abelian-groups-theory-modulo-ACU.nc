%***************************************************************************
%
% Abelian groups theory modulo ACU, with AC unification
%
% $Author: marche $
% $Source: /users/demons/demons/master-sources-repository/cime/examples/Abelian-groups-theory/Abelian-groups-theory-modulo-ACU.nc,v $
% $Revision: 1.3 $ 
% $Date: 1997/07/01 16:14:49 $
% 
%***************************************************************************

operators
  + : AC
  0 : constant
  - : unary
  x,y,z : variable

theory  ACU(+,0)

axioms
  x+-(x) = 0;

order rpo( - >0>+ ; + mul)

end

