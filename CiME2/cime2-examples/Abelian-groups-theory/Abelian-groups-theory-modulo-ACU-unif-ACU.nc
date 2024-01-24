%***************************************************************************
%
% Abelian groups theory modulo ACU, with ACU unification
%
% $Author: contejea $
% $Source: /users/demons/demons/master-sources-repository/cime/examples/Abelian-groups-theory/Abelian-groups-theory-modulo-ACU-unif-ACU.nc,v $
% $Revision: 1.2 $ 
% $Date: 1997/05/16 07:55:15 $
% 
%***************************************************************************

operators
  + : AC
  0 : constant
  - : unary
  x,y : variable

unification theory ACU(+,0)
theory  ACU(+,0)

axioms
  x+-(x) = 0;

order rpo( - >+>0 ; + mul)

end

