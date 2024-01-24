%***************************************************************************
%
% Operateurs de parallelisme
%
% File name:        $Source: /users/demons/demons/master-sources-repository/cime/examples/others/parall.nc,v $
% Revision:         $Revision: 1.2 $ 
% Last modified by: $Author: marche $
% Last modified on: $Date: 1995/09/12 12:38:38 $
%
%***************************************************************************

operators
  + : AC
  . : infix binary
  0,1 : constant
  -   : 1
  x,y,z : variable

axioms
  (x.y).z = x.(y.z);
  x+x  = x;
  (y+z).x = (y.x)+(z.x);

order rpo(.>1, .>->0>+ ; + mul, . lrlex)

end

