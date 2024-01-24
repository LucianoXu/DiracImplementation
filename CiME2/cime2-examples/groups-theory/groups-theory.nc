%***************************************************************************
%
% Groups theory
% 
% File name:        $Source: /users/demons/demons/master-sources-repository/cime/examples/groups-theory/groups-theory.nc,v $
% Revision:         $Revision: 1.1 $ 
% Last modified by: $Author: marche $
% Last modified on: $Date: 1996/02/15 12:05:54 $
% 
%***************************************************************************

operators
  . : infix binary
  I : unary
  e : constant
  x,y,z : variable

axioms
  x.(y.z) = (x.y).z;
  x.e = x;
  e.x = x;
  x.I(x) = e;
  I(x).x = e;

order
  rpo( I>., I>e;. lrlex )
% interactive
end

