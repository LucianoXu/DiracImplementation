%***************************************************************************
%
% Minimal presentation of Abelian groups theory
%
%
%***************************************************************************

operators
  . : infix binary
  I : 1
  e : constant
  x,y,z : variable

axioms
  x.(y.z) = (x.y).z;
  x.e = x;
%  e.x = x;
  x.I(x) = e;
%  I(x).x = e

order
  rpo( I>., I>e;. lrlex )

problems
  I(x.y) = I(x).I(y);

end

