%***************************************************************************
%
%
% Comple'tion du groupe du double tore: (a,b,c,d;abcda'b'c'd=1)
%
% modulo A1(.,e)
%
% Project:                Cime
% Author(s):             Claude March\'e
%
% File name:        dtorus-a1.nc
% Created on:              08 nov 93
% Last modified on: 08 nov 93
%
%***************************************************************************

operators
  . : infix binary
  I : unary
  e : constant
  x,y,z : variable
  a,b,c,d : constant

theory
  AU(.,e)

axioms
  x.I(x) = e;
  I(x).x = e;
  a.b.c.d.I(a).I(b).I(c).I(d) = e;

order
  rpo( a>b>c>d>I>e>.;. lrlex )
% interactive
end

