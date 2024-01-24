%***************************************************************************
%
%
% Comple'tion du groupe du double tore: (a,b,c,d;abcda'b'c'd=1)
%
% modulo rien
%
%
%***************************************************************************

operators
  . : infix binary
  I : unary
  e : constant
  x,y,z : variable
  a,b,c,d : constant

axioms
  x.(y.z) = (x.y).z;
  x.e = x;
  e.x = x;
  x.I(x) = e;
  I(x).x = e;
  a.b.c.d.I(a).I(b).I(c).I(d) = e;

order
  rpo( a>b>c>d>I>e>.;. lrlex )
% interactive
end

