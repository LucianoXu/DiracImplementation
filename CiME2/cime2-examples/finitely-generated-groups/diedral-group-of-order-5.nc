%***************************************************************************
%
%
% Comple'tion d'un groupe diedral (ordre 5) modulo rien
%
%
%
%***************************************************************************

operators
  . : infix binary
  I : unary
  e : constant
  x,y,z : variable
  a,b : constant

axioms
  x.(y.z) = (x.y).z;
  x.e = x;
  e.x = x;
  x.I(x) = e;
  I(x).x = e;
  a.a = e;
  b.b.b.b.b = e;
  a.b = I(b).a;


order
  rpo( a > b > I > . , a > b > I > e;. lrlex )

end

