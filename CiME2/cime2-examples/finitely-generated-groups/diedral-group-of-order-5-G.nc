%***************************************************************************
%
%
% Comple'tion d'un groupe diedral (ordre 5) modulo G
%
%
%
%***************************************************************************

operators
  . : infix binary
  I : unary
  1 : constant
  x,y,z : variable
  a,b : constant

theory G(.,1,I)

axioms

  a.a = 1;
  b.b.b.b.b = 1;
  a.b = I(b).a;


order
  rpo( a > b > I > . , a > b > I > 1;. lrlex )

end

