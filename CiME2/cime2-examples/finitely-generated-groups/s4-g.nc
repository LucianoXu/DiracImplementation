%***************************************************************************
%
% Group S_4 modulo G
%
% Author(s):     Claude March\'e
%
%***************************************************************************

operators
  . : infix binary
  I : unary
  e : constant
  x,y,z : variable
  a1,a2,a3 : constant

theory
  G(.,e,I)

axioms
  a1.a1 = e;
  a2.a2 = e;
  a3.a3 = e;
  ((a1.a2).(a1.a2)).(a1.a2) = e;
  ((a2.a3).(a2.a3)).(a2.a3) = e;
  a1.a3 = a3.a1;

order
  lexico ( rpo(I>.>a1>e , a1=a2=a3 ; . lrlex) ;
           rpo(a1>a2>a3 ; . lrlex) ;
           interactive )
end

