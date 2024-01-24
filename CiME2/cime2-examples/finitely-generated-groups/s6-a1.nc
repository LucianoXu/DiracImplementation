%***************************************************************************
%
%
% Comple'tion du groupe S_5 modulo A1
%
% Project:                Cime
% Author(s):             Claude March\'e
%
% File name:        s5-a1.nc
% Created on:              03 nov 93
% Last modified on: 03 nov 93
%
%***************************************************************************

operators
  . : infix binary
  I : unary
  e : constant
  x,y,z : variable
  a1,a2,a3,a4,a5 : constant

theory
  AU(.,e)

axioms
  x.I(x) = e;
  I(x).x = e;
  a1.a1 = e;
  a2.a2 = e;
  a3.a3 = e;
  a4.a4 = e;
  a5.a5 = e;
  ((a1.a2).(a1.a2)).(a1.a2) = e;
  ((a2.a3).(a2.a3)).(a2.a3) = e;
  ((a3.a4).(a3.a4)).(a3.a4) = e;
  ((a4.a5).(a4.a5)).(a4.a5) = e;
  a1.a3 = a3.a1;
  a1.a4 = a4.a1;
  a1.a5 = a5.a1;
  a2.a4 = a4.a2;
  a2.a5 = a5.a2;
  a3.a5 = a5.a3;

order
  rpo(a1>a2>a3>a4>a5>I>e>. ; . lrlex)

end

