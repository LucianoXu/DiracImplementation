%***************************************************************************
%
%
% Comple'tion du groupe S_6 modulo G
%
% Project:                Cime
% Author(s):             Claude March\'e
%
% File name:        s6-g.nc
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
  G(.,e,I)

axioms
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
  rpo( I>.>a1>a2>a3>a4>a5>e ; . lrlex) 
%  lexico( rpo( I>.>a1>e , a1=a2=a3=a4=a5 ; . lrlex) ;
%          interactive )
end

