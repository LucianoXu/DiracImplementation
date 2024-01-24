%***************************************************************************
%
%
% Comple'tion des booleens 
% modulo AC
%
%
% Project:                Cime
% Author(s):             Claude March\'e
%
% File name:        booleens.nc
% Created on:              05 nov 93
% Last modified on: 05 nov 93
%
%***************************************************************************

operators
  xor, and, or : AC
  false, true : constant
  x,y,z : variable
  -,not : unary

theory CR(xor,false,-,and,true)

axioms
  x and x = x;
  x or y = not(not(x) and not(y));
  not(x) xor x = true;

order  rpo (
   or > not > true > and > - > xor > false)

end





