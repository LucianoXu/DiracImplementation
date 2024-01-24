%***************************************************************************
%
%
% Comple'tion des groupes abe'liens modulo AC
%
%
% Project:                Cime
% Author(s):             Claude March\'e
%
% File name:        demo2bis.nc
% Created on:              08 mar 93
% Last modified on: 26 avr 93
%
%***************************************************************************

operators
  + : AC
  0 : constant
  - : unary
  x,y : variable

axioms
  x+0 = x;
  x+-(x) = 0;

order 
%  rpo( ->+>0 ; + mul)
  interactive

end

