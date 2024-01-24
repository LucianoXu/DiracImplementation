%***************************************************************************
%
%
% Comple'tion des groupes abe'liens modulo AC1
%
%
% Project:                Cime
% Author(s):             Claude March\'e
%
% File name:        demo2.nc
% Created on:              08 mar 93
% Last modified on: 08 mar 93
%
%***************************************************************************

operators
  + : AC
  0 : constant
  - : unary
  x,y : variable

theory  ACU(+,0)

axioms
  x+-(x) = 0;

order  % rpo( ->+>0 ; + mul)
  interactive

end

