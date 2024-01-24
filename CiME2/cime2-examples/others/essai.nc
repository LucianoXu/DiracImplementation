%***************************************************************************
%
%
% Comple'tion modulo AG du groupe finiment engendre' par
%
%    -a = 0 
%
% Project:                Cime
% Author(s):             Claude March\'e
%
% File name:        essai.nc
% Created on:              08 mar 93
% Last modified on: 08 mar 93
%
%***************************************************************************

operators
  + : AC
  0 : constant
  - : unary
  x,y : variable
  a,b : constant

theory  AG(+,0,-)

axioms
  -(a) = 0;

order  rpo( a>b>->0>+ ; + mul )

problems
  a = 0;

end

