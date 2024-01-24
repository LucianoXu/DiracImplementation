%***************************************************************************
%
%
% Comple'tion modulo AG du groupe finiment engendre' par
%
%    2a-3b+c   = 0
%    -3a+2b+3c = 0 
%    2a+2b-2c  = 0
%
% Project:                Cime
% Author(s):             Claude March\'e
%
% File name:        grf3-ag.nc
% Created on:              24 mar 93
% Last modified on: 28 avr 93
%
%***************************************************************************

operators
  + : AC
  0 : constant
  - : unary
  x,y : variable
  a,b,c : constant

theory  AG(+,0,-)
unification theory AG(+,0,-)


axioms
  a+a+-(b+b+b)+c = 0;
  -(a+a+a)+b+b+c+c+c = 0;
  a+a+b+b+-(c+c) = 0;

order  rpo( c>b>a>- >0>+ ; + mul )

end

