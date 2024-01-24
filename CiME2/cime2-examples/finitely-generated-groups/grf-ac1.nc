%***************************************************************************
%
%
% Comple'tion modulo AC1 du groupe finiment engendre' par
%
%    -3a+2b+3c = 0 
%    2a+2b-2c = 0
%
% Project:                Cime
% Author(s):             Claude March\'e
%
% File name:        groupe-fini-ac1.nc
% Created on:              08 mar 93
% Last modified on: 08 mar 93
%
%***************************************************************************

operators
  + : AC
  0 : constant
  - : unary
  x,y : variable
  a,b,c : constant

theory  AC1(+,0)

axioms
  x+-(x)=0;
  -(a+a+a)+b+b+c+c+c = 0;
  a+a+b+b+-(c+c) = 0

order  rpo( a>b>c>->0>+ ; + mul)

problems
  a = b+b+b+b+c

end

