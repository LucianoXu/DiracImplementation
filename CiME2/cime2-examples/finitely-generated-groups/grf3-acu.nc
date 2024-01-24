%***************************************************************************
%
%
% Comple'tion modulo ACU du groupe finiment engendre' par
%
%    2a-3b+c   = 0
%    -3a+2b+3c = 0 
%    2a+2b-2c  = 0
%
%
%***************************************************************************

operators
  + : AC
  0 : constant
  - : unary
  x,y : variable
  a,b,c : constant

theory  ACU(+,0)

axioms
  x+-(x)=0;
  a+a+-(b+b+b)+c = 0;
  -(a+a+a)+b+b+c+c+c = 0;
  a+a+b+b+-(c+c) = 0;

order  rpo( c>b>a>- >0>+ ; + mul )

end

