%***************************************************************************
%
%
% Comple'tion du groupe finiment engendre' par
%
%    -3a+2b+3c = 0 
%    2a+2b-2c = 0
%
%***************************************************************************

operators
  + : AC
  0 : constant
  - : unary
  x,y : variable
  a,b,c : constant

axioms
  x+0=x;
  x+-(x)=0;
  -(a+a+a)+b+b+c+c+c = 0;
  a+a+b+b+-(c+c) = 0

order  rpo( a>b>c>->0>+ ; + mul )

problems
  a = b+b+b+b+c

end

