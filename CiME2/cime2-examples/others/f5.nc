%***************************************************************************
%
% The finite field of cardinal 5
%
%
%***************************************************************************

operators
  +,. : AC
  0,1 : constant
  -   : unary
  x,y,z : variable

theory CR(+,0,-,.,1)

axioms
%  x+0 = x;
%  -(x)+x  = 0;
%  x.1 = x;
%  x.(y+z) = (x.y)+(x.z);
  x+x+x+x+x = 0;
  x.x.x.x.x = x;

order%  rpo( 2>->1>.>+>0 ; + mul, . mul )
interactive


end







