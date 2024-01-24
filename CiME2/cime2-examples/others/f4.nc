%***************************************************************************
%
% Completion modulo AC du corps fini F_4
%
%
%***************************************************************************

operators
  +,. : AC
  0,1,a : constant
  -   : 1
  x,y,z : variable

theory  CR(+,0,-,.,1)

axioms
%  x+0 = x;
%  -(x)+x  = 0;
%  x.1 = x;
%  x.(y+z) = (x.y)+(x.z);
  x+x = 0;
  x.x.x.x = x;
  (a.a)+a+1 = 0;

order%  rpo( ->1>.>+>0 ; + mul, . mul )
interactive

end







