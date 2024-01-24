%***************************************************************************
%
%
% Comple'tion modulo AC d'un corps premier
%
%
%***************************************************************************

operators
  +,. : AC
  0,1,2 : constant
  -   : 1
  x,y,z : variable


axioms
  x+0 = x;
  -(x)+x  = 0;
  x.1 = x;
  x.(y+z) = (x.y)+(x.z);
  x+x+x = 0;
  x.x.x = x;
  2 = 1+1;

order%  rpo( 2>->1>.>+>0 ; + mul, . mul )
interactive

problems
  (x+y)   .(x+y)    = (x.x)+(x.y)+(x.y)+(y.y);
  (x+-(y)).(x+-(y)) = (x.x)+-(x.y)+-(x.y)+(y.y);
  (x+y)   .(x+-(y)) = (x.x)+-(y.y);
  reduce 2.2;

end







