%***************************************************************************
%
%
% Comple'tion modulo AC des anneaux commutatifs
%
%
%***************************************************************************

operators
  +,. : AC
  0,1 : constant
  -   : 1
  x,y,z : variable

axioms
  x+0 = x;
  -(x)+x  = 0;
  x.1 = x;
  x.(y+z) = (x.y)+(x.z);

order rpo( .>->+>0; + mul, . mul)

%problems
%  (x+y)   .(x+y)    = (x.x)+(x.y)+(x.y)+(y.y);
%  (x+-(y)).(x+-(y)) = (x.x)+-(x.y)+-(x.y)+(y.y);
%  (x+y)   .(x+-(y)) = (x.x)+-(y.y);

end

