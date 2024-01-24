%***************************************************************************
%
% Commutative rings theory modulo AC(+) and AC(*)
%
% Author(s):     Claude Marche'
% 
%***************************************************************************

operators
  +,. : AC
  0,1 : constant
  -   : 1
  x,y,z : variable

axioms
  x+0 = x;
  x+-(x) = 0;
  x.1 = x;
  x.(y+z) = (x.y)+(x.z);

order  
  rpo( .>- >+>0 , .>1 )

end

