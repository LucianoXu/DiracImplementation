%***************************************************************************
%
% Rings theory modulo ACU(+,0)
%
% Author(s):     Claude March\'e
%
%***************************************************************************

operators
  +   : AC
  .   : infix binary
  0,1 : constant
  -   : 1
  x,y,z : variable

theory ACU(+,0)
unification theory ACU(+,0)
    
axioms
  x+-(x) = 0;
  (x.y).z = x.(y.z);
  x.1 = x;
  1.x = x;
  x.(y+z) = (x.y)+(x.z);
  (x+y).z = (x.z)+(y.z);

order  
  rpo( .>- >+>0 , .>1 ; . lrlex )

end

