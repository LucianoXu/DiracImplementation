%***************************************************************************
%
% Rings theory modulo ACU(+,0) and AU(.,1)
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

theory ACU(+,0) AU(.,1)
unification theory ACU(+,0)
    
axioms
  x+-(x) = 0;
  x.(y+z) = (x.y)+(x.z);
  (x+y).z = (x.z)+(y.z);

order  
  rpo( .> - >+>0 , .>1 ; . lrlex )

end

