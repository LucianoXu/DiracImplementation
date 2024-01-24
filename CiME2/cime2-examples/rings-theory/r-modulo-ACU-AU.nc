%***************************************************************************
%
% Rings theory modulo ACU(+,0) and AU(.,1)
%
% Author(s):     Claude March\'e
%$Id: r-modulo-ACU-AU.nc,v 1.2 1997/05/16 07:58:31 contejea Exp $
%***************************************************************************

operators
  +   : AC
  .   : infix binary
  0,1 : constant
  -   : 1
  x,y,z : variable

theory ACU(+,0) AU(.,1)
    
axioms
  x+-(x) = 0;
  x.(y+z) = (x.y)+(x.z);
  (x+y).z = (x.z)+(y.z);

order  
  rpo( .> - >+>0 , .>1 ; . lrlex )

end

