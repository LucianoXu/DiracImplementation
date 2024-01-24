%***************************************************************************
%
% Rings theory modulo AC(+)
%
% $Id: r.nc,v 1.3 1997/05/16 07:58:52 contejea Exp $
% 
%***************************************************************************

operators
  +   : AC
  .   : infix binary
  0,1 : constant
  -   : 1
  x,y,z : variable

axioms
  x+0 = x;
  x+-(x) = 0;
  x.(y.z) = (x.y).z;
  x.1 = x;
  1.x = x;
  x.(y+z) = (x.y)+(x.z);
  (x+y).z = (x.z)+(y.z);

order  
  rpo( .>- >+>0 , .>1 ; . lrlex )
%  interactive
end

