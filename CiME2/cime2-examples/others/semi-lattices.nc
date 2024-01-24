%***************************************************************************
%
% Semi-lattices theory. This should never terminate since it has
% been shown that this theory does not possess any canonical system
%
% Author(s):     Claude March\'e
% 
%***************************************************************************

operators
  +,. : AC
  0,1 : constant
  -   : 1
  x,y,z : variable

theory 
  AC1I(+,0)
    
axioms
  x.0 = 0;
  x.(y+z) = (x.y)+(x.z);
  x.x = x;

order  
  rpo( .>->+>0 , .>1 )

end


