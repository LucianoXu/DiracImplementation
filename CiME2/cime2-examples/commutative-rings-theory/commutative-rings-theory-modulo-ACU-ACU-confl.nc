%***************************************************************************
%
% Commutative rings theory modulo ACU(+,0) and ACU(*,1)
%
% Project:       Cime
% Author(s):     Claude March\'e
% 
% Created on March 8, 1993
%
% Last modified by $Author: marche $
% 
% File name: $Source: /users/demons/demons/master-sources-repository/cime/examples/commutative-rings-theory/commutative-rings-theory-modulo-ACU-ACU-confl.nc,v $
% $Revision: 1.1 $ 
% 
% Last modified on $Date: 1996/05/28 14:15:06 $
% 
%***************************************************************************

operators
  +,. : AC
  0,1 : constant
  -   : 1
  x,y,z : variable

theory ACU(+,0) ACU(.,1)
% unification theory ACU(+,0) ACU(.,1)
    
axioms
  x+-(x) = 0;
  x.(y+z) = (x.y)+(x.z);
  -(0) = 0;
  x.0 = 0;
  x.-(y) = -(x.y);
  -(-(x)) = x;
  -(x+y) = -(x)+-(y);

order  
  rpo( .>->+>0 , .>1 )

end

