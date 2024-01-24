%***************************************************************************
%
% Commutative rings theory modulo AG(+,0,-)
%
% Project:       Cime
% Author(s):     Claude March\'e
% 
% Created on March 8, 1993
%
% Last modified by $Author: contejea $
% 
% File name: $Source: /users/demons/demons/master-sources-repository/cime/examples/commutative-rings-theory/cr-modulo-AG.nc,v $
% $Revision: 1.2 $ 
% 
% Last modified on $Date: 1997/05/16 07:56:37 $
% 
%***************************************************************************

operators
  +,. : AC
  0,1 : constant
  -   : 1
  x,y,z : variable

theory 
  AG(+,0,-)
    
axioms
  x.(y+z) = (x.y)+(x.z);
  x.1 = x;

order  
  rpo( .>- >+>0 , .>1 )

end

