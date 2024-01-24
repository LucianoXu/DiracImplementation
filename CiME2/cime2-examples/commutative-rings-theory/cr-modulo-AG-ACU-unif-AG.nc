%***************************************************************************
%
% Commutative rings theory modulo AG(+,0,-) and ACU(.,1)
%
% Project:       Cime
% Author(s):     Claude March\'e
% 
% Created on March 8, 1993
%
% Last modified by $Author: contejea $
% 
% File name: $Source: /users/demons/demons/master-sources-repository/cime/examples/commutative-rings-theory/cr-modulo-AG-ACU-unif-AG.nc,v $
% $Revision: 1.2 $ 
% 
% Last modified on $Date: 1997/05/16 07:56:30 $
% 
%***************************************************************************

operators
  +,. : AC
  0,1 : constant
  -   : 1
  x,y,z : variable

theory 
  AG(+,0,-)
  ACU(.,1)
    
unification theory
  AG(+,0,-)

axioms
  x.(y+z) = (x.y)+(x.z);

order  
  rpo( .>- >+>0 , .>1 )

end

