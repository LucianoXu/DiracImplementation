%***************************************************************************
% 
% Theory of distributive lattices
% 
% Project:       Cime
% Author(s):     Claude March\'e
% 
% Created on March 8, 1993
%
% Last modified by $Author: marche $
% 
% File name: $Source: /users/demons/demons/master-sources-repository/cime/examples/distributive-lattices/distributive-unitary-lattices.nc,v $
% $Revision: 1.1 $ 
% 
% Last modified on $Date: 1996/05/28 14:15:19 $
% 
%***************************************************************************

operators
  &, V : AC
  0,1 : constant 
  x,y,z : variable


axioms
 x & 1 	      = x ;
 x & 0 	      = 0 ;
 x V 1 	      = 1 ;
 x V 0 	      = x ;
 x & x        = x ;
 x V x        = x ;
 x & (y V x)  = x ;
 x V (y & z) = (x V y) & (x V z) ;

order
  rpo( V>& )
 % interactive
end

