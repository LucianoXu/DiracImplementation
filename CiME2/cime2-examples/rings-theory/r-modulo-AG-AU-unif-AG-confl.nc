%***************************************************************************
%
% Rings theory modulo AG(+,0,-) and AU(.,1)
%
% Project:       Cime
% Author(s):     Claude March\'e
% 
% Created on March 8, 1993
%
% Last modified by $Author: marche $
% 
% File name: $Source: /users/demons/demons/master-sources-repository/cime/examples/rings-theory/r-modulo-AG-AU-unif-AG-confl.nc,v $
% $Revision: 1.1 $ 
% 
% Last modified on $Date: 1996/02/27 17:03:07 $
% 
%***************************************************************************

operators
  +   : AC
  .   : infix binary
  0,1 : constant
  -   : 1
  x,y,z : variable

theory  AG(+,0,-) AU(.,1)
unification theory  AG(+,0,-) 

axioms
  x.(y+z) = (x.y)+(x.z);
  (x+y).z = (x.z)+(y.z);
  x.0 = 0;
  0.x = 0;
  x.-(y) = -(x.y);
  -(x).y = -(x.y);

order  
  rpo( .>->+>0 , .>1 ; . lrlex )
%  interactive
end

