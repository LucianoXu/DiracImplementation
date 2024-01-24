%***************************************************************************
%
% Rings theory modulo AG(+,0,-)
%
% Project:       Cime
% Author(s):     Claude March\'e
% 
% Created on March 8, 1993
%
% Last modified by $Author: contejea $
% 
% File name: $Source: /users/demons/demons/master-sources-repository/cime/examples/rings-theory/r-modulo-AG-plain-unif-AG.nc,v $
% $Revision: 1.1 $ 
% 
% Last modified on $Date: 1997/11/26 14:11:36 $
% 
%***************************************************************************

operators
  +   : AC
  .   : infix binary
  0,1 : constant
  -   : 1
  x,y,z : variable

unification type plain
theory  AG(+,0,-)
unification theory AG(+,0,-)

axioms
  x.(y.z) = (x.y).z;
  x.1 = x;
  1.x = x;
  x.(y+z) = (x.y)+(x.z);
  (x+y).z = (x.z)+(y.z);

order  
  rpo( .>- >+>0 , .>1 ; . lrlex )
%  interactive
end

