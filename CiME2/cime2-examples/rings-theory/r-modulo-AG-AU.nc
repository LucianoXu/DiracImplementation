%***************************************************************************
%
% Rings theory modulo AG(+,0,-) and AU(.,1)
%
% Project:       Cime
% Author(s):     Claude March\'e
% 
% Created on March 8, 1993
%
% Last modified by $Author: contejea $
% 
% File name: $Source: /users/demons/demons/master-sources-repository/cime/examples/rings-theory/r-modulo-AG-AU.nc,v $
% $Revision: 1.2 $ 
% 
% Last modified on $Date: 1997/05/16 07:58:45 $
% 
%***************************************************************************

operators
  +   : AC
  .   : infix binary
  0,1 : constant
  -   : 1
  x,y,z : variable

theory  AG(+,0,-) AU(.,1)

axioms
  x.(y+z) = (x.y)+(x.z);
  (x+y).z = (x.z)+(y.z);

order  
  rpo( .>- >+>0 , .>1 ; . lrlex )
%  interactive
end

