%***************************************************************************
%
%
% Theory of an homomorphism between two rings
%
% Author(s):        Claude Marche'
% File name:        rings-homomorphism.nc
% Last modified on: june 24, 1994
%
%***************************************************************************

operators
  + : AC
  & : AC
  . : infix binary
  * : infix binary
  0,1 : constant
  zero,un : constant
  -   : 1
  O   : 1
  x,y,z : variable
  H : unary

theory  AG(+,0,-)
        AG(&,zero,O)
        AU(.,1)
        AU(*,un)
axioms
  x.(y+z) = (x.y)+(x.z);
  (x+y).z = (x.z)+(y.z);

  x*(y&z) = (x*y)&(x*z);
  (x&y)*z = (x*z)&(y*z);

  H(x+y) = H(x) & H(y);
  H(x.y) = H(x) * H(y);  

order  
  rpo( H>1>.>->+>0, H>un>*>O>&>zero ; . lrlex, * lrlex )

end

