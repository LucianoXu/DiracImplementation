%***************************************************************************
%
% Boolean rings theory modulo AG(+,0,i) and ACUI(.,1)
%
% Author(s):             Claude March\'e
%
%***************************************************************************

operators
  +,. : AC
  0,1 : constant
  x,y,z : variable
  - : unary

theory AG(+,0,-) ACUI(.,1)

axioms
  x.(y+z) = (x.y)+(x.z);

order  rpo(1>.>- >+>0)

end





