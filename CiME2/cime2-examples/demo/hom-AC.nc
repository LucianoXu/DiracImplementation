%******************************************************************
%
% Commutative rings homomorphism, modulo AC only
%
% $Id: hom-AC.nc,v 1.1 1996/05/30 15:04:02 marche Exp $
%
%******************************************************************

operators
  +,.     : AC
  0,1     : constant
  -       : unary
  x,y,z   : variable

axioms  
  x+0     = x ;
  x+-(x)  = 0;
  x.(y+z) = (x.y) + (x.z) ;
  x.1     = x ;

operators
  plus,times : AC
  zero,one   : constant
  minus      : unary

axioms  
  x plus zero        = x ;
  x plus minus(x)    = zero;
  x times (y plus z) = (x times y)  plus  (x times z) ;
  x times one        = x ;

operators
  H        : unary


axioms 

  H(x+y) = H(x) plus H(y); 
  H(x.y) = H(x) times H(y);  

order  
  rpo( H>1>.>->+>0, H>one>times>minus>plus>zero  )

conjectures

  H(0) = zero ;
  H(1) = one ;
  H(-(x)) = minus(H(x)) ;
  
end

