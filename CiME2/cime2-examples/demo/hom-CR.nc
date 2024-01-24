%******************************************************************
%
% Commutative rings homomorphism
%
% $Id: hom-CR.nc,v 1.2 1997/07/01 16:15:03 marche Exp $
%
%******************************************************************

operators
  +,.     : AC
  0,1     : constant
  -       : unary

theory  
  CR(+,0,-,.,1)  

operators
  plus,times : AC
  zero,one   : constant
  minus      : unary

theory  
  CR(plus,zero,minus,times,one)

operators
  H        : unary
  x,y,z    : variable


axioms 

  H(x+y) = H(x) plus H(y); 
  H(x.y) = H(x) times H(y);  

order  
  rpo( H > 1 > . > - > + > 0 , 
       H > one > times > minus > plus > zero  )

conjectures

  H(0) = zero ;
  H(1) = one ;
  H(-(x)) = minus(H(x)) ;
  
end

