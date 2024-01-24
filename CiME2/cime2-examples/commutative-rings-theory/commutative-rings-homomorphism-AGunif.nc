%***************************************************************************
%
% Comple'tion modulo CR de la th\'eorie d'un morphisme d'anneaux
% commutatifs
%
% $Id: commutative-rings-homomorphism-AGunif.nc,v 1.2 1997/03/14 13:45:17 marche Exp $
%
%***************************************************************************

operators
  +,.,&,*      : AC
  0,1,zero,one : constant
  -,I,H        : unary
  x,y,z,t,u    : variable

theory  CR(+,0,-,.,1)  CR(&,zero,I,*,one)

unification theory AG(+,0,-) ACU(.,1) AG(&,zero,I) ACU(*,one)

axioms H(x+y) = H(x) & H(y); H(x.y) = H(x) * H(y);  

order  rpo( H>1>.>- >+>0, H>one>*>I>&>zero  )

end

