%***************************************************************************
%
% Oppose
%
%
% Project:                Cime
% Author(s):             Claude March\'e
%
%***************************************************************************

operators
  0 : constant
  s,p : unary
  + : AC
  - : unary
  x,y,z:variable

axioms
  s(p(x)) = x;
  p(s(x)) = x;
  x+0 = x;
  s(x)+y = s(x+y);
  p(x)+y = p(x+y);
  x+-(x) = 0 ;

order 

  rpo (- > + > p > s > 0 ) 

%  lexico ( mapo(- > + > p > s > 0 ) ;
%           poly([-](x)=3.x+1 ; [+](x,y)=x.y ; [s](x)=2.x+1 ; [p](x)=2.x+1 ))


end

