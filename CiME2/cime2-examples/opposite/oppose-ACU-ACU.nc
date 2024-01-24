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

theory  ACU(+,0)

unification theory ACU(+,0)

axioms
  s(p(x)) = x;
  p(s(x)) = x;
  s(x)+y = s(x+y);
  p(x)+y = p(x+y);
  x+-(x) = 0 ;

order 
  rpo(->p,->s,->+,+>p,+>s,+>0)


end

