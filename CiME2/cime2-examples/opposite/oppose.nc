%***************************************************************************
%
% Oppose sans AC (diverge)
%
%
% Project:                Cime
% Author(s):             Claude March\'e
%
%***************************************************************************

operators
  0 : constant
  s,p : unary
  + : infix binary
  - : unary
  x,y,z:variable

axioms
  s(p(x)) = x;
  p(s(x)) = x;
  x+0 = x;
%  0+x = x;
%  s(x)+y = s(x+y);
  x+s(y) = s(x+y);
%  p(x)+y = p(x+y);
%  x+p(y) = p(x+y);
%  x+-(x) = 0 ;
%  -(x)+x = 0 ;

order 
  rpo(- > p,- > s,- > +,+ > p,+ > s,+ > 0)


end

