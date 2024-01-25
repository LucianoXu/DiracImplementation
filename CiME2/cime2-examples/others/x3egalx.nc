%***************************************************************************
%
%
% Comple'tion modulo AC des anneaux commutatifs avec x^3 =x
%
%
% Project:                Cime
% Author(s):             Claude March\'e
%
% File name:        anneaux.nc
% Created on:              08 mar 93
% Last modified on: 08 mar 93
%
%***************************************************************************

operators
  +     : AC
  .     : infix binary
  0,1   : constant
  -     : unary
  x,y,z : variable
  a,b   : constant

theory AG(+,0,-)
       %AU(.,1)
       %ACU(+,0)

% unification theory AG(+,0,-)

unification theory ACU(+,0)

axioms
  x+0=x;
  x+-(x) = 0;
  x.(y.z) = (x.y).z ;
  x.(y+z) = (x.y) + (x.z);
  (x+y).z = (x.z) + (y.z);
 x.x.x = x;

order  rpo(a > b > 1 > . > - > + > 0 ; + mul, . lrlex)

conjectures
  a.b = b.a;

end
