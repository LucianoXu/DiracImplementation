%***************************************************************************
%
%
% Comple'tion de la theorie des anneaux booleens 
% modulo ACN(+,0) et AC1I(.,1)
%
%
% Project:                Cime
% Author(s):             Claude March\'e
%
% File name:        anboacin.nc
% Created on:              08 mar 93
% Last modified on: 12 oct 93
%
%***************************************************************************

operators
  +,. : AC
  0,1 : constant
  -   : 1
  x,y,z : variable

theory ACUN(+,0,2) ACUI(.,1)

axioms
  x+-(x) = 0;
  x.(y+z) = (x.y)+(x.z);

order  rpo( 1>.>- >+>0 )

end

