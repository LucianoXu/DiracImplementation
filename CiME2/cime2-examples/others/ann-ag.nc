%***************************************************************************
%
%
% Comple'tion modulo AG des anneaux commutatifs
%
%
% Project:                Cime
% Author(s):             Claude March\'e
%
% File name:        ann-ag.nc
% Created on:              08 mar 93
% Last modified on: 08 mar 93
%
%***************************************************************************

operators
  +,. : AC
  0,1 : constant
  -   : 1
  x,y,z : variable

theory  AG(+,0,-)

axioms
  x.1 = x;
  x.(y+z) = (x.y)+(x.z);

order  
  rpo( 1>.>->+>0 ; + mul, . mul )
  % interactive

end

